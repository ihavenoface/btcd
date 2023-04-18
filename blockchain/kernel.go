// Copyright (c) 2014-2014 PPCD developers.
// Use of this source code is governed by an ISC
// license that can be found in the LICENSE file.

package blockchain

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"math/big"
	"sort"
	"time"

	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/txscript"
	"github.com/btcsuite/btcd/wire"
)

const (
	nModifierIntervalRatio int64 = 3
	// StakeTargetSpacing TODO(kac-) golint
	StakeTargetSpacing int64 = 10 * 60 // 10 minutes
	// StakeMaxAge TODO(kac-) golint
	StakeMaxAge int64 = 60 * 60 * 24 * 90 // stake age of full weight
	// MaxClockDrift TODO(kac-) golint
	MaxClockDrift int64 = 2 * 60 * 60 // two hours (main.h)

	MaxFutureBlockTimePrev09 int64 = 2 * 60 * 60
	MaxFutureBlockTime       int64 = 15 * 60
)

type blockTimeHash struct {
	time int64
	hash *chainhash.Hash
}

type blockTimeHashSorter []blockTimeHash

// Len returns the number of timestamps in the slice.  It is part of the
// sort.Interface implementation.
func (s blockTimeHashSorter) Len() int {
	return len(s)
}

// Swap swaps the timestamps at the passed indices.  It is part of the
// sort.Interface implementation.
func (s blockTimeHashSorter) Swap(i, j int) {
	s[i], s[j] = s[j], s[i]
}

// Less returns whether the timstamp with index i should sort before the
// timestamp with index j.  It is part of the sort.Interface implementation.
// http://stackoverflow.com/a/2819287/343061
// template <class T1, class T2>
// bool operator<(const pair<T1, T2>& x, const pair<T1, T2>& y);
// Returns: x.first < y.first || (!(y.first < x.first) && x.second < y.second).
func (s blockTimeHashSorter) Less(i, j int) bool {
	if s[i].time == s[j].time {
		// todo ppc Bytes() -> CloneBytes()
		bi := s[i].hash.CloneBytes()
		bj := s[j].hash.CloneBytes()
		// todo ppc wire.HashSize -> chainhash.HashSize
		for k := chainhash.HashSize - 1; k >= 0; k-- {
			if bi[k] < bj[k] {
				return true
			} else if bi[k] > bj[k] {
				return false
			}
		}
		return false
	}
	return s[i].time < s[j].time
}

// Get the last stake modifier and its generation time from a given block
func (b *BlockChain) getLastStakeModifier(pindex *blockNode) (
	nStakeModifier uint64, nModifierTime int64, err error) {

	// defer timeTrack(now(), fmt.Sprintf("getLastStakeModifier(%v)", pindex.hash))

	if pindex == nil {
		err = errors.New("getLastStakeModifier: nil pindex")
		return
	}

	// todo ppc !pindex.parentHash.IsEqual(zeroHash) -> !pindex.parent.hash.IsEqual(&chainhash.Hash{})
	for pindex.parent != nil && !isGeneratedStakeModifier(pindex.meta) {
		// todo ppc replaced getPrevNodeFromNode with LookupNode throughout this file
		//   should be checked for sanity across
		// pindex = b.index.LookupNode(&pindex.hash)
		pindex = b.index.LookupNode(&pindex.parent.hash)
		if pindex == nil {
			return
		}
	}

	if !isGeneratedStakeModifier(pindex.meta) {
		err = errors.New("getLastStakeModifier: no generation at genesis block")
		return
	}

	//log.Infof("pindex height=%v, stkmdf=%v", pindex.height, pindex.meta.StakeModifier)

	nStakeModifier = pindex.meta.StakeModifier
	// todo ppc pindex.timestamp.Unix() -> pindex.timestamp
	nModifierTime = pindex.timestamp

	return
}

// Get selection interval section (in seconds)
func getStakeModifierSelectionIntervalSection(params *chaincfg.Params, nSection int) int64 {
	//assert (nSection >= 0 && nSection < 64)
	return params.ModifierInterval * 63 / (63 + ((63 - int64(nSection)) * (nModifierIntervalRatio - 1)))
}

// Get stake modifier selection interval (in seconds)
func getStakeModifierSelectionInterval(params *chaincfg.Params) int64 {
	nSelectionInterval := int64(0)
	for nSection := 0; nSection < 64; nSection++ {
		nSelectionInterval += getStakeModifierSelectionIntervalSection(params, nSection)
	}
	return nSelectionInterval
}

// select a block from the candidate blocks in vSortedByTimestamp, excluding
// already selected blocks in vSelectedBlocks, and with timestamp up to
// nSelectionIntervalStop.
func selectBlockFromCandidates(
	b *BlockChain, vSortedByTimestamp []blockTimeHash,
	mapSelectedBlocks map[*chainhash.Hash]*blockNode,
	nSelectionIntervalStop int64,
	nStakeModifierPrev uint64) (pindexSelected *blockNode, err error) {

	// defer timeTrack(now(), fmt.Sprintf("selectBlockFromCandidates"))

	hashBest := new(chainhash.Hash)
	fSelected := false

	for _, item := range vSortedByTimestamp {

		pindex := b.index.LookupNode(item.hash)
		if pindex == nil {
			err = fmt.Errorf("SelectBlockFromCandidates: failed to find block index for candidate block %s", item.hash.String())
			return
		}
		// todo ppc pindex.timestamp.Unix() -> pindex.timestamp
		if fSelected && pindex.timestamp > nSelectionIntervalStop {
			break
		}
		// todo ppc pindex.hash -> &pindex.hash
		if _, ok := mapSelectedBlocks[&pindex.hash]; ok {
			continue
		}

		// compute the selection hash by hashing its proof-hash and the
		// previous proof-of-stake modifier
		var hashProof chainhash.Hash
		if !pindex.meta.HashProofOfStake.IsEqual(&zeroHash) { // TODO(mably) test null pointer in original code
			hashProof = pindex.meta.HashProofOfStake
		} else {
			// todo ppc *pindex.hash -> pindex.hash
			hashProof = pindex.hash
		}

		/* ss << hashProof << nStakeModifierPrev */
		buf := bytes.NewBuffer(make([]byte, 0,
			// todo ppc wire.HashSize -> chainhash.HashSize
			chainhash.HashSize+wire.VarIntSerializeSize(nStakeModifierPrev)))
		// todo ppc Bytes() -> slice
		_, err = buf.Write(hashProof[:])
		if err != nil {
			return
		}
		err = writeElement(buf, nStakeModifierPrev)
		if err != nil {
			return
		}

		hashSelection, _ := chainhash.NewHash(chainhash.DoubleHashB(buf.Bytes()))

		// the selection hash is divided by 2**32 so that proof-of-stake block
		// is always favored over proof-of-work block. this is to preserve
		// the energy efficiency property
		if !pindex.meta.HashProofOfStake.IsEqual(&zeroHash) { // TODO(mably) test null pointer in original code
			tmp := HashToBig(hashSelection)
			//hashSelection >>= 32
			tmp = tmp.Rsh(tmp, 32)
			hashSelection, err = bigToShaHash(tmp)
			if err != nil {
				return
			}
		}

		var hashSelectionInt = HashToBig(hashSelection)
		var hashBestInt = HashToBig(hashBest)

		if fSelected && (hashSelectionInt.Cmp(hashBestInt) == -1) {
			hashBest = hashSelection
			pindexSelected = pindex
		} else if !fSelected {
			fSelected = true
			hashBest = hashSelection
			pindexSelected = pindex
		}
	}
	//if fDebug && GetBoolArg("-printstakemodifier") {
	log.Debugf("SelectBlockFromCandidates: selection hash=%v", hashBest)
	//}
	return
}
// Stake Modifier (hash modifier of proof-of-stake):
// The purpose of stake modifier is to prevent a txout (coin) owner from
// computing future proof-of-stake generated by this txout at the time
// of transaction confirmation. To meet kernel protocol, the txout
// must hash with a future stake modifier to generate the proof.
// Stake modifier consists of bits each of which is contributed from a
// selected block of a given block group in the past.
// The selection of a block is based on a hash of the block's proof-hash and
// the previous stake modifier.
// Stake modifier is recomputed at a fixed time interval instead of every
// block. This is to make it difficult for an attacker to gain control of
// additional bits in the stake modifier, even after generating a chain of
// blocks.
func (b *BlockChain) computeNextStakeModifier(pindexCurrent *btcutil.Block) (
	nStakeModifier uint64, fGeneratedStakeModifier bool, err error) {

	// defer timeTrack(now(), fmt.Sprintf("computeNextStakeModifier(%v)", slice(pindexCurrent.Hash())[0]))

	nStakeModifier = 0
	fGeneratedStakeModifier = false

	//log.Debugf("pindexCurrent = %v, %v", pindexCurrent.Height(), pindexCurrent.Sha())

	// Get a block node for the block previous to this one.  Will be nil
	// if this is the genesis block.
	pindexPrev := b.index.LookupNode(&pindexCurrent.MsgBlock().Header.PrevBlock)
	/*
		if errPrevNode != nil {
			err = fmt.Errorf("fetching prev node: %v", errPrevNode)
			return
		}
	*/
	// todo ppc
	if pindexPrev == nil {
		fGeneratedStakeModifier = true
		return // genesis block's modifier is 0
	}

	// First find current stake modifier and its generation block time
	// if it's not old enough, return the same stake modifier
	nModifierTime := int64(0)
	nStakeModifier, nModifierTime, stakeErr := b.getLastStakeModifier(pindexPrev)
	if stakeErr != nil {
		err = fmt.Errorf("computeNextStakeModifier: unable to get last modifier: %v", stakeErr)
		return
	}

	log.Debugf("computeNextStakeModifier: prev modifier=%d time=%s epoch=%d\n", nStakeModifier, dateTimeStrFormat(nModifierTime), uint(nModifierTime))

	if (nModifierTime / b.chainParams.ModifierInterval) >= (pindexPrev.timestamp / b.chainParams.ModifierInterval) {
		log.Debugf("computeNextStakeModifier: no new interval keep current modifier: pindexPrev nHeight=%d nTime=%d", pindexPrev.height, pindexPrev.timestamp)
		return
	}

	pindexCurrentHeader := pindexCurrent.MsgBlock().Header
	if (nModifierTime / b.chainParams.ModifierInterval) >= (pindexCurrentHeader.Timestamp.Unix() / b.chainParams.ModifierInterval) {
		// v0.4+ requires current block timestamp also be in a different modifier interval
		if isProtocolV04(b, pindexCurrentHeader.Timestamp.Unix()) {
			log.Debugf("computeNextStakeModifier: (v0.4+) no new interval keep current modifier: pindexCurrent nHeight=%d nTime=%d", pindexCurrent.Height(), pindexCurrentHeader.Timestamp.Unix())
			return
		}
		currentSha := pindexCurrent.Hash()
		log.Debugf("computeNextStakeModifier: v0.3 modifier at block %s not meeting v0.4+ protocol: pindexCurrent nHeight=%d nTime=%d", currentSha.String(), pindexCurrent.Height(), pindexCurrentHeader.Timestamp.Unix())
	}

	// Sort candidate blocks by timestamp
	// TODO(kac-) ouch
	//var vSortedByTimestamp []blockTimeHash = make([]blockTimeHash, 64*nModifierInterval/StakeTargetSpacing)
	//vSortedByTimestamp := make([]blockTimeHash, 0)
	var vSortedByTimestamp []blockTimeHash // golint suggestion
	//vSortedByTimestamp.reserve(64 * nModifierInterval / STAKE_TARGET_SPACING)
	nSelectionInterval := getStakeModifierSelectionInterval(b.chainParams)
	nSelectionIntervalStart := (pindexPrev.timestamp/b.chainParams.ModifierInterval)*b.chainParams.ModifierInterval - nSelectionInterval
	log.Debugf("computeNextStakeModifier: nSelectionInterval = %d, nSelectionIntervalStart = %s[%d]", nSelectionInterval, dateTimeStrFormat(nSelectionIntervalStart), nSelectionIntervalStart)
	pindex := pindexPrev
	// todo ppc either the timestamp is off or we're reaching genesis block for some other reason
	for pindex != nil && (pindex.timestamp >= nSelectionIntervalStart) {
		vSortedByTimestamp = append(vSortedByTimestamp,
			blockTimeHash{pindex.timestamp, &pindex.hash})
		if pindex.parent != nil { // todo ppc meh
			pindex = b.index.LookupNode(&pindex.parent.hash)
		} else {
			break
		}
	}
	// TODO needs verification
	//reverse(vSortedByTimestamp.begin(), vSortedByTimestamp.end());
	//sort(vSortedByTimestamp.begin(), vSortedByTimestamp.end());
	sort.Reverse(blockTimeHashSorter(vSortedByTimestamp))
	sort.Sort(blockTimeHashSorter(vSortedByTimestamp))

	// Select 64 blocks from candidate blocks to generate stake modifier
	nStakeModifierNew := uint64(0)
	nSelectionIntervalStop := nSelectionIntervalStart
	mapSelectedBlocks := make(map[*chainhash.Hash]*blockNode)
	for nRound := 0; nRound < minInt(64, len(vSortedByTimestamp)); nRound++ {
		// add an interval section to the current selection round
		nSelectionIntervalStop += getStakeModifierSelectionIntervalSection(b.chainParams, nRound)
		// select a block from the candidates of current round
		pindex, errSelBlk := selectBlockFromCandidates(b, vSortedByTimestamp,
			mapSelectedBlocks, nSelectionIntervalStop, nStakeModifier)
		if errSelBlk != nil {
			err = fmt.Errorf("computeNextStakeModifier: unable to select block at round %d : %v", nRound, errSelBlk)
			return
		}
		// write the entropy bit of the selected block
		nStakeModifierNew |= (uint64(getMetaStakeEntropyBit(pindex.meta)) << uint64(nRound))
		// add the selected block from candidates to selected list
		// todo ppc pindex.hash -> & pindex.hash
		mapSelectedBlocks[&pindex.hash] = pindex
		//if (fDebug && GetBoolArg("-printstakemodifier")) {
		log.Debugf("computeNextStakeModifier: selected round %d stop=%s height=%d bit=%d modifier=%v",
			nRound, dateTimeStrFormat(nSelectionIntervalStop),
			pindex.height, getMetaStakeEntropyBit(pindex.meta),
			getStakeModifierHexString(nStakeModifierNew))
		//}
	}

	/*// Print selection map for visualization of the selected blocks
	if (fDebug && GetBoolArg("-printstakemodifier")) {
		var nHeightFirstCandidate int64
		if pindex == nil {
			nHeightFirstCandidate = 0
		} else {
			nHeightFirstCandidate = pindex.height + 1
		}
		strSelectionMap := ""
		// '-' indicates proof-of-work blocks not selected
		strSelectionMap.insert(0, pindexPrev.height - nHeightFirstCandidate + 1, '-')
		pindex = pindexPrev
		for pindex != nil && (pindex.height >= nHeightFirstCandidate) {
			// '=' indicates proof-of-stake blocks not selected
			if pindex.hashProofOfStake != nil {
				strSelectionMap.replace(pindex.Height() - nHeightFirstCandidate, 1, "=")
			}
			pindex = pindex.pprev
		}
		for _, item := range mapSelectedBlocks {
			// 'S' indicates selected proof-of-stake blocks
			// 'W' indicates selected proof-of-work blocks
			if IsBlockProofOfStake(item) {
				blockType := "S"
			} else {
				blockType := "W"
			}
			strSelectionMap.replace(item.Height() - nHeightFirstCandidate, 1,  blockType);
		}
		log.Debugf("computeNextStakeModifier: selection height [%d, %d] map %s\n", nHeightFirstCandidate, pindexPrev.Height(), strSelectionMap)
	}*/

	log.Debugf("computeNextStakeModifier: new modifier=%v time=%v height=%v",
		getStakeModifierHexString(nStakeModifierNew),
		dateTimeStrFormat(pindexPrev.timestamp), pindexCurrent.Height())

	nStakeModifier = nStakeModifierNew
	fGeneratedStakeModifier = true

	return
}

// addToBlockIndex processes all ppcoin specific block meta data
func (b *BlockChain) addToBlockIndex(block *btcutil.Block) (err error) {

	// defer timeTrack(now(), fmt.Sprintf("addToBlockIndex(%v)", slice(block.Sha())[0]))

	meta := block.Meta()

	// ppcoin: compute stake entropy bit for stake modifier
	stakeEntropyBit, err := getStakeEntropyBit(b, block)
	if err != nil {
		err = errors.New("addToBlockIndex() : GetStakeEntropyBit() failed")
		return
	}
	setMetaStakeEntropyBit(meta, stakeEntropyBit)

	// ppcoin: compute stake modifier
	nStakeModifier := uint64(0)
	fGeneratedStakeModifier := false
	nStakeModifier, fGeneratedStakeModifier, err =
		b.computeNextStakeModifier(block)
	if err != nil {
		err = fmt.Errorf("addToBlockIndex() : computeNextStakeModifier() failed %v", err)
		return
	}

	meta.StakeModifier = nStakeModifier
	setGeneratedStakeModifier(meta, fGeneratedStakeModifier)

	meta.StakeModifierChecksum, err = b.getStakeModifierChecksum(block)

	log.Debugf("addToBlockIndex() : height=%d, modifier=%v, checksum=%v",
		block.Height(), getStakeModifierHexString(meta.StakeModifier),
		getStakeModifierCSHexString(meta.StakeModifierChecksum))

	if err != nil {
		err = errors.New("addToBlockIndex() : getStakeModifierChecksum() failed")
		return
	}
	// todo ppc
	if !b.checkStakeModifierCheckpoints(block.Height(), meta.StakeModifierChecksum) {
		err = fmt.Errorf("addToBlockIndex() : Rejected by stake modifier checkpoint height=%d, modifier=%d", block.Height(), meta.StakeModifier)
		return
	}

	return nil
}

//CBlockIndex* pindexPrev, unsigned int nTimeTx, uint64_t& nStakeModifier, int& nStakeModifierHeight, int64_t& nStakeModifierTime, bool fPrintProofOfStake
func (b *BlockChain) getKernelStakeModifierV05(hashBlockFrom *chainhash.Hash, nTimeTx int64, fPrintProofOfStake bool) (
	nStakeModifier uint64, nStakeModifierHeight int32, nStakeModifierTime int64,
	err error) {
	/*
	   const Consensus::Params& params = Params().GetConsensus();
	   const CBlockIndex* pindex = pindexPrev;
	   nStakeModifierHeight = pindex->nHeight;
	   nStakeModifierTime = pindex->GetBlockTime();
	   int64_t nStakeModifierSelectionInterval = GetStakeModifierSelectionInterval();

	   if (nStakeModifierTime + params.nStakeMinAge - nStakeModifierSelectionInterval <= (int64_t) nTimeTx)
	   {
	       // Best block is still more than
	       // (nStakeMinAge minus a selection interval) older than kernel timestamp
	       if (fPrintProofOfStake)
	           return error("GetKernelStakeModifier() : best block %s at height %d too old for stake",
	               pindex->GetBlockHash().ToString(), pindex->nHeight);
	       else
	           return false;
	   }
	   // loop to find the stake modifier earlier by
	   // (nStakeMinAge minus a selection interval)
	   while (nStakeModifierTime + params.nStakeMinAge - nStakeModifierSelectionInterval >(int64_t) nTimeTx)
	   {
	       if (!pindex->pprev)
	       {   // reached genesis block; should not happen
	           return error("GetKernelStakeModifier() : reached genesis block");
	       }
	       pindex = pindex->pprev;
	       if (pindex->GeneratedStakeModifier())
	       {
	           nStakeModifierHeight = pindex->nHeight;
	           nStakeModifierTime = pindex->GetBlockTime();
	       }
	   }
	   nStakeModifier = pindex->nStakeModifier;
	   return true;
	*/
	nStakeModifier = 0
	blockFrom := b.bestChain.Tip() // todo ppc check if this makes sense
	blockFromHeight := blockFrom.height
	// todo ppc
	/*if blockFrom == nil {
		err = fmt.Errorf("getKernelStakeModifier() : block not found (%v)", hashBlockFrom)
		return
	}
	blockFromHeight, fetchErr := b.BlockHeightByHash(hashBlockFrom)
	if fetchErr != nil {
		err = fmt.Errorf("getKernelStakeModifier() : block height not found (%v)", fetchErr)
		return
	}*/
	nStakeModifierHeight = blockFromHeight
	nStakeModifierTime = blockFrom.Header().Timestamp.Unix()
	nStakeModifierSelectionInterval := getStakeModifierSelectionInterval(b.chainParams)

	block := blockFrom.Header()
	blockHeight := blockFromHeight
	meta := blockFrom.meta

	var blockHash *chainhash.Hash
	if (nStakeModifierTime + b.chainParams.StakeMinAge - nStakeModifierSelectionInterval) <= nTimeTx {
		// Best block is still more than
		// (nStakeMinAge minus a selection interval) older than kernel timestamp
		if fPrintProofOfStake {
			err = fmt.Errorf("GetKernelStakeModifier() : best block %v at height %v too old for stake",
				hashBlockFrom, blockFromHeight)
			return
		} else {
			return
		}
	}

	// loop to find the stake modifier earlier by
	// (nStakeMinAge minus a selection interval)
	for (nStakeModifierTime + b.chainParams.StakeMinAge - nStakeModifierSelectionInterval) > nTimeTx {
		// todo ppc genesis test
		// todo this can be dumbed down
		blockHash, err = b.BlockHashByHeight(blockHeight)
		if err != nil {
			return
		}
		block, err = b.HeaderByHash(blockHash)
		if err != nil {
			return
		}
		// todo ppc possibly read meta from disk
		node := b.index.LookupNode(blockHash)
		if node == nil {
			return
		}
		meta = node.meta
		blockHeight--
		if isGeneratedStakeModifier(meta) {
			nStakeModifierHeight = node.height
			nStakeModifierTime = block.Timestamp.Unix()
		}
	}
	nStakeModifier = meta.StakeModifier
	return
}

// The stake modifier used to hash for a stake kernel is chosen as the stake
// modifier about a selection interval later than the coin generating the kernel
func (b *BlockChain) getKernelStakeModifier03(
	hashBlockFrom *chainhash.Hash, timeSource MedianTimeSource, fPrintProofOfStake bool) (
	nStakeModifier uint64, nStakeModifierHeight int32, nStakeModifierTime int64,
	err error) {

	// defer timeTrack(now(), fmt.Sprintf("getKernelStakeModifier(%v)", hashBlockFrom))

	//log.Debugf("getKernelStakeModifier : blockFrom = %v", hashBlockFrom)

	nStakeModifier = 0
	blockFrom := b.index.LookupNode(hashBlockFrom)
	if blockFrom == nil {
		err = fmt.Errorf("getKernelStakeModifier() : block not found (%v)", hashBlockFrom)
		return
	}
	blockFromHeight, fetchErr := b.BlockHeightByHash(hashBlockFrom)
	if fetchErr != nil {
		err = fmt.Errorf("getKernelStakeModifier() : block height not found (%v)", fetchErr)
		return
	}
	nStakeModifierHeight = blockFromHeight
	blockFromTimestamp := blockFrom.Header().Timestamp.Unix()
	nStakeModifierTime = blockFromTimestamp
	nStakeModifierSelectionInterval := getStakeModifierSelectionInterval(b.chainParams)
	block := blockFrom.Header()
	blockHeight := blockFromHeight
	meta := blockFrom.meta
	var blockHash *chainhash.Hash
	// loop to find the stake modifier later by a selection interval
	for nStakeModifierTime < (blockFromTimestamp + nStakeModifierSelectionInterval) {
		if blockHeight >= b.bestChain.height() { // reached best block; may happen if node is behind on block chain
			blockTimestamp := block.Timestamp.Unix()
			if fPrintProofOfStake || (blockTimestamp+b.chainParams.StakeMinAge-nStakeModifierSelectionInterval > timeSource.AdjustedTime().Unix()) {
				err = fmt.Errorf("GetKernelStakeModifier() : reached best block %v at height %v from block %v",
					blockHash, blockHeight, hashBlockFrom)
				return
			}
			return
		}
		// todo this can be dumbed down
		blockHash, err = b.BlockHashByHeight(blockHeight + 1)
		if err != nil {
			return
		}
		block, err = b.HeaderByHash(blockHash)
		if err != nil {
			return
		}
		// todo ppc possibly read meta from disk
		node := b.index.LookupNode(blockHash)
		if node == nil {
			return
		}
		meta = node.meta
		blockHeight++
		if isGeneratedStakeModifier(meta) {
			nStakeModifierHeight = blockHeight
			nStakeModifierTime = block.Timestamp.Unix()
		}
	}
	nStakeModifier = meta.StakeModifier
	return
}

func (b *BlockChain) getKernelStakeModifier(
	hashBlockFrom *chainhash.Hash, timeSource MedianTimeSource, nTimeTx int64, fPrintProofOfStake bool) (
	nStakeModifier uint64, nStakeModifierHeight int32, nStakeModifierTime int64,
	err error) {
	if isProtocolV05(b, nTimeTx) {
		nStakeModifier, nStakeModifierHeight, nStakeModifierTime, err = b.getKernelStakeModifierV05(hashBlockFrom, nTimeTx, fPrintProofOfStake)
	} else {
		nStakeModifier, nStakeModifierHeight, nStakeModifierTime, err = b.getKernelStakeModifier03(hashBlockFrom, timeSource, fPrintProofOfStake)
	}
	return
}

// ppcoin kernel protocol
// coinstake must meet hash target according to the protocol:
// kernel (input 0) must meet the formula
//     hash(nStakeModifier + txPrev.block.nTime + txPrev.offset + txPrev.nTime + txPrev.vout.n + nTime) < bnTarget * nCoinDayWeight
// this ensures that the chance of getting a coinstake is proportional to the
// amount of coin age one owns.
// The reason this hash is chosen is the following:
//   nStakeModifier:
//       (v0.3) scrambles computation to make it very difficult to precompute
//              future proof-of-stake at the time of the coin's confirmation
//       (v0.2) nBits (deprecated): encodes all past block timestamps
//   txPrev.block.nTime: prevent nodes from guessing a good timestamp to
//                       generate transaction for future advantage
//   txPrev.offset: offset of txPrev inside block, to reduce the chance of
//                  nodes generating coinstake at the same time
//   txPrev.nTime: reduce the chance of nodes generating coinstake at the same
//                 time
//   txPrev.vout.n: output number of txPrev, to reduce the chance of nodes
//                  generating coinstake at the same time
//   block/tx hash should not be used here as they can be generated in vast
//   quantities so as to generate blocks faster, degrading the system back into
//   a proof-of-work situation.
//
func (b *BlockChain) checkStakeKernelHash(
	nBits uint32, blockFrom *btcutil.Block, nTxPrevOffset uint32,
	txPrev *btcutil.Tx, prevout *wire.OutPoint, nTimeTx int64,
	timeSource MedianTimeSource, fPrintProofOfStake bool) (
	hashProofOfStake *chainhash.Hash, success bool, err error) {

	// defer timeTrack(now(), fmt.Sprintf("checkStakeKernelHash(%v)", slice(blockFrom.Hash())[0]))

	success = false

	txMsgPrev := txPrev.MsgTx()
	nTimeBlockFrom := blockFrom.MsgBlock().Header.Timestamp.Unix()

	var nTimeTxPrev int64
	if txMsgPrev.Timestamp.Unix() == 0 {
		nTimeTxPrev = nTimeBlockFrom
	} else {
		nTimeTxPrev = txMsgPrev.Timestamp.Unix()
	}
	if nTimeTx < nTimeTxPrev { // Transaction timestamp violation
		err = errors.New("checkStakeKernelHash() : nTime violation")
		return
	}

	// todo ppc
	// 1346126538
	// 1346140595

	if nTimeBlockFrom+b.chainParams.StakeMinAge > nTimeTx { // Min age requirement
		err = errors.New("checkStakeKernelHash() : min age violation")
		return
	}

	// todo ppc
	bnTargetPerCoinDay := CompactToBig(nBits)

	nValueIn := txMsgPrev.TxOut[prevout.Index].Value

	// v0.3 protocol kernel hash weight starts from 0 at the 30-day min age
	// this change increases active coins participating the hash and helps
	// to secure the network when proof-of-stake difficulty is low
	var timeReduction int64
	if isProtocolV03(b, nTimeTx) {
		timeReduction = b.chainParams.StakeMinAge
	} else {
		timeReduction = 0
	}
	nTimeWeight := minInt64(nTimeTx-nTimeTxPrev, StakeMaxAge) - timeReduction

	//CBigNum bnCoinDayWeight = CBigNum(nValueIn) * nTimeWeight / COIN / (24 * 60 * 60)
	bnCoinDayWeight := new(big.Int).Div(new(big.Int).Div(new(big.Int).Mul(
		big.NewInt(nValueIn), big.NewInt(nTimeWeight)), big.NewInt(Coin)), big.NewInt(24*60*60))
	/*var bnCoinDayWeight *big.Int = new(big.Int).Div(new(big.Int).Mul(
	new(big.Int).Div(big.NewtInt(nValueIn), big.NewInt(COIN)),
		big.NewInt(nTimeWeight)), big.NewInt(24*60*60))*/

	log.Debugf("checkStakeKernelHash() : nValueIn=%v nTimeWeight=%v bnCoinDayWeight=%v",
		nValueIn, nTimeWeight, bnCoinDayWeight)

	// Calculate hash
	buf := bytes.NewBuffer(make([]byte, 0, 28)) // TODO pre-calculate size?

	bufSize := 0
	var nStakeModifier uint64
	var nStakeModifierHeight int32
	var nStakeModifierTime int64
	if isProtocolV03(b, nTimeTx) { // v0.3 protocol
		var blockFromHash *chainhash.Hash
		blockFromHash = blockFrom.Hash()
		// todo ppc
		nStakeModifier, nStakeModifierHeight, nStakeModifierTime, err =
			b.getKernelStakeModifier(blockFromHash, timeSource, nTimeTx, fPrintProofOfStake)
		if err != nil {
			return
		}
		//ss << nStakeModifier;
		err = writeElement(buf, nStakeModifier)
		bufSize += 8
		if err != nil {
			return
		}
	} else { // v0.2 protocol
		//ss << nBits;
		err = writeElement(buf, nBits)
		bufSize += 4
		if err != nil {
			return
		}
	}

	err = writeElement(buf, uint32(nTimeBlockFrom))
	bufSize += 4
	if err != nil {
		return
	}
	// todo ppc the info we get from meta is off by 4 currently
	nTxPrevOffset = nTxPrevOffset - 4
	err = writeElement(buf, nTxPrevOffset)
	bufSize += 4
	if err != nil {
		return
	}
	err = writeElement(buf, uint32(nTimeTxPrev))
	bufSize += 4
	if err != nil {
		return
	}
	err = writeElement(buf, prevout.Index)
	bufSize += 4
	if err != nil {
		return
	}
	err = writeElement(buf, uint32(nTimeTx))
	bufSize += 4
	if err != nil {
		return
	}

	//ss << nTimeBlockFrom << nTxPrevOffset << txPrev.nTime << prevout.n << nTimeTx;

	hashProofOfStake, err = chainhash.NewHash(
		chainhash.DoubleHashB(buf.Bytes()[:bufSize]))
	if err != nil {
		return
	}

	if fPrintProofOfStake {
		if isProtocolV03(b, nTimeTx) {
			// todo ppc update log v05
			log.Debugf("checkStakeKernelHash() : using modifier %d at height=%d timestamp=%s for block from height=%d timestamp=%s",
				nStakeModifier, nStakeModifierHeight,
				dateTimeStrFormat(nStakeModifierTime), blockFrom.Height(),
				dateTimeStrFormat(nTimeBlockFrom))
		}
		var ver string
		var modifier uint64
		// todo ppc update log v05
		if isProtocolV03(b, nTimeTx) {
			ver = "0.3"
			modifier = nStakeModifier
		} else {
			ver = "0.2"
			modifier = uint64(nBits)
		}
		// todo ppc update log v05
		log.Debugf("checkStakeKernelHash() : check protocol=%s modifier=%d nBits=%d nTimeBlockFrom=%d nTxPrevOffset=%d nTimeTxPrev=%d nPrevout=%d nTimeTx=%d hashProof=%s",
			ver, modifier, nBits, nTimeBlockFrom, nTxPrevOffset, nTimeTxPrev,
			prevout.Index, nTimeTx, hashProofOfStake.String())
	}

	// Now check if proof-of-stake hash meets target protocol
	// todo ppc re-enable
	hashProofOfStakeInt := HashToBig(hashProofOfStake)
	targetInt := new(big.Int).Mul(bnCoinDayWeight, bnTargetPerCoinDay)
	//log.Debugf("checkStakeKernelHash() : hashInt = %v, targetInt = %v", hashProofOfStakeInt, targetInt)
	if hashProofOfStakeInt.Cmp(targetInt) > 0 {
		return
	}
	//if (fDebug && !fPrintProofOfStake) {
	if !fPrintProofOfStake {
		if isProtocolV03(b, nTimeTx) {
			log.Debugf("checkStakeKernelHash() : using modifier %d at height=%d timestamp=%s for block from height=%d timestamp=%s\n",
				nStakeModifier, nStakeModifierHeight,
				dateTimeStrFormat(nStakeModifierTime), blockFrom.Height(),
				dateTimeStrFormat(nTimeBlockFrom))
		}
		var ver string
		var modifier uint64
		if isProtocolV03(b, nTimeTx) {
			ver = "0.3"
			modifier = nStakeModifier
		} else {
			ver = "0.2"
			modifier = uint64(nBits)
		}
		log.Debugf("checkStakeKernelHash() : pass protocol=%s modifier=%d nTimeBlockFrom=%d nTxPrevOffset=%d nTimeTxPrev=%d nPrevout=%d nTimeTx=%d hashProof=%s",
			ver, modifier, nTimeBlockFrom, nTxPrevOffset, nTimeTxPrev,
			prevout.Index, nTimeTx, hashProofOfStake.String())
	}

	success = true
	return
}

// Check kernel hash target and coinstake signature
func (b *BlockChain) checkTxProofOfStake(tx *btcutil.Tx, timeSource MedianTimeSource, nBits uint32, blockTime time.Time) (
	hashProofOfStake *chainhash.Hash, err error) {
	// todo ppc possibly run lock

	// b.chainLock.RLock()
	// defer b.chainLock.RUnlock()

	// defer timeTrack(now(), fmt.Sprintf("CheckProofOfStake(%v)", slice(tx.Hash())[0]))

	msgTx := tx.MsgTx()

	if !msgTx.IsCoinStake() {
		err = fmt.Errorf("CheckProofOfStake() : called on non-coinstake %s", tx.Hash().String())
		return
	}

	// Kernel (input 0) must match the stake hash target per coin age (nBits)
	txin := msgTx.TxIn[0]

	// First try finding the previous transaction in database
	// todo ppc ProcessBlock() holds lock. re-do lock order or avoid FetchUtxoView
	// todo ppc we might be able to pass in dbTx
	b.chainLock.Unlock()
	utxoView, err := b.FetchUtxoView(tx)
	b.chainLock.Lock()
	if err != nil {
		return
	}
	// todo ppc possibly assign
	// var prevBlockHeight int64

	txPrevData := utxoView.LookupEntry(txin.PreviousOutPoint)
	if txPrevData == nil { // todo ppc does this work?
		//return tx.DoS(1, error("CheckProofOfStake() : INFO: read txPrev failed"))  // previous transaction not in main chain, may occur during initial download
		// todo ppc check if we're generating the error properly
		err = fmt.Errorf("CheckProofOfStake() : INFO: read txPrevData failed")
		return
	}
	// todo ppc possibly assign
	// prevBlockHeight = txPrevData.BlockHeight

	// Verify signature
	errVerif := b.verifySignature(utxoView, txin, tx, 0, true, 0)
	if errVerif != nil {
		//return tx.DoS(100, error("CheckProofOfStake() : VerifySignature failed on coinstake %s", tx.Sha().String()))
		err = fmt.Errorf("CheckProofOfStake() : VerifySignature failed on coinstake %s (%v)", tx.Hash().String(), errVerif)
		return
	}

	/* todo ppc maybe use this?
	prevHash := &block.MsgBlock().Header.PrevBlock
	prevHeader, err := dbFetchHeaderByHash(dbTx, prevHash)
	*/


	// Read block header
	// The desired block height is in the main chain, so look it up
	// from the main chain database.
	/* todo ppc block should be in mem but we check anyway
	prevBlockHash, err := b.db.FetchblockHashByHeight(txPrevData.BlockHeight)
	if err != nil {
		err = fmt.Errorf("CheckProofOfStake() : read block failed (%v)", err) // unable to read block of previous transaction
		return
	}
	prevBlock, err := b.db.FetchBlockBySha(prevBlockHash)
	if err != nil {
		err = fmt.Errorf("CheckProofOfStake() : read block failed (%v)", err) // unable to read block of previous transaction
		return
	}
	*/

	prevBlock, err := b.BlockByHeight(txPrevData.BlockHeight())
	if err != nil {
		err = fmt.Errorf("CheckProofOfStake() : read block failed (%v)", err) // unable to read block of previous transaction
		return
	}

	success := false
	for _, txPrev := range prevBlock.Transactions() {

		if txPrev.Hash().IsEqual(&txin.PreviousOutPoint.Hash) {
			var nTimeTx int64
			if msgTx.Timestamp.Unix() == 0 {
				nTimeTx = blockTime.Unix()
			} else {
				nTimeTx = msgTx.Timestamp.Unix()
			}
			fDebug := true
			//nTxPrevOffset uint := txindex.pos.nTxPos - txindex.pos.nBlockPos
			//prevBlockTxLoc, _ := prevBlock.TxLoc() // TODO not optimal way
			//nTxPrevOffset := uint32(prevBlockTxLoc[txPrev.Index()].TxStart)
			nTxPrevOffset := prevBlock.Meta().TxOffsets[txPrev.Index()]
			//log.Infof("Comparing txOffset : %v - %v", nTxPrevOffset, nTxPrevOffsetMeta)
			hashProofOfStake, success, err = b.checkStakeKernelHash(
				nBits, prevBlock, nTxPrevOffset, txPrev, &txin.PreviousOutPoint,
				nTimeTx, timeSource, fDebug)
			if err != nil {
				return
			}
			break
		}
	}

	if !success {
		//return tx.DoS(1, error("CheckProofOfStake() : INFO: check kernel failed on coinstake %s, hashProof=%s",
		//		tx.Sha().String(), hashProofOfStake.String())) // may occur during initial download or if behind on block chain sync
		err = fmt.Errorf("CheckProofOfStake() : INFO: check kernel failed on coinstake %v, hashProof=%v",
			tx.Hash(), hashProofOfStake)
		return
	}

	return
}

// checkBlockProofOfStake
func (b *BlockChain) checkBlockProofOfStake(block *btcutil.Block, timeSource MedianTimeSource) error {

	if block.MsgBlock().IsProofOfStake() {

		blockHash := block.Hash()
		log.Tracef("Block %v is PoS", blockHash)

		tx, err := block.Tx(1)
		if err != nil {
			return err
		}

		hashProofOfStake, err :=
			b.checkTxProofOfStake(tx, timeSource, block.MsgBlock().Header.Bits, block.MsgBlock().Header.Timestamp)
		if err != nil {
			return err
		}

		setProofOfStake(block.Meta(), true) // Important: flags
		block.Meta().HashProofOfStake = *hashProofOfStake
		// todo ppc check if Debugf makes sense
		log.Debugf("Proof of stake for block %v = %v", blockHash, hashProofOfStake)

	}

	return nil
}

// Check whether the coinstake timestamp meets protocol
// called from main.cpp
func (b *BlockChain) checkCoinStakeTimestamp(
	nTimeBlock int64, nTimeTx int64) bool {

	if isProtocolV03(b, nTimeTx) { // v0.3 protocol
		return nTimeBlock == nTimeTx
	}
	// v0.2 protocol
	return (nTimeTx <= nTimeBlock) && (nTimeBlock <= nTimeTx+MaxFutureBlockTimePrev09)
}

func checkCoinStakeTimestamp(params *chaincfg.Params,
	nTimeBlock int64, nTimeTx int64) bool {

	if isProtocolV03FromParams(params, nTimeTx) { // v0.3 protocol
		return nTimeBlock == nTimeTx
	}
	// v0.2 protocol
	return (nTimeTx <= nTimeBlock) && (nTimeBlock <= nTimeTx+MaxFutureBlockTimePrev09)
}

// Get stake modifier checksum
// called from main.cpp
func (b *BlockChain) getStakeModifierChecksum(
	pindex *btcutil.Block) (checkSum uint32, err error) {

	// defer timeTrack(now(), fmt.Sprintf("getStakeModifierChecksum(%v)", slice(pindex.Hash())[0]))

	//assert (pindex.pprev || pindex.Sha().IsEqual(hashGenesisBlock))
	// Hash previous checksum with flags, hashProofOfStake and nStakeModifier
	bufSize := 0
	buf := bytes.NewBuffer(make([]byte, 0, 50)) // TODO calculate size
	//CDataStream ss(SER_GETHASH, 0)
	var parent *blockNode
	parent = b.index.LookupNode(&pindex.MsgBlock().Header.PrevBlock)
	if parent == nil {
		return
	} else {
		//ss << pindex.pprev.nStakeModifierChecksum
		err = writeElement(
			buf, parent.meta.StakeModifierChecksum)
		bufSize += 4
		if err != nil {
			return
		}
	}
	meta := pindex.Meta()
	//ss << pindex.nFlags << pindex.hashProofOfStake << pindex.nStakeModifier
	err = writeElement(buf, meta.Flags)
	bufSize += 4
	if err != nil {
		return
	}
	// todo ppc Bytes() -> slice
	_, err = buf.Write(meta.HashProofOfStake[:]) // .CloneBytes()?
	bufSize += 32
	if err != nil {
		return
	}
	err = writeElement(buf, meta.StakeModifier)
	bufSize += 8
	if err != nil {
		return
	}

	//uint256 hashChecksum = Hash(ss.begin(), ss.end())
	var hashChecksum *chainhash.Hash
	hashChecksum, err = chainhash.NewHash(
		chainhash.DoubleHashB(buf.Bytes()[:bufSize]))
	if err != nil {
		return
	}

	//hashChecksum >>= (256 - 32)
	var hashCheckSumInt = HashToBig(hashChecksum)
	//return hashChecksum.Get64()
	checkSum = uint32(hashCheckSumInt.Rsh(hashCheckSumInt, 256-32).Uint64())

	return
}

// Check stake modifier hard checkpoints
// called from (main.cpp)
func (b *BlockChain) checkStakeModifierCheckpoints(
	nHeight int32, nStakeModifierChecksum uint32) bool {
	if checkpoint, ok := b.chainParams.StakeModifierCheckpoints[nHeight]; ok {
		return nStakeModifierChecksum == checkpoint
	}
	return true
}

func IsSuperMajority(b *BlockChain, minVersion int32, pstart *blockNode, nRequired uint64, nToCheck uint64) bool {
	return HowSuperMajority(b, minVersion, pstart, nRequired, nToCheck) >= nRequired
}

func HowSuperMajority(b *BlockChain, minVersion int32, pstart *blockNode, nRequired uint64, nToCheck uint64) uint64 {
	// todo ppc check if mainnet (900) works as expected
	numFound := uint64(0)
	iterNode := pstart
	for i := uint64(0); i < nToCheck && numFound < nRequired && iterNode != nil; i++ {
		if !iterNode.isProofOfStake() {
			continue
		}

		// This node has a version that is at least the minimum version.
		if iterNode.version >= minVersion {
			numFound++
		}

		// Get the previous block node.  This function is used over
		// simply accessing iterNode.parent directly as it will
		// dynamically create previous block nodes as needed.  This
		// helps allow only the pieces of the chain that are needed
		// to remain in memory.
		iterNode = b.index.LookupNode(&iterNode.parent.hash)
		if iterNode == nil {
			break
		}
	}

	return numFound
}

// todo ppc check if we can attach to blockchain like this
func (b *BlockChain) verifySignature(utxoView *UtxoViewpoint, txIn *wire.TxIn, tx *btcutil.Tx,
	nIn uint32, fValidatePayToScriptHash bool, nHashType int) error {

	// Setup the script validation flags.  Blocks created after the BIP0016
	// activation time need to have the pay-to-script-hash checks enabled.
	var flags txscript.ScriptFlags
	if fValidatePayToScriptHash {
		flags |= txscript.ScriptBip16
	}

	txVI := &txValidateItem{
		txInIndex: int(nIn),
		txIn:      txIn,
		tx:        tx,
	}
	var txValItems [1]*txValidateItem
	txValItems[0] = txVI

	validator := newTxValidator(utxoView, flags, b.sigCache, b.hashCache) // todo ppc verify context
	if err := validator.Validate(txValItems[:]); err != nil {
		return err
	}

	return nil
}

// writeElement writes the little endian representation of element to w.
// original method in wire/common.go
func writeElement(w io.Writer, element interface{}) error {
	var scratch [8]byte

	// Attempt to write the element based on the concrete type via fast
	// type assertions first.
	switch e := element.(type) {
	case int32:
		b := scratch[0:4]
		binary.LittleEndian.PutUint32(b, uint32(e))
		_, err := w.Write(b)
		if err != nil {
			return err
		}
		return nil

	case uint32:
		b := scratch[0:4]
		binary.LittleEndian.PutUint32(b, e)
		_, err := w.Write(b)
		if err != nil {
			return err
		}
		return nil

	case int64:
		b := scratch[0:8]
		binary.LittleEndian.PutUint64(b, uint64(e))
		_, err := w.Write(b)
		if err != nil {
			return err
		}
		return nil

	case uint64:
		b := scratch[0:8]
		binary.LittleEndian.PutUint64(b, e)
		_, err := w.Write(b)
		if err != nil {
			return err
		}
		return nil

	case bool:
		b := scratch[0:1]
		if e == true {
			b[0] = 0x01
		} else {
			b[0] = 0x00
		}
		_, err := w.Write(b)
		if err != nil {
			return err
		}
		return nil

	// Message header checksum.
	case [4]byte:
		_, err := w.Write(e[:])
		if err != nil {
			return err
		}
		return nil

	// IP address.
	case [16]byte:
		_, err := w.Write(e[:])
		if err != nil {
			return err
		}
		return nil

	case *chainhash.Hash:
		_, err := w.Write(e[:])
		if err != nil {
			return err
		}
		return nil
	}

	// Fall back to the slower binary.Write if a fast path was not available
	// above.
	return binary.Write(w, binary.LittleEndian, element)
}
