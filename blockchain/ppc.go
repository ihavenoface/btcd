// Copyright (c) 2014-2014 PPCD developers.
// Use of this source code is governed by an ISC
// license that can be found in the LICENSE file.

package blockchain

import (
	"fmt"
	"github.com/btcsuite/btcd/btcec/v2/ecdsa"
	"github.com/btcsuite/btcd/txscript"

	// "github.com/btcsuite/btcd/btcec/v2"
	"github.com/btcsuite/btcd/chaincfg"
	// "github.com/btcsuite/btcd/txscript"
	"math/big"

	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
)

// Peercoin
const (
	// InitialHashTargetBits TODO(?) golint
	InitialHashTargetBits uint32 = 0x1c00ffff
	// TargetSpacingWorkMax TODO(?) golint
	TargetSpacingWorkMax int64 = StakeTargetSpacing * 12
	// TargetTimespan TODO(?) golint
	TargetTimespan int64 = 7 * 24 * 60 * 60

	// Cent is the number of sunnys in one cent of peercoin
	Cent int64 = 10000
	// Coin is the number of sunnys in one peercoin
	Coin int64 = 100 * Cent
	// MinTxFee is the minimum transaction fee
	MinTxFee int64 = Cent
	// MinRelayTxFee is the minimum relayed transaction fee
	MinRelayTxFee int64 = Cent
	// MaxMoney is the max number of sunnys that can be generated
	MaxMoney int64 = 2000000000 * Coin
	// MaxMintProofOfWork is the max number of sunnys that can be POW minted
	MaxMintProofOfWork int64 = 9999 * Coin
	// MinTxOutAmount is the minimum output amount required for a transaction
	MinTxOutAmount int64 = MinTxFee

	// FBlockProofOfStake proof of stake blockNode flag (ppc)
	FBlockProofOfStake = uint32(1 << 0)
	// FBlockStakeEntropy entropy bit for stake modifier blockNode flag (ppc)
	FBlockStakeEntropy = uint32(1 << 1)
	// FBlockStakeModifier regenerated stake modifier blockNode flag (ppc)
	FBlockStakeModifier = uint32(1 << 2)
)

// Stake TODO(?) golint
type Stake struct {
	outPoint wire.OutPoint
	time     int64
}

type processPhase int

const (
	phasePreSanity processPhase = iota
)

func getProofOfStakeFromBlock(block *btcutil.Block) Stake {
	if block.IsProofOfStake() {
		tx := block.Transactions()[1].MsgTx()
		return Stake{tx.TxIn[0].PreviousOutPoint, tx.Timestamp.Unix()}
	}
	return Stake{}
}

var stakeSeen, stakeSeenOrphan = make(map[Stake]bool), make(map[Stake]bool)

// getBlockNode try to obtain a node form the memory block chain and loads it
// form the database in not found in memory.
func (b *BlockChain) getBlockNode(hash *chainhash.Hash) (*blockNode, error) {

	// Return the existing previous block node if it's already there.
	/*if bn, ok := b.index.LookupNode(hash); ok {
		return bn, nil
	}*/

	bn := b.index.LookupNode(hash)
	if bn != nil {
		return bn, nil
	}

	// Dynamically load the previous block from the block database, create
	// a new block node for it, and update the memory chain accordingly.
	// todo ppc
	/*prevBlockNode, err := b.loadBlockNode(hash)
	if err != nil {
		return nil, err
	}
	return prevBlockNode, nil
	*/
	return bn, nil
}

// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L894
// ppc: find last block index up to pindex
func (b *BlockChain) getLastBlockIndex(last *blockNode, proofOfStake bool) (block *blockNode) {

	/*
		if last == nil {
			defer timeTrack(now(), fmt.Sprintf("GetLastBlockIndex"))
		} else {
			defer timeTrack(now(), fmt.Sprintf("GetLastBlockIndex(%v)", last.hash))
		}
	*/

	block = last
	for true {
		if block == nil {
			break
		}
		// TODO dirty workaround, ppcoin doesn't point to genesis block
		if block.height == 0 {
			break
		}
		if block.parent == nil {
			break
		}
		if block.isProofOfStake() == proofOfStake {
			break
		}
		block = b.index.LookupNode(&block.parent.hash)
	}
	return block
}

// calcNextRequiredDifficulty calculates the required difficulty for the block
// after the passed previous block node based on the difficulty retarget rules.
// This function differs from the exported CalcNextRequiredDifficulty in that
// the exported version uses the current best chain as the previous block node
// while this function accepts any block node.
// Peercoin https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L902
func (b *BlockChain) ppcCalcNextRequiredDifficulty(lastNode *blockNode, proofOfStake bool) (uint32, error) {

	if lastNode == nil { // todo ppc
		return b.chainParams.PowLimitBits, nil // genesis block
	}

	// defer timeTrack(now(), fmt.Sprintf("ppcCalcNextRequiredDifficulty(%v)", lastNode.hash))

	prev := b.getLastBlockIndex(lastNode, proofOfStake)
	if prev.hash.IsEqual(b.chainParams.GenesisHash) {
		return b.chainParams.InitialHashTargetBits, nil // first block
	}
	prevParent := b.index.LookupNode(&prev.parent.hash)
	prevPrev := b.getLastBlockIndex(prevParent, proofOfStake)
	if prevPrev.hash.IsEqual(b.chainParams.GenesisHash) {
		return b.chainParams.InitialHashTargetBits, nil // second block
	}

	actualSpacing := prev.timestamp - prevPrev.timestamp

	newTarget := CompactToBig(prev.bits)
	var targetSpacing int64
	if proofOfStake {
		targetSpacing = StakeTargetSpacing
	} else {
		targetSpacing = minInt64(TargetSpacingWorkMax, StakeTargetSpacing*(int64(1+lastNode.height-prev.height)))
	}
	interval := TargetTimespan / targetSpacing
	targetSpacingBig := big.NewInt(targetSpacing)
	intervalMinusOne := big.NewInt(interval - 1)
	intervalPlusOne := big.NewInt(interval + 1)
	tmp := new(big.Int).Mul(intervalMinusOne, targetSpacingBig)
	tmp.Add(tmp, big.NewInt(actualSpacing+actualSpacing))
	newTarget.Mul(newTarget, tmp)
	newTarget.Div(newTarget, new(big.Int).Mul(intervalPlusOne, targetSpacingBig))

	if newTarget.Cmp(b.chainParams.PowLimit) > 0 {
		newTarget = b.chainParams.PowLimit
	}

	return BigToCompact(newTarget), nil
}

/*
// CalcNextRequiredDifficulty calculates the required difficulty for the block
// after the end of the current best chain based on the difficulty retarget
// rules.
//
// This function is NOT safe for concurrent access. Use blockmanager.
func (b *BlockChain) PPCCalcNextRequiredDifficulty(proofOfStake bool) (uint32, error) {
	return b.ppcCalcNextRequiredDifficulty(b.bestChain, proofOfStake)
}
*/

/*
// setCoinbaseMaturity sets required coinbase maturity and return old one
// Export required for tests only
func (b *BlockChain) SetCoinbaseMaturity(coinbaseMaturity int64) (old int64) {
	old = b.chainParams.CoinbaseMaturity
	b.chainParams.CoinbaseMaturity = coinbaseMaturity
	return
}
*/

// calcTrust calculates a work value from difficulty bits.  Bitcoin increases
// the difficulty for generating a block by decreasing the value which the
// generated hash must be less than.  This difficulty target is stored in each
// block header using a compact representation as described in the documenation
// for CompactToBig.  The main chain is selected by choosing the chain that has
// the most proof of work (highest difficulty).  Since a lower target difficulty
// value equates to higher actual difficulty, the work value which will be
// accumulated must be the inverse of the difficulty.  Also, in order to avoid
// potential division by zero and really small floating point numbers, the
// result adds 1 to the denominator and multiplies the numerator by 2^256.
func calcTrust(bits uint32, proofOfStake bool) *big.Int {
	// Return a work value of zero if the passed difficulty bits represent
	// a negative number. Note this should not happen in practice with valid
	// blocks, but an invalid block could trigger it.
	difficultyNum := CompactToBig(bits)
	if difficultyNum.Sign() <= 0 {
		return big.NewInt(0)
	}
	if !proofOfStake {
		return new(big.Int).SetInt64(1)
	}
	// (1 << 256) / (difficultyNum + 1)
	denominator := new(big.Int).Add(difficultyNum, bigOne)
	return new(big.Int).Div(oneLsh256, denominator)
}


// calcMintAndMoneySupply TODO(?) golint
func (b *BlockChain) calcMintAndMoneySupply(node *blockNode, block *btcutil.Block) error {

	nFees := int64(0)
	nValueIn := int64(0)
	nValueOut := int64(0)

	// todo ppc
	utxoView := NewUtxoViewpoint()
	err := utxoView.fetchInputUtxos(b.db, block)
	if err != nil {
		return err
	}

	transactions := block.Transactions()
	for _, tx := range transactions {

		nTxValueOut := int64(0)
		for _, txOut := range tx.MsgTx().TxOut {
			nTxValueOut += txOut.Value
		}

		if IsCoinBase(tx) {
			nValueOut += nTxValueOut
		} else {
			nTxValueIn := int64(0)
			for _, txIn := range tx.MsgTx().TxIn {
				// todo ppc placeholder. should be replaced
				originTx := utxoView.LookupEntry(txIn.PreviousOutPoint)
				// todo ppc error out when not found
				// originTxIndex := txIn.PreviousOutPoint.Index
				// originTxSatoshi := originTx.Amount() // originTx.Tx.MsgTx().TxOut[originTxIndex].Value
				nTxValueIn += originTx.Amount()
			}
			nValueIn += nTxValueIn
			nValueOut += nTxValueOut
			if !IsCoinStake(tx) {
				nFees += nTxValueIn - nTxValueOut
			}
		}
	}

	log.Debugf("height = %v, nValueIn = %v, nValueOut = %v, nFees = %v", block.Height(), nValueIn, nValueOut, nFees)

	// ppc: track money supply and mint amount info
	block.Meta().Mint = nValueOut - nValueIn + nFees
	var prevNode *blockNode
	prevNode = b.index.LookupNode(&node.hash)
	if prevNode == nil {
		return err
	}
	if prevNode == nil {
		block.Meta().MoneySupply = nValueOut - nValueIn
	} else {
		block.Meta().MoneySupply = prevNode.meta.MoneySupply + nValueOut - nValueIn
	}

	log.Debugf("height = %v, mint = %v, moneySupply = %v", block.Height(), block.Meta().Mint, block.Meta().MoneySupply)

	return nil
}

/*
// ppc: total coin age spent in transaction, in the unit of coin-days.
// Only those coins meeting minimum age requirement counts. As those
// transactions not in main chain are not currently indexed so we
// might not find out about their coin age. Older transactions are
// guaranteed to be in main chain by sync-checkpoint. This rule is
// introduced to help nodes establish a consistent view of the coin
// age (trust score) of competing branches.
func getCoinAgeTx(tx *btcutil.Tx, utxoView *UtxoViewpoint, chainParams *chaincfg.Params) (uint64, error) {

	bnCentSecond := big.NewInt(0) // coin age in the unit of cent-seconds

	if IsCoinBase(tx) {
		return 0, nil
	}

	nTime := tx.MsgTx().Timestamp.Unix()

	for _, txIn := range tx.MsgTx().TxIn {
		// First try finding the previous transaction in database
		txPrev := utxoView.LookupEntry(txIn.PreviousOutPoint)
		if txPrev == nil {
			continue // previous transaction not in main chain
		}
		txPrevTime := txPrev.Timestamp().Unix()
		if nTime < txPrevTime {
			err := fmt.Errorf("Transaction timestamp violation")
			return 0, err // Transaction timestamp violation
		}
		// todo ppc v3 tx does not carry timestamps, use block instead
		// todo ppc verify Timestamp does what we need it to
		// todo ppc this might be too lax. we either need blocktime in utxoview or another way to fetch the block itself
		if (txPrev.BlockTime().Unix()+chainParams.StakeMinAge > nTime) ||
			(txPrevTime+chainParams.StakeMinAge > nTime) {
			continue // only count coins meeting min age requirement
		}

		// todo ppc this is probably wrong
		// txPrevIndex := txIn.PreviousOutPoint.Index
		nValueIn := txPrev.Amount()
		bnCentSecond.Add(bnCentSecond,
			new(big.Int).Div(new(big.Int).Mul(big.NewInt(nValueIn), big.NewInt(nTime-txPrev.BlockTime().Unix())),
				big.NewInt(Cent)))

		log.Debugf("coin age nValueIn=%v nTimeDiff=%v bnCentSecond=%v", nValueIn, nTime-txPrev.BlockTime().Unix(), bnCentSecond.String())
	}

	bnCoinDay := new(big.Int).Div(new(big.Int).Mul(bnCentSecond, big.NewInt(Cent)),
		big.NewInt(int64(Coin)*24*60*60))
	log.Debugf("coin age bnCoinDay=%v", bnCoinDay.String())

	return bnCoinDay.Uint64(), nil
}
*/

/*
// ppc: total coin age spent in block, in the unit of coin-days.
func (b *BlockChain) getCoinAgeBlock(node *blockNode, block *btcutil.Block) (uint64, error) {


	txStore, err := b.fetchInputTransactions(node, block)
	if err != nil {
		return 0, err
	}

	nCoinAge := uint64(0)

	transactions := block.Transactions()
	for _, tx := range transactions {
		nTxCoinAge, err := b.getCoinAgeTx(tx, txStore)
		if err != nil {
			return 0, err
		}
		nCoinAge += nTxCoinAge
	}

	if nCoinAge == 0 { // block coin age minimum 1 coin-day
		nCoinAge = 1
	}

	log.Debugf("block coin age total nCoinDays=%v", nCoinAge)

	return nCoinAge, nil
}
*/

// PPCGetProofOfStakeReward
// Export requited, used my ppcwallet createCoinStake method
func PPCGetProofOfStakeReward(nCoinAge int64) btcutil.Amount {
	nRewardCoinYear := Cent // creation amount per coin-year
	nSubsidy := nCoinAge * 33 / (365*33 + 8) * nRewardCoinYear
	log.Debugf("getProofOfStakeReward(): create=%v nCoinAge=%v", nSubsidy, nCoinAge)
	return btcutil.Amount(nSubsidy)
}

// ppc: miner's coin stake is rewarded based on coin age spent (coin-days)
func getProofOfStakeReward(nCoinAge int64) int64 {
	nRewardCoinYear := Cent // creation amount per coin-year
	nSubsidy := nCoinAge * 33 / (365*33 + 8) * nRewardCoinYear
	log.Debugf("getProofOfStakeReward(): create=%v nCoinAge=%v", nSubsidy, nCoinAge)
	return nSubsidy
}

// IsCoinStake determines whether or not a transaction is a coinstake.  A coinstake
// is a special transaction created by peercoin minters.
// Export required as it is used in ppcwallet
func IsCoinStakeTx(tx *wire.MsgTx) bool {
	return tx.IsCoinStake()
}

// IsCoinStake determines whether or not a transaction is a coinstake.  A coinstake
// is a special transaction created by peercoin minters.
// Export required as it is used in mempool.go
func IsCoinStake(tx *btcutil.Tx) bool {
	return IsCoinStakeTx(tx.MsgTx())
}

/*
// ppcNewBlockNode returns a new block node for the given block header.  It is
// completely disconnected from the chain and the workSum value is just the work
// for the passed block.  The work sum is updated accordingly when the node is
// inserted into a chain.
func ppcNewBlockNode(
	blockHeader *wire.BlockHeader, blockSha *chainhash.Hash, height int64,
	blockMeta *wire.Meta) *blockNode {
	// Make a copy of the hash so the node doesn't keep a reference to part
	// of the full block/block header preventing it from being garbage
	// collected.
	prevHash := blockHeader.PrevBlock
	workSum := calcTrust(blockHeader.Bits, (blockMeta.Flags&FBlockProofOfStake) > 0)
	//log.Debugf("Height = %v, WorkSum = %v", height, workSum)
	node := blockNode{
		hash:       blockSha,
		parentHash: &prevHash,
		workSum:    workSum,
		height:     height,
		version:    blockHeader.Version,
		bits:       blockHeader.Bits,
		timestamp:  blockHeader.Timestamp,
		meta:       blockMeta,
	}
	return &node
}
*/
func initBlockNodePPC(node *blockNode, blockHeader *wire.BlockHeader, parent *blockNode, blockMeta *wire.Meta) {
	workSum := calcTrust(blockHeader.Bits, (blockMeta.Flags&FBlockProofOfStake) > 0)
	*node = blockNode{
		hash:       blockHeader.BlockHash(),
		workSum:    workSum,
		version:    blockHeader.Version,
		bits:       blockHeader.Bits,
		nonce:      blockHeader.Nonce,
		timestamp:  blockHeader.Timestamp.Unix(),
		merkleRoot: blockHeader.MerkleRoot,
		meta:       blockMeta,
	}
	if parent != nil {
		node.parent = parent
		node.height = parent.height + 1
		node.workSum = node.workSum.Add(parent.workSum, node.workSum)
	}
}

func newBlockNodePPC(blockHeader *wire.BlockHeader, parent *blockNode, blockMeta *wire.Meta) *blockNode {
	var node blockNode
	initBlockNodePPC(&node, blockHeader, parent, blockMeta)
	return &node
}

// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.h#L962
// ppc: two types of block: proof-of-work or proof-of-stake
func (block *blockNode) isProofOfStake() bool {
	return isProofOfStake(block.meta)
}

// ppc: two types of block: proof-of-work or proof-of-stake
func isProofOfStake(meta *wire.Meta) bool {
	return meta.Flags&FBlockProofOfStake != 0
}

// setProofOfStake
func setProofOfStake(meta *wire.Meta, proofOfStake bool) {
	if proofOfStake {
		meta.Flags |= FBlockProofOfStake
	} else {
		meta.Flags &^= FBlockProofOfStake
	}
}

// isGeneratedStakeModifier
func isGeneratedStakeModifier(meta *wire.Meta) bool {
	return meta.Flags&FBlockStakeModifier != 0
}

// setGeneratedStakeModifier
func setGeneratedStakeModifier(meta *wire.Meta, generated bool) {
	if generated {
		meta.Flags |= FBlockStakeModifier
	} else {
		meta.Flags &^= FBlockStakeModifier
	}
}

// getMetaStakeEntropyBit
func getMetaStakeEntropyBit(meta *wire.Meta) uint32 {
	if meta.Flags&FBlockStakeEntropy != 0 {
		return 1
	}
	return 0
}

// setMetaStakeEntropyBit
func setMetaStakeEntropyBit(meta *wire.Meta, entropyBit uint32) {
	if entropyBit == 0 {
		meta.Flags &^= FBlockStakeEntropy
	} else {
		meta.Flags |= FBlockStakeEntropy
	}
}

// bigToShaHash converts a big.Int into a chainhash.Hash.
func bigToShaHash(value *big.Int) (*chainhash.Hash, error) {

	buf := value.Bytes()

	blen := len(buf)
	for i := 0; i < blen/2; i++ {
		buf[i], buf[blen-1-i] = buf[blen-1-i], buf[i]
	}

	// Make sure the byte slice is the right length by appending zeros to
	// pad it out.
	pbuf := buf
	if chainhash.HashSize-blen > 0 {
		pbuf = make([]byte, chainhash.HashSize)
		copy(pbuf, buf)
	}

	return chainhash.NewHash(pbuf)
}


// PPCGetLastProofOfWorkReward
// Export required, used in ppcwallet CreateCoinStake method
// todo ppc unused -> ppcGetLastProofOfWorkRewardMsg in netsync
func (b *BlockChain) PPCGetLastProofOfWorkReward() (subsidy int64) {
	lastPOWNode := b.getLastBlockIndex(b.bestChain.Tip(), false)
	return PPCGetProofOfWorkReward(lastPOWNode.bits, b.chainParams)
}

// ppcGetProofOfWorkReward is Peercoin's validate.go:CalcBlockSubsidy(...)
// counterpart.
// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L829
// Export required, used in NewBlockTemplate method
func PPCGetProofOfWorkReward(nBits uint32, chainParams *chaincfg.Params) (subsidy int64) {
	bigTwo := new(big.Int).SetInt64(2)
	bnSubsidyLimit := new(big.Int).SetInt64(MaxMintProofOfWork)
	bnTarget := CompactToBig(nBits)
	bnTargetLimit := chainParams.PowLimit
	// TODO(kac-) wat? bnTargetLimit.SetCompact(bnTargetLimit.GetCompact());
	bnTargetLimit = CompactToBig(BigToCompact(bnTargetLimit))
	// ppc: subsidy is cut in half every 16x multiply of difficulty
	// A reasonably continuous curve is used to avoid shock to market
	// (nSubsidyLimit / nSubsidy) ** 4 == bnProofOfWorkLimit / bnTarget
	bnLowerBound := new(big.Int).SetInt64(Cent)
	bnUpperBound := new(big.Int).Set(bnSubsidyLimit)
	for new(big.Int).Add(bnLowerBound, new(big.Int).SetInt64(Cent)).Cmp(bnUpperBound) <= 0 {
		bnMidValue := new(big.Int).Div(new(big.Int).Add(bnLowerBound, bnUpperBound), bigTwo)
		/*
			if (fDebug && GetBoolArg("-printcreation"))
			printf("GetProofOfWorkReward() : lower=%"PRI64d" upper=%"PRI64d" mid=%"PRI64d"\n", bnLowerBound.getuint64(), bnUpperBound.getuint64(), bnMidValue.getuint64());
		*/
		mid := new(big.Int).Set(bnMidValue)
		sub := new(big.Int).Set(bnSubsidyLimit)
		//if (bnMidValue * bnMidValue * bnMidValue * bnMidValue * bnTargetLimit > bnSubsidyLimit * bnSubsidyLimit * bnSubsidyLimit * bnSubsidyLimit * bnTarget)
		if mid.Mul(mid, mid).Mul(mid, mid).Mul(mid, bnTargetLimit).Cmp(sub.Mul(sub, sub).Mul(sub, sub).Mul(sub, bnTarget)) > 0 {
			bnUpperBound = bnMidValue
		} else {
			bnLowerBound = bnMidValue
		}
	}
	subsidy = bnUpperBound.Int64()
	subsidy = (subsidy / Cent) * Cent
	if subsidy > MaxMintProofOfWork {
		subsidy = MaxMintProofOfWork
	}
	return
}

// GetMinFee calculates minimum required required for transaction.
// Export required, used in ppcwallet createCoinStake method
func GetMinFee(tx *wire.MsgTx) int64 {
	baseFee := MinTxFee
	bytes := tx.SerializeSize()
	minFee := (1 + int64(bytes)/1000) * baseFee
	return minFee
}

// getMinFee calculates minimum required required for transaction.
// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.h#L592
// Export required, used in ppcwallet createCoinStake method
func getMinFee(tx *btcutil.Tx) int64 {
	baseFee := MinTxFee
	bytes := tx.MsgTx().SerializeSize()
	minFee := (1 + int64(bytes)/1000) * baseFee
	return minFee
}

// checkBlockSignature ppc: check block signature
// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L2116
// Export required for tests only
func CheckBlockSignature(msgBlock *wire.MsgBlock,
	params *chaincfg.Params) bool {
	sha := msgBlock.BlockHash()
	if sha.IsEqual(params.GenesisHash) {
		return len(msgBlock.Signature) == 0
	}
	var txOut *wire.TxOut
	if msgBlock.IsProofOfStake() {
		txOut = msgBlock.Transactions[1].TxOut[1]
	} else {
		txOut = msgBlock.Transactions[0].TxOut[0]
	}
	scriptClass, addresses, _, err := txscript.ExtractPkScriptAddrs(txOut.PkScript, params)
	if err != nil {
		return false
	}
	if scriptClass != txscript.PubKeyTy {
		return false
	}
	a, ok := addresses[0].(*btcutil.AddressPubKey)
	if !ok {
		return false
	}
	// todo ppc btcec.ParseSignature(msgBlock.Signature, btcec.S256()) -> ecdsa.ParseSignature(msgBlock.Signature)
	sig, err := ecdsa.ParseSignature(msgBlock.Signature)
	if err != nil {
		return false
	}
	// todo ppc .Bytes() -> slice
	return sig.Verify(sha[:], a.PubKey())
}

func IsZeroAllowed(nTimeTx int64) bool {
	return nTimeTx >= 1447700000 // very crude approximation to prevent linking with kernel.cpp
}

// Peercoin additional context free transaction checks.
// Basing on CTransaction::CheckTransaction().
// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L445
func ppcCheckTransactionSanity(tx *btcutil.Tx) error { // todo ppc add more rules where needed
	msgTx := tx.MsgTx()
	for _, txOut := range msgTx.TxOut {
		// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L461
		// if (txout.IsEmpty() && (!IsCoinBase()) && (!IsCoinStake()))
		// 	return DoS(100, error("CTransaction::CheckTransaction() : txout empty for user transaction"));
		if txOut.IsEmpty() && (!IsCoinBase(tx)) && (!IsCoinStake(tx)) {
			str := "transaction output empty for user transaction"
			return ruleError(ErrEmptyTxOut, str)
		}

		// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L463
		// ppc: enforce minimum output amount
		// if ((!txout.IsEmpty()) && txout.nValue < MIN_TXOUT_AMOUNT)
		// 	return DoS(100, error("CTransaction::CheckTransaction() : txout.nValue below minimum"));
		if (!txOut.IsEmpty()) && txOut.Value < MinTxOutAmount &&
			(msgTx.Version < 3 && !(IsZeroAllowed(msgTx.Timestamp.Unix()) && (txOut.Value == 0))) {
			str := fmt.Sprintf("transaction output value of %v is below minimum %v",
				txOut.Value, MinTxOutAmount)
			return ruleError(ErrBadTxOutValue, str)
		}
	}
	return nil
}

// Peercoin additional transaction checks.
// Basing on CTransaction::ConnectInputs().
// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1149
func ppcCheckTransactionInputs(tx *btcutil.Tx, utxoView *UtxoViewpoint,
	satoshiIn int64, satoshiOut int64, chainParams *chaincfg.Params) error {
	// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1230
	// ppc: coin stake tx earns reward instead of paying fee
	// if (IsCoinStake())
	// {
	// uint64 nCoinAge;
	// if (!GetCoinAge(txdb, nCoinAge))
	// 	return error("ConnectInputs() : %s unable to get coin age for coinstake", GetHash().ToString().substr(0,10).c_str());
	// int64 nStakeReward = GetValueOut() - nValueIn;
	// if (nStakeReward > getProofOfStakeReward(nCoinAge) - GetMinFee() + MIN_TX_FEE)
	// 	return DoS(100, error("ConnectInputs() : %s stake reward exceeded", GetHash().ToString().substr(0,10).c_str()));
	// }
	if IsCoinStake(tx) {
		coinAge, err := getCoinAgeTx(tx, utxoView, chainParams) // todo ppc output here doesn't make sense yet
		if err != nil {
			return fmt.Errorf("unable to get coin age for coinstake: %v", err)
		}
		stakeReward := satoshiOut - satoshiIn
		maxReward := getProofOfStakeReward(int64(coinAge)) - getMinFee(tx) + MinTxFee
		if stakeReward > maxReward {
			str := fmt.Sprintf("%v stake reward value %v exceeded %v", tx.Hash(), stakeReward, maxReward)
			return ruleError(ErrBadCoinstakeValue, str)
		}
		*/
	} else {
		// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1249
		// ppc: enforce transaction fees for every block
		// if (nTxFee < GetMinFee())
		// 	return fBlock? DoS(100, error("ConnectInputs() : %s not paying required fee=%s, paid=%s", GetHash().ToString().substr(0,10).c_str(), FormatMoney(GetMinFee()).c_str(), FormatMoney(nTxFee).c_str())) : false;
		txFee := satoshiIn - satoshiOut
		if txFee < getMinFee(tx) {
			str := fmt.Sprintf("%v not paying required fee=%v, paid=%v", tx.Hash(), getMinFee(tx), txFee)
			return ruleError(ErrInsufficientFee, str)
		}
	}
	return nil
}

func ppcCheckTransactionInput(tx *btcutil.Tx, txIn *wire.TxIn, originUtxo *UtxoEntry) error {
	// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1177
	// ppc: check transaction timestamp
	// if (txPrev.nTime > nTime)
	// 	return DoS(100, error("ConnectInputs() : transaction timestamp earlier than input transaction"));
	// todo ppc I added timestamp to utxoview, and it might not be accurate.
	if originUtxo.Timestamp().After(tx.MsgTx().Timestamp) {
		str := "transaction timestamp earlier than input transaction"
		return ruleError(ErrEarlierTimestamp, str)
	}
	return nil
}

// Peercoin additional context free block checks.
// Basing on CBlock::CheckBlock().
// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1829
func ppcCheckBlockSanity(chainParams *chaincfg.Params, block *btcutil.Block) error {
	msgBlock := block.MsgBlock()
	// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1853
	// ppc: only the second transaction can be the optional coinstake
	// for (int i = 2; i < vtx.size(); i++)
	// 	if (vtx[i].IsCoinStake())
	// 		return DoS(100, error("CheckBlock() : coinstake in wrong position"));
	for i := 2; i < len(msgBlock.Transactions); i++ {
		if msgBlock.Transactions[i].IsCoinStake() {
			str := "coinstake in wrong position"
			return ruleError(ErrWrongCoinstakePosition, str)
		}
	}
	// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1858
	// peercoin: first coinbase output should be empty if proof-of-stake block
	// if (block.IsProofOfStake() && !block.vtx[0]->vout[0].IsEmpty())
	//    return state.Invalid(BlockValidationResult::BLOCK_CONSENSUS, "bad-cb-notempty", "coinbase output not empty in PoS block");
	if block.IsProofOfStake() && !msgBlock.Transactions[0].TxOut[0].IsEmpty() {
		str := "coinbase output not empty for proof-of-stake block"
		return ruleError(ErrCoinbaseNotEmpty, str)
	}
	// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1866
	// Check coinstake timestamp
	// if (IsProofOfStake() && !CheckCoinStakeTimestamp(GetBlockTime(), (int64)vtx[1].nTime))
	// 	return DoS(50, error("CheckBlock() : coinstake timestamp violation nTimeBlock=%u nTimeTx=%u", GetBlockTime(), vtx[1].nTime));
	if msgBlock.IsProofOfStake() && !checkCoinStakeTimestamp(chainParams, msgBlock.Header.Timestamp.Unix(),
		msgBlock.Transactions[1].Timestamp.Unix()) {
		str := fmt.Sprintf("coinstake timestamp violation TimeBlock=%v TimeTx=%v",
			msgBlock.Header.Timestamp, msgBlock.Transactions[1].Timestamp)
		return ruleError(ErrCoinstakeTimeViolation, str)
	}
	for _, tx := range msgBlock.Transactions {
		// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1881
		// ppc: check transaction timestamp
		// if (GetBlockTime() < (int64)tx.nTime)
		//  return DoS(50, error("CheckBlock() : block timestamp earlier than transaction timestamp"));
		if msgBlock.Header.Timestamp.Before(tx.Timestamp) {
			str := "block timestamp earlier than transaction timestamp"
			return ruleError(ErrBlockBeforeTx, str)
		}
	}
	// ppc: check block signature
	// if (!CheckBlockSignature())
	// 	return DoS(100, error("CheckBlock() : bad block signature"));
	// todo ppc enable for PoW blocks
	if msgBlock.IsProofOfStake() && !CheckBlockSignature(msgBlock, chainParams) {
		str := "bad block signature"
		return ruleError(ErrBadBlockSignature, str)
	}
	return nil
}

func (b *BlockChain) ppcProcessOrphan(block *btcutil.Block) error {
	// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L2036
	// ppc: check proof-of-stake
	if block.IsProofOfStake() {
		// Limited duplicity on stake: prevents block flood attack
		// Duplicate stake allowed only when there is orphan child block
		sha := block.Hash()
		stake := getProofOfStakeFromBlock(block)
		_, seen := stakeSeen[stake]
		childs, hasChild := b.prevOrphans[*sha]
		hasChild = hasChild && (len(childs) > 0)
		if seen && !hasChild {
			str := fmt.Sprintf("duplicate proof-of-stake (%v) for orphan block %s", stake, sha)
			return ruleError(ErrDuplicateStake, str)
		}
		stakeSeenOrphan[stake] = true
	}
	// TODO(kac-:dup-stake)
	// there is explicit Ask for block not handled now
	// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L2055
	return nil
}

func (b *BlockChain) ppcOrphanBlockRemoved(block *btcutil.Block) {
	// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L2078
	delete(stakeSeenOrphan, getProofOfStakeFromBlock(block))
}

func (b *BlockChain) ppcProcessBlock(block *btcutil.Block, phase processPhase) error {
	switch phase {
	case phasePreSanity:
		// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.cpp#L1985
		// ppc: check proof-of-stake
		// Limited duplicity on stake: prevents block flood attack
		// Duplicate stake allowed only when there is orphan child block
		// TODO(kac-) should it be exported to limitedStakeDuplicityCheck(block)error ?
		if block.IsProofOfStake() {
			sha := block.Hash()
			stake := getProofOfStakeFromBlock(block)
			_, seen := stakeSeen[stake]
			childs, hasChild := b.prevOrphans[*sha]
			hasChild = hasChild && (len(childs) > 0)
			if seen && !hasChild {
				str := fmt.Sprintf("duplicate proof-of-stake (%v) for orphan block %s", stake, sha)
				return ruleError(ErrDuplicateStake, str)
			}
		}
	}
	return nil
}

/* todo ppc unused -> netsync
// GetLastBlockHeader ppc: find last block from db up to lastSha
func GetLastBlockHeader(db database.Db, lastSha *chainhash.Hash, proofOfStake bool) (
	header *wire.BlockHeader, meta *wire.Meta, err error) {
	sha := lastSha
	for true {
		header, meta, err = db.FetchBlockHeaderBySha(sha)
		if err != nil {
			break
		}
		if header.PrevBlock.IsEqual(&zeroHash) {
			break
		}
		if isProofOfStake(meta) == proofOfStake {
			break
		}
		sha = &header.PrevBlock
	}
	return
}
*/

/* todo ppc -> netsync
// GetKernelStakeModifier
// This function is NOT safe for concurrent access. Use blockmanager.
func (b *BlockChain) GetKernelStakeModifier(hash *chainhash.Hash, timeSource MedianTimeSource) (uint64, error) {
	stakeModifier, _, _, err := b.getKernelStakeModifier(hash, timeSource, false)
	return stakeModifier, err
}
*/

// WantedOrphan finds block wanted by given orphan block
//
// This function is safe for concurrent access.
func (b *BlockChain) WantedOrphan(hash *chainhash.Hash) *chainhash.Hash {
	// Protect concurrent access.  Using a read lock only so multiple
	// readers can query without blocking each other.
	b.orphanLock.RLock()
	defer b.orphanLock.RUnlock()

	// Work back to the first block in the orphan chain
	prevHash := hash
	for {
		orphan, exists := b.orphans[*prevHash]
		if !exists {
			break
		}
		prevHash = &orphan.block.MsgBlock().Header.PrevBlock
	}

	return prevHash
}
