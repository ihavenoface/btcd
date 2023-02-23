// Copyright (c) 2013-2016 The btcsuite developers
// Use of this source code is governed by an ISC
// license that can be found in the LICENSE file.

package btcutil

import (
	"bytes"
	"fmt"
	"io"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
)

// OutOfRangeError describes an error due to accessing an element that is out
// of range.
type OutOfRangeError string

// BlockHeightUnknown is the value returned for a block height that is unknown.
// This is typically because the block has not been inserted into the main chain
// yet.
const BlockHeightUnknown = int32(-1)

// Error satisfies the error interface and prints human-readable errors.
func (e OutOfRangeError) Error() string {
	return string(e)
}

// Block defines a bitcoin block that provides easier and more efficient
// manipulation of raw blocks.  It also memoizes hashes for the block and its
// transactions on their first access so subsequent accesses don't have to
// repeat the relatively expensive hashing operations.
type Block struct {
	msgBlock                 *wire.MsgBlock  // Underlying MsgBlock
	serializedBlock          []byte          // Serialized bytes for the block
	serializedBlockNoWitness []byte          // Serialized bytes for block w/o witness data
	blockHash                *chainhash.Hash // Cached block hash
	blockHeight              int32           // Height in the main block chain
	transactions             []*Tx           // Transactions
	txnsGenerated            bool            // ALL wrapped transactions generated
	meta                     *wire.Meta      // peercoin block meta data
	serializedMeta           []byte          // peercoin serialized bytes for the block meta
}

// MsgBlock returns the underlying wire.MsgBlock for the Block.
func (b *Block) MsgBlock() *wire.MsgBlock {
	// Return the cached block.
	return b.msgBlock
}

// Bytes returns the serialized bytes for the Block.  This is equivalent to
// calling Serialize on the underlying wire.MsgBlock, however it caches the
// result so subsequent calls are more efficient.
func (b *Block) Bytes() ([]byte, error) {
	// Return the cached serialized bytes if it has already been generated.
	if len(b.serializedBlock) != 0 {
		return b.serializedBlock, nil
	}

	// Serialize the MsgBlock.
	w := bytes.NewBuffer(make([]byte, 0, b.msgBlock.SerializeSize()))
	err := b.msgBlock.Serialize(w)
	if err != nil {
		return nil, err
	}
	serializedBlock := w.Bytes()

	// Cache the serialized bytes and return them.
	b.serializedBlock = serializedBlock
	return serializedBlock, nil
}

// BytesNoWitness returns the serialized bytes for the block with transactions
// encoded without any witness data.
func (b *Block) BytesNoWitness() ([]byte, error) {
	// Return the cached serialized bytes if it has already been generated.
	if len(b.serializedBlockNoWitness) != 0 {
		return b.serializedBlockNoWitness, nil
	}

	// Serialize the MsgBlock.
	var w bytes.Buffer
	err := b.msgBlock.SerializeNoWitness(&w)
	if err != nil {
		return nil, err
	}
	serializedBlock := w.Bytes()

	// Cache the serialized bytes and return them.
	b.serializedBlockNoWitness = serializedBlock
	return serializedBlock, nil
}

// Hash returns the block identifier hash for the Block.  This is equivalent to
// calling BlockHash on the underlying wire.MsgBlock, however it caches the
// result so subsequent calls are more efficient.
func (b *Block) Hash() *chainhash.Hash {
	// Return the cached block hash if it has already been generated.
	if b.blockHash != nil {
		return b.blockHash
	}

	// Cache the block hash and return it.
	hash := b.msgBlock.BlockHash()
	b.blockHash = &hash
	return &hash
}

// Tx returns a wrapped transaction (btcutil.Tx) for the transaction at the
// specified index in the Block.  The supplied index is 0 based.  That is to
// say, the first transaction in the block is txNum 0.  This is nearly
// equivalent to accessing the raw transaction (wire.MsgTx) from the
// underlying wire.MsgBlock, however the wrapped transaction has some helpful
// properties such as caching the hash so subsequent calls are more efficient.
func (b *Block) Tx(txNum int) (*Tx, error) {
	// Ensure the requested transaction is in range.
	numTx := uint64(len(b.msgBlock.Transactions))
	if txNum < 0 || uint64(txNum) >= numTx {
		str := fmt.Sprintf("transaction index %d is out of range - max %d",
			txNum, numTx-1)
		return nil, OutOfRangeError(str)
	}

	// Generate slice to hold all of the wrapped transactions if needed.
	if len(b.transactions) == 0 {
		b.transactions = make([]*Tx, numTx)
	}

	// Return the wrapped transaction if it has already been generated.
	if b.transactions[txNum] != nil {
		return b.transactions[txNum], nil
	}

	// Generate and cache the wrapped transaction and return it.
	newTx := NewTx(b.msgBlock.Transactions[txNum])
	newTx.SetIndex(txNum)
	b.transactions[txNum] = newTx
	return newTx, nil
}

// Transactions returns a slice of wrapped transactions (btcutil.Tx) for all
// transactions in the Block.  This is nearly equivalent to accessing the raw
// transactions (wire.MsgTx) in the underlying wire.MsgBlock, however it
// instead provides easy access to wrapped versions (btcutil.Tx) of them.
func (b *Block) Transactions() []*Tx {
	// Return transactions if they have ALL already been generated.  This
	// flag is necessary because the wrapped transactions are lazily
	// generated in a sparse fashion.
	if b.txnsGenerated {
		return b.transactions
	}

	// Generate slice to hold all of the wrapped transactions if needed.
	if len(b.transactions) == 0 {
		b.transactions = make([]*Tx, len(b.msgBlock.Transactions))
	}

	// Generate and cache the wrapped transactions for all that haven't
	// already been done.
	for i, tx := range b.transactions {
		if tx == nil {
			newTx := NewTx(b.msgBlock.Transactions[i])
			newTx.SetIndex(i)
			b.transactions[i] = newTx
		}
	}

	b.txnsGenerated = true
	return b.transactions
}

// TxHash returns the hash for the requested transaction number in the Block.
// The supplied index is 0 based.  That is to say, the first transaction in the
// block is txNum 0.  This is equivalent to calling TxHash on the underlying
// wire.MsgTx, however it caches the result so subsequent calls are more
// efficient.
func (b *Block) TxHash(txNum int) (*chainhash.Hash, error) {
	// Attempt to get a wrapped transaction for the specified index.  It
	// will be created lazily if needed or simply return the cached version
	// if it has already been generated.
	tx, err := b.Tx(txNum)
	if err != nil {
		return nil, err
	}

	// Defer to the wrapped transaction which will return the cached hash if
	// it has already been generated.
	return tx.Hash(), nil
}

// TxLoc returns the offsets and lengths of each transaction in a raw block.
// It is used to allow fast indexing into transactions within the raw byte
// stream.
func (b *Block) TxLoc() ([]wire.TxLoc, error) {
	rawMsg, err := b.Bytes()
	if err != nil {
		return nil, err
	}
	rbuf := bytes.NewBuffer(rawMsg)

	var mblock wire.MsgBlock
	txLocs, err := mblock.DeserializeTxLoc(rbuf)
	if err != nil {
		return nil, err
	}
	return txLocs, err
}

// Height returns the saved height of the block in the block chain.  This value
// will be BlockHeightUnknown if it hasn't already explicitly been set.
func (b *Block) Height() int32 {
	return b.blockHeight
}

// SetHeight sets the height of the block in the block chain.
func (b *Block) SetHeight(height int32) {
	b.blockHeight = height
}

// NewBlock returns a new instance of a bitcoin block given an underlying
// wire.MsgBlock.  See Block.
func NewBlock(msgBlock *wire.MsgBlock) *Block {
	return &Block{
		msgBlock:    msgBlock,
		blockHeight: BlockHeightUnknown,
	}
}

// NewBlockFromBytes returns a new instance of a bitcoin block given the
// serialized bytes.  See Block.
func NewBlockFromBytes(serializedBlock []byte) (*Block, error) {
	br := bytes.NewReader(serializedBlock)
	b, err := NewBlockFromReader(br)
	if err != nil {
		return nil, err
	}
	b.serializedBlock = serializedBlock
	return b, nil
}

// NewBlockFromReader returns a new instance of a bitcoin block given a
// Reader to deserialize the block.  See Block.
func NewBlockFromReader(r io.Reader) (*Block, error) {
	// Deserialize the bytes into a MsgBlock.
	var msgBlock wire.MsgBlock
	err := msgBlock.Deserialize(r)
	if err != nil {
		return nil, err
	}

	b := Block{
		msgBlock:    &msgBlock,
		blockHeight: BlockHeightUnknown,
	}
	return &b, nil
}

// NewBlockFromBlockAndBytes returns a new instance of a bitcoin block given
// an underlying wire.MsgBlock and the serialized bytes for it.  See Block.
func NewBlockFromBlockAndBytes(msgBlock *wire.MsgBlock, serializedBlock []byte) *Block {
	return &Block{
		msgBlock:        msgBlock,
		serializedBlock: serializedBlock,
		blockHeight:     BlockHeightUnknown,
	}
}

// peercoin start
// taken from legacy ppcsuite

// TxOffsetUnknown is the value returned for a transaction offset that is unknown.
// This is typically because the transaction has not been inserted into a block
// yet.
// const TxOffsetUnknown = uint32(0)

// KernelStakeModifierUnknown is the value returned for a block kernel stake
// modifier that is unknown.
// This is typically because the block has not been used for minting yet.
const KernelStakeModifierUnknown = uint64(0)

// Offset returns the saved offset of the transaction within a block.  This value
// will be TxOffsetUnknown if it hasn't already explicitly been set.
func (t *Tx) Offset() uint32 {
	return t.txOffset
}

// SetOffset sets the offset of the transaction in within a block.
func (t *Tx) SetOffset(offset uint32) {
	t.txOffset = offset
}

func (b *Block) Meta() *wire.Meta {
	if b.meta != nil {
		return b.meta
	}
	b.meta = new(wire.Meta)
	return b.meta
}

// MetaToBytes serializes block meta data to byte array
func (b *Block) MetaToBytes() ([]byte, error) {
	// Return the cached serialized bytes if it has already been generated.
	if len(b.serializedMeta) != 0 {
		return b.serializedMeta, nil
	}

	// Serialize the Meta.
	var w bytes.Buffer
	err := b.Meta().Serialize(&w)
	if err != nil {
		return nil, err
	}
	serializedMeta := w.Bytes()

	// Cache the serialized bytes and return them.
	b.serializedMeta = serializedMeta
	return serializedMeta, nil
}

// MetaFromBytes deserializes block meta data from byte array
func (b *Block) MetaFromBytes(serializedMeta []byte) error {
	mr := bytes.NewReader(serializedMeta)
	err := b.Meta().Deserialize(mr)
	if err != nil {
		return err
	}
	b.serializedMeta = serializedMeta
	return nil
}

// NewBlock returns a new instance of a peercoin block given an underlying
// wire.MsgBlock.  See Block.
func NewBlockWithMetas(msgBlock *wire.MsgBlock, meta *wire.Meta) *Block {
	return &Block{
		msgBlock:    msgBlock,
		blockHeight: BlockHeightUnknown,
		meta:        meta,
	}
}

// https://github.com/ppcoin/ppcoin/blob/v0.4.0ppc/src/main.h#L962
// ppc: two types of block: proof-of-work or proof-of-stake
func (block *Block) IsProofOfStake() bool {
	return block.msgBlock.IsProofOfStake()
}

func Now() time.Time {
	return time.Now()
}

/* todo ppc?
func TimeTrack(log btclog.Logger, start time.Time, name string) {
	elapsed := time.Since(start)
	log.Tracef("%s took %s", name, elapsed)
}

func Slice(args ...interface{}) []interface{} {
	return args
}
*/

// peercoin end