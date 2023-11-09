// Copyright (c) 2013-2016 The btcsuite developers
// Use of this source code is governed by an ISC
// license that can be found in the LICENSE file.

package wire

import (
	"bytes"
	"io"
	"reflect"
	"testing"

	"github.com/davecgh/go-spew/spew"
)

// TestHeaders tests the MsgHeaders API.
func TestHeaders(t *testing.T) {
	pver := uint32(60002)

	// Ensure the command is expected value.
	wantCmd := "headers"
	msg := NewMsgHeaders()
	if cmd := msg.Command(); cmd != wantCmd {
		t.Errorf("NewMsgHeaders: wrong command - got %v want %v",
			cmd, wantCmd)
	}

	// Ensure max payload is expected value for latest protocol version.
	// Num headers (varInt) + max allowed headers (header length + 1 byte
	// for the number of transactions which is always 0).
	wantPayload := uint32(178009)
	maxPayload := msg.MaxPayloadLength(pver)
	if maxPayload != wantPayload {
		t.Errorf("MaxPayloadLength: wrong max payload length for "+
			"protocol version %d - got %v, want %v", pver,
			maxPayload, wantPayload)
	}

	// Ensure headers are added properly.
	bh := &blockOne.Header
	msg.AddBlockHeader(bh)
	if !reflect.DeepEqual(msg.Headers[0], bh) {
		t.Errorf("AddHeader: wrong header - got %v, want %v",
			spew.Sdump(msg.Headers),
			spew.Sdump(bh))
	}

	// Ensure adding more than the max allowed headers per message returns
	// error.
	var err error
	for i := 0; i < MaxBlockHeadersPerMsg+1; i++ {
		err = msg.AddBlockHeader(bh)
	}
	if reflect.TypeOf(err) != reflect.TypeOf(&MessageError{}) {
		t.Errorf("AddBlockHeader: expected error on too many headers " +
			"not received")
	}
}

// TestHeadersWire tests the MsgHeaders wire encode and decode for various
// numbers of headers and protocol versions.
func TestHeadersWire(t *testing.T) {
	hash := mainNetGenesisHash
	merkleHash := blockOne.Header.MerkleRoot
	bits := uint32(0x1c00ffff)
	nonce := uint32(0x722a498e)
	flags := blockOne.Header.Flags
	bh := NewBlockHeader(1, &hash, &merkleHash, bits, nonce, flags)
	bh.Version = blockOne.Header.Version
	bh.Timestamp = blockOne.Header.Timestamp

	// Empty headers message.
	noHeaders := NewMsgHeaders()
	noHeadersEncoded := []byte{
		0x00, // Varint for number of headers
	}

	// Headers message with one header.
	oneHeader := NewMsgHeaders()
	oneHeader.AddBlockHeader(bh)
	oneHeaderEncoded := []byte{
		0x01,                   // VarInt for number of headers.
		0x01, 0x00, 0x00, 0x00, // Version 1
		0xe3, 0x27, 0xcd, 0x80, 0xc8, 0xb1, 0x7e, 0xfd,
		0xa4, 0xea, 0x08, 0xc5, 0x87, 0x7e, 0x95, 0xd8,
		0x77, 0x46, 0x2a, 0xb6, 0x63, 0x49, 0xd5, 0x66,
		0x71, 0x67, 0xfe, 0x32, 0x00, 0x00, 0x00, 0x00, // PrevBlock
		0x68, 0xf6, 0x23, 0xd2, 0x06, 0xa1, 0xbd, 0xe3,
		0xb0, 0x38, 0x2e, 0x97, 0xaf, 0x9c, 0x0b, 0x6b,
		0xfa, 0x70, 0x8c, 0xa4, 0xc2, 0x5f, 0x33, 0x99,
		0x53, 0xe1, 0x34, 0xff, 0x4e, 0xe8, 0xda, 0x1b, // MerkleRoot
		0x24, 0x2e, 0x31, 0x50, // Timestamp
		0xff, 0xff, 0x00, 0x1c, // Bits
		0x8e, 0x49, 0x2a, 0x72, // Nonce
		0x00, 0x00, 0x00, 0x00, // Flags
		0x00, // todo ppc shouldn't be here, buffer possibly extended too far on init
		0x00, // TxnCount (0 for headers message)
	}

	tests := []struct {
		in   *MsgHeaders     // Message to encode
		out  *MsgHeaders     // Expected decoded message
		buf  []byte          // Wire encoding
		pver uint32          // Protocol version for wire encoding
		enc  MessageEncoding // Message encoding format
	}{
		// Latest protocol version with no headers.
		{
			noHeaders,
			noHeaders,
			noHeadersEncoded,
			ProtocolVersion,
			BaseEncoding,
		},

		// Latest protocol version with one header.
		{
			oneHeader,
			oneHeader,
			oneHeaderEncoded,
			ProtocolVersion,
			BaseEncoding,
		},

		// Protocol version BIP0035Version with no headers.
		{
			noHeaders,
			noHeaders,
			noHeadersEncoded,
			BIP0035Version,
			BaseEncoding,
		},

		// Protocol version BIP0035Version with one header.
		{
			oneHeader,
			oneHeader,
			oneHeaderEncoded,
			BIP0035Version,
			BaseEncoding,
		},

		// Protocol version BIP0031Version with no headers.
		{
			noHeaders,
			noHeaders,
			noHeadersEncoded,
			BIP0031Version,
			BaseEncoding,
		},

		// Protocol version BIP0031Version with one header.
		{
			oneHeader,
			oneHeader,
			oneHeaderEncoded,
			BIP0031Version,
			BaseEncoding,
		},
		// Protocol version NetAddressTimeVersion with no headers.
		{
			noHeaders,
			noHeaders,
			noHeadersEncoded,
			NetAddressTimeVersion,
			BaseEncoding,
		},

		// Protocol version NetAddressTimeVersion with one header.
		{
			oneHeader,
			oneHeader,
			oneHeaderEncoded,
			NetAddressTimeVersion,
			BaseEncoding,
		},

		// Protocol version MultipleAddressVersion with no headers.
		{
			noHeaders,
			noHeaders,
			noHeadersEncoded,
			MultipleAddressVersion,
			BaseEncoding,
		},

		// Protocol version MultipleAddressVersion with one header.
		{
			oneHeader,
			oneHeader,
			oneHeaderEncoded,
			MultipleAddressVersion,
			BaseEncoding,
		},
	}

	t.Logf("Running %d tests", len(tests))
	for i, test := range tests {
		// Encode the message to wire format.
		var buf bytes.Buffer
		err := test.in.BtcEncode(&buf, test.pver, test.enc)
		if err != nil {
			t.Errorf("BtcEncode #%d error %v", i, err)
			continue
		}
		if !bytes.Equal(buf.Bytes(), test.buf) {
			t.Errorf("BtcEncode #%d\n got: %s want: %s", i,
				spew.Sdump(buf.Bytes()), spew.Sdump(test.buf))
			continue
		}

		// Decode the message from wire format.
		var msg MsgHeaders
		rbuf := bytes.NewReader(test.buf)
		err = msg.BtcDecode(rbuf, test.pver, test.enc)
		if err != nil {
			t.Errorf("BtcDecode #%d error %v", i, err)
			continue
		}
		if !reflect.DeepEqual(&msg, test.out) {
			t.Errorf("BtcDecode #%d\n got: %s want: %s", i,
				spew.Sdump(&msg), spew.Sdump(test.out))
			continue
		}
	}
}

// TestHeadersWireErrors performs negative tests against wire encode and decode
// of MsgHeaders to confirm error paths work correctly.
func TestHeadersWireErrors(t *testing.T) {
	pver := ProtocolVersion
	wireErr := &MessageError{}

	hash := mainNetGenesisHash
	merkleHash := blockOne.Header.MerkleRoot
	bits := uint32(0x1c00ffff)
	nonce := uint32(0x722a498e)
	flags := blockOne.Header.Flags
	bh := NewBlockHeader(1, &hash, &merkleHash, bits, nonce, flags)
	bh.Version = blockOne.Header.Version
	bh.Timestamp = blockOne.Header.Timestamp

	// Headers message with one header.
	oneHeader := NewMsgHeaders()
	oneHeader.AddBlockHeader(bh)
	oneHeaderEncoded := []byte{
		0x01,                   // VarInt for number of headers.
		0x01, 0x00, 0x00, 0x00, // Version 1
		0xe3, 0x27, 0xcd, 0x80, 0xc8, 0xb1, 0x7e, 0xfd,
		0xa4, 0xea, 0x08, 0xc5, 0x87, 0x7e, 0x95, 0xd8,
		0x77, 0x46, 0x2a, 0xb6, 0x63, 0x49, 0xd5, 0x66,
		0x71, 0x67, 0xfe, 0x32, 0x00, 0x00, 0x00, 0x00, // PrevBlock
		0x68, 0xf6, 0x23, 0xd2, 0x06, 0xa1, 0xbd, 0xe3,
		0xb0, 0x38, 0x2e, 0x97, 0xaf, 0x9c, 0x0b, 0x6b,
		0xfa, 0x70, 0x8c, 0xa4, 0xc2, 0x5f, 0x33, 0x99,
		0x53, 0xe1, 0x34, 0xff, 0x4e, 0xe8, 0xda, 0x1b, // MerkleRoot
		0x24, 0x2e, 0x31, 0x50, // Timestamp
		0xff, 0xff, 0x00, 0x1c, // Bits
		0x8e, 0x49, 0x2a, 0x72, // Nonce
		0x00, 0x00, 0x00, 0x00, // Flags
		0x00, // todo ppc shouldn't be here, buffer possibly extended too much on init
		0x00, // TxnCount (0 for headers message)
	}

	// Message that forces an error by having more than the max allowed
	// headers.
	maxHeaders := NewMsgHeaders()
	for i := 0; i < MaxBlockHeadersPerMsg; i++ {
		maxHeaders.AddBlockHeader(bh)
	}
	maxHeaders.Headers = append(maxHeaders.Headers, bh)
	maxHeadersEncoded := []byte{
		0xfd, 0xd1, 0x07, // Varint for number of addresses (2001)7D1
	}

	// Intentionally invalid block header that has a transaction count used
	// to force errors.
	bhTrans := NewBlockHeader(1, &hash, &merkleHash, bits, nonce, flags)
	bhTrans.Version = blockOne.Header.Version
	bhTrans.Timestamp = blockOne.Header.Timestamp

	transHeader := NewMsgHeaders()
	transHeader.AddBlockHeader(bhTrans)
	transHeaderEncoded := []byte{
		0x01,                   // VarInt for number of headers.
		0x01, 0x00, 0x00, 0x00, // Version 1
		0xe3, 0x27, 0xcd, 0x80, 0xc8, 0xb1, 0x7e, 0xfd,
		0xa4, 0xea, 0x08, 0xc5, 0x87, 0x7e, 0x95, 0xd8,
		0x77, 0x46, 0x2a, 0xb6, 0x63, 0x49, 0xd5, 0x66,
		0x71, 0x67, 0xfe, 0x32, 0x00, 0x00, 0x00, 0x00, // PrevBlock
		0x68, 0xf6, 0x23, 0xd2, 0x06, 0xa1, 0xbd, 0xe3,
		0xb0, 0x38, 0x2e, 0x97, 0xaf, 0x9c, 0x0b, 0x6b,
		0xfa, 0x70, 0x8c, 0xa4, 0xc2, 0x5f, 0x33, 0x99,
		0x53, 0xe1, 0x34, 0xff, 0x4e, 0xe8, 0xda, 0x1b, // MerkleRoot
		0x24, 0x2e, 0x31, 0x50, // Timestamp
		0xff, 0xff, 0x00, 0x1c, // Bits
		0x8e, 0x49, 0x2a, 0x72, // Nonce
		0x00, 0x00, 0x00, 0x00, // Flags
		0x00, // todo ppc shouldn't be here, buffer possibly extended too far on init
		0x01, // TxnCount (should be 0 for headers message, but 1 to force error)
	}

	tests := []struct {
		in       *MsgHeaders     // Value to encode
		buf      []byte          // Wire encoding
		pver     uint32          // Protocol version for wire encoding
		enc      MessageEncoding // Message encoding format
		max      int             // Max size of fixed buffer to induce errors
		writeErr error           // Expected write error
		readErr  error           // Expected read error
	}{
		// Latest protocol version with intentional read/write errors.
		// Force error in header count.
		{oneHeader, oneHeaderEncoded, pver, BaseEncoding, 0, io.ErrShortWrite, io.EOF},
		// Force error in block header.
		{oneHeader, oneHeaderEncoded, pver, BaseEncoding, 5, io.ErrShortWrite, io.EOF},
		// Force error with greater than max headers.
		{maxHeaders, maxHeadersEncoded, pver, BaseEncoding, 3, wireErr, wireErr},
		// Force error with number of transactions.
		{transHeader, transHeaderEncoded, pver, BaseEncoding, 81, io.ErrShortWrite, io.EOF},
		// Force error with included transactions.
		{transHeader, transHeaderEncoded, pver, BaseEncoding, len(transHeaderEncoded), nil, wireErr},
	}

	t.Logf("Running %d tests", len(tests))
	for i, test := range tests {
		// Encode to wire format.
		w := newFixedWriter(test.max)
		err := test.in.BtcEncode(w, test.pver, test.enc)
		if reflect.TypeOf(err) != reflect.TypeOf(test.writeErr) {
			t.Errorf("BtcEncode #%d wrong error got: %v, want: %v",
				i, err, test.writeErr)
			continue
		}

		// For errors which are not of type MessageError, check them for
		// equality.
		if _, ok := err.(*MessageError); !ok {
			if err != test.writeErr {
				t.Errorf("BtcEncode #%d wrong error got: %v, "+
					"want: %v", i, err, test.writeErr)
				continue
			}
		}

		// Decode from wire format.
		var msg MsgHeaders
		r := newFixedReader(test.max, test.buf)
		err = msg.BtcDecode(r, test.pver, test.enc)
		if reflect.TypeOf(err) != reflect.TypeOf(test.readErr) {
			t.Errorf("BtcDecode #%d wrong error got: %v, want: %v",
				i, err, test.readErr)
			continue
		}

		// For errors which are not of type MessageError, check them for
		// equality.
		if _, ok := err.(*MessageError); !ok {
			if err != test.readErr {
				t.Errorf("BtcDecode #%d wrong error got: %v, "+
					"want: %v", i, err, test.readErr)
				continue
			}
		}

	}
}
