module

public import Silmaril.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Formats.Compression.Deflate.Stored
public import Silmaril.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Formats.Compression.Deflate.LZ77
public import Silmaril.Formats.Compression.Bits.ByteFields
public import Silmaril.Formats.Compression.Checksum.Adler32
public import Silmaril.Formats.Compression.Checksum.CRC32
public import Silmaril.Formats.Compression.Zlib.Basic
public import Silmaril.Formats.Compression.Zlib.Take
public import Silmaril.Formats.Compression.Zlib.Dictionary
public import Silmaril.Formats.Compression.Gzip.Basic

/-!
# Token-oriented manual DEFLATE translation

This is a hand-written, complete-input mathematical translation of the symbol
portion of zlib's inflater: `LEN`, `LENEXT`, `DIST`, `DISTEXT`, `LIT`, and `MATCH`.
It deliberately separates parsing a token from applying it to output.  The
parser can therefore be related to a bit-buffer or a Huffman-table implementation
independently of the output/history implementation.

The equalities below cover arbitrary tables, readers, outputs and fuel, including
the specification's errors.  The shared primitives are the existing bit reader,
Huffman symbol reader, RFC tables and overlapping `copyBack` algorithm.  These
are proofs against the repository's format specification; they do not establish
correspondence to C, its streaming API, its lookup tables or its fast path.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual

open Silmaril.Formats.Compression

/-- A literal, end-of-block marker, or length/distance back-reference. -/
inductive Token where
  | literal (byte : UInt8)
  | endBlock
  | matchBytes (length distance : Nat)
  deriving Repr, DecidableEq

/-- Parse a length/distance pair after the literal/length symbol.  Distance
validity against the available history is checked when the token is applied. -/
def parseMatch (dist : HuffmanTable) (symbol : Nat) (r : LSBReader) :
    Except Deflate.DecompressError (Token × LSBReader) :=
  let index := symbol - 257
  let length := Deflate.lengthBase.getD index 3
  let lengthBits := Deflate.lengthExtraBits.getD index 0
  match r.readBits lengthBits with
  | none => .error .decodeOverrun
  | some (lengthExtra, r1) =>
    match dist.readSymbolLSB r1 with
    | none => .error .decodeOverrun
    | some (distanceSymbol, r2) =>
      if 30 ≤ distanceSymbol then .error (.badDistanceCode distanceSymbol)
      else
        let distance := Deflate.distanceBase.getD distanceSymbol 1
        let distanceBits := Deflate.distanceExtraBits.getD distanceSymbol 0
        match r2.readBits distanceBits with
        | none => .error .decodeOverrun
        | some (distanceExtra, r3) =>
          .ok (.matchBytes (length + lengthExtra) (distance + distanceExtra), r3)

/-- Parse exactly one token, consuming the Huffman codes and their extra bits.
Symbols 286 and above and reserved distance symbols are rejected. -/
def parseToken (litLen dist : HuffmanTable) (r : LSBReader) :
    Except Deflate.DecompressError (Token × LSBReader) :=
  match litLen.readSymbolLSB r with
  | none => .error .decodeOverrun
  | some (symbol, r1) =>
    if symbol < 256 then .ok (.literal (UInt8.ofNat symbol), r1)
    else if symbol = 256 then .ok (.endBlock, r1)
    else if symbol ≤ 285 then parseMatch dist symbol r1
    else .error .decodeOverrun

/-- Apply a parsed token.  Back-references use sequential overlapping copying,
so newly emitted bytes can themselves be the source of later copied bytes. -/
def applyToken (output : List UInt8) (token : Token) (r : LSBReader) :
    Except Deflate.DecompressError Deflate.SymbolStep :=
  match token with
  | .literal byte => .ok (.more (output ++ [byte]) r)
  | .endBlock => .ok (.done output r)
  | .matchBytes length distance =>
    if distance > output.length then .error .decodeOverrun
    else .ok (.more (Deflate.copyBack distance output length) r)

/-- One symbol transition factored through an explicit, output-independent
token representation. -/
def decodeStep (litLen dist : HuffmanTable) (r : LSBReader) (output : List UInt8) :
    Except Deflate.DecompressError Deflate.SymbolStep :=
  match parseToken litLen dist r with
  | .error e => .error e
  | .ok (token, r') => applyToken output token r'

/-- Explicit symbol loop.  Fuel counts tokens, including the end marker. -/
def decodeSymbolsFuel (litLen dist : HuffmanTable) :
    Nat → LSBReader → List UInt8 → Except Deflate.DecompressError (List UInt8 × LSBReader)
  | 0, _, _ => .error .decodeOverrun
  | fuel + 1, r, output =>
    match decodeStep litLen dist r output with
    | .error e => .error e
    | .ok (.done bytes r') => .ok (bytes, r')
    | .ok (.more bytes r') => decodeSymbolsFuel litLen dist fuel r' bytes

/-- Decode one Huffman block's tokens, with the same bit-derived fuel bound as
the specification. -/
def decodeSymbol (litLen dist : HuffmanTable) (r : LSBReader)
    (output : List UInt8) : Except Deflate.DecompressError (List UInt8 × LSBReader) :=
  decodeSymbolsFuel litLen dist (r.bitsLeft + 1) r output

end Silmaril.Formats.Compression.Inflate.Manual
