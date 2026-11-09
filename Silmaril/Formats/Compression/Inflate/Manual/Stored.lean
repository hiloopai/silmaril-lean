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
public import Silmaril.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Formats.Compression.Deflate.StoredWriter
public import Silmaril.Formats.Compression.Deflate.RoundTrip
public import Silmaril.Formats.Compression.Checksum.Adler32Spec
public import Silmaril.Formats.Compression.Zlib.DictionaryHistory
public import Silmaril.Formats.Compression.Vectors

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Deflate (DecompressError)

/-!
# Complete-input mathematical translation of the STORED/COPY path

A candidate abstraction. The header path
independently aligns the reader, reads LEN and NLEN, and checks the source-style
one's-complement equation. COPY uses the existing array-push byte-reading
primitive, whose relation to the format's list accumulator is already proved.
The result theorem preserves the complete reader and all errors, for arbitrary
input readers and stored lengths, not only bytes produced by our encoder.

This is a complete-input abstraction of the algorithm shared by the two pinned
source versions. It is not execution of either C body. In particular, our reader
is the format reader: `alignToByte` discards its current partial-byte buffer. A
source refinement must normalize C's potentially prefetched whole bytes before
using it, and account for the source's single 32-bit lookahead, input/output
suspension, public stream-field updates, pointer ownership and mode transitions.
The mathematical error on incomplete input describes unavailable complete data;
it does not equate zlib's resumable `Z_OK`/`Z_BUF_ERROR` protocol with an error.
-/

/-- The stored header's complement check, without the format decoder's modulo
test. Reads have already bounded both operands to sixteen bits. -/
def readStoredHeader (r : LSBReader) : Except DecompressError (Nat × LSBReader) :=
  let aligned := r.alignToByte
  match aligned.readBits 16 with
  | none => .error .badStoredLen
  | some (len, afterLen) =>
    match afterLen.readBits 16 with
    | none => .error .badStoredLen
    | some (nlen, afterHeader) =>
      if len = nlen ^^^ 65535 then .ok (len, afterHeader)
      else .error .badStoredLen

/-- Independently checked header followed by the shared, verified array copy
primitive. This does not call either stored-block decoder. -/
def decompressStoredArray (r : LSBReader) :
    Except DecompressError (Array UInt8 × LSBReader) :=
  match readStoredHeader r with
  | .error e => .error e
  | .ok (len, afterHeader) => Deflate.readStoredBytesArr #[] afterHeader len

/-- Complete-input STORED/COPY translation, exposing ordinary mathematical
byte lists while retaining the entire residual bit reader. -/
def decompressStored (r : LSBReader) :
    Except DecompressError (List UInt8 × LSBReader) :=
  (decompressStoredArray r).map Deflate.toSpecPair

end Silmaril.Formats.Compression.Inflate.Manual
