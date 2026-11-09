module

public import Silmaril.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Formats.Compression.Deflate.Decompress

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

open Silmaril.Formats.Compression

/-!
# Stored (uncompressed) DEFLATE streams — RFC 1951 §3.2.4

A stored block carries `LEN` in 16 bits, so it holds at most 65535 bytes. Input
longer than that must be split across several blocks, with `BFINAL` set only on
the last one; `storedBytes` does exactly that. Every block starts on a byte
boundary (`BFINAL`/`BTYPE` are followed by padding to the next byte), so a
stored stream is a plain byte-level encoding and needs no bit juggling.

This encoder does not compress: it is `O(n)` and adds a five-byte header per
65535-byte chunk (five bytes even for empty input). `Deflate.compress` (fixed Huffman, round trip proved in
`Deflate/RoundTrip.lean`) does compress, but its greedy LZ77 match search is
quadratic with a 32 KiB window, so it is not usable on inputs of realistic size.
-/

/-- The largest payload of one stored block (RFC 1951 §3.2.4: `LEN` is 16 bits). -/
def storedMax : Nat := 65535

/-- `LEN` and `NLEN = ~LEN` of a stored block, little-endian (RFC 1951 §3.2.4). -/
def storedLenBytes (len : Nat) : List UInt8 :=
  let nlen := 65535 ^^^ len
  [UInt8.ofNat (len % 256), UInt8.ofNat (len / 256),
   UInt8.ofNat (nlen % 256), UInt8.ofNat (nlen / 256)]

/-- One stored block: the byte `BFINAL ∣ BTYPE=00` padded to a byte boundary,
then `LEN` and `NLEN`, then the raw bytes. `chunk` must be at most `storedMax`
bytes long. -/
def storedBlockBytes (final : Bool) (chunk : List UInt8) : List UInt8 :=
  (if final then 1 else 0) :: (storedLenBytes chunk.length ++ chunk)

/-- `data` as a sequence of stored blocks of at most `storedMax` bytes each, with
`BFINAL` set on the last one. Empty input gives one empty final block. -/
def storedBytes (data : List UInt8) : List UInt8 :=
  if _hle : data.length ≤ storedMax then storedBlockBytes true data
  else storedBlockBytes false (data.take storedMax) ++ storedBytes (data.drop storedMax)
termination_by data.length
decreasing_by
  simp only [List.length_drop, storedMax] at _hle ⊢
  omega

/-- Store-only DEFLATE compression. Valid for inputs of any size, unlike a single
stored block. -/
def compressStored (data : ByteArray) : ByteArray :=
  ⟨(storedBytes data.data.toList).toArray⟩

/-- Decode the DEFLATE stream at the front of `bs`, returning the decoded bytes
and the bytes that follow the block with `BFINAL` set. DEFLATE blocks are
bit-packed, but a stream always ends on a byte boundary from the point of view of
its container (gzip and zlib both resume at the next byte), so the remainder is a
byte list: the reader's unread input. -/
def deflateTake (bs : List UInt8) : Except DecompressError (List UInt8 × List UInt8) :=
  let r : LSBReader := { buffer := 0, count := 0, input := bs, totalRead := 0 }
  match decompressBlocks (r.bitsLeft + 1) r [] with
  | .error e => .error e
  | .ok (out, r') => .ok (out, r'.input)

/-- `deflateTake` with the output accumulated in an `Array`.

`decompressBlocks` appends to a `List UInt8`, so every decoded byte costs a copy
of everything decoded so far, and expanding a back-reference is quadratic in the
output length.  `decompressBlock` already avoids that through
`decompressBlock_eq_decompressBlockFast`, but `deflateTake` calls
`decompressBlocks` directly — it needs the reader's leftover input, which
`decompressBlock` discards — so the `@[csimp]` replacement did not reach it, and
the containers that use `deflateTake` (gzip and zlib) kept the slow path.

Measured on zlib's 422-byte encoding of 200 000 repetitive bytes:
`Deflate.decompress` takes 92 ms, `zlibDecompress` took **98.8 s**. -/
def deflateTakeFast (bs : List UInt8) : Except DecompressError (List UInt8 × List UInt8) :=
  let r : LSBReader := { buffer := 0, count := 0, input := bs, totalRead := 0 }
  match decompressBlocksArr (r.bitsLeft + 1) r #[] with
  | .error e => .error e
  | .ok (out, r') => .ok (out.toList, r'.input)

@[csimp] theorem deflateTake_eq_deflateTakeFast : @deflateTake = @deflateTakeFast := by
  funext bs
  rw [deflateTake, deflateTakeFast]
  dsimp only
  have h := decompressBlocksArr_eq
    (({ buffer := 0, count := 0, input := bs, totalRead := 0 } : LSBReader).bitsLeft + 1)
    ({ buffer := 0, count := 0, input := bs, totalRead := 0 } : LSBReader) #[]
  rw [← h]
  generalize decompressBlocksArr
    (({ buffer := 0, count := 0, input := bs, totalRead := 0 } : LSBReader).bitsLeft + 1)
    ({ buffer := 0, count := 0, input := bs, totalRead := 0 } : LSBReader) #[] = x
  cases x with
  | error e => rfl
  | ok pr => rfl

/-! ### The decoder only consumes a prefix

Every reader step leaves the unread input a suffix of what it started with, so
whatever `deflateTake` hands back really is the tail of the stream it was given.
This is what makes a trailer check meaningful: the bytes compared against the
checksum are bytes of the stream. -/

/-- The reader a decoding step leaves behind. -/
def stepReader : SymbolStep → LSBReader
  | .done _ r => r
  | .more _ r => r

end Silmaril.Formats.Compression.Deflate
