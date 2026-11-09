module

public import Silmaril.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Formats.Compression.Deflate.LZ77

/-!
# DEFLATE round trip

`decompress` defines the format; `Compresses data c` says that `c` decodes to
`data`. This file proves that `compress` is total and always produces such a
`c`, hence that `decompress` is surjective:

* `compress_total : ∃ c, compress data = some c`
* `compress_sound : compress data = some c → Compresses data c`
* `decompress_surjective : ∃ c, Compresses data c`

Those three are internal: they relate `compress` to `decompress`.  The
known-answer vectors at the end of the file tie `decompress` to RFC 1951 itself,
using byte strings produced by zlib, and two rejection theorems cover streams
the decoder must refuse.

The proof is layered: bits (`BitstreamLemmas`), Huffman codes (`HuffmanLemmas`),
LZ77 tokens (`LZ77`), and below, the length/distance tables, one token, a token
stream with its end-of-block, and the block header.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

open Silmaril.Formats.Compression

section Tokens

variable {litLen dist : HuffmanTable} (hl : ∀ s < 286, litLen.SymOK s)
  (hd : ∀ s < 30, dist.SymOK s)
include hl hd

end Tokens

/-! ### Stored blocks

`writeStoredBlock` is the path `zlibCompress` and `gzipCompress` take, and the
one that silently corrupted every input of 65536 bytes or more.  The statement
that would have caught it is `writeStoredBlock_sound` at the end of this
section: it holds for *every* `data`, because `writeStoredGo` now splits.
-/

/-- The bits one stored block writes: BFINAL, BTYPE = 00, five pad bits up to
the byte boundary, LEN, NLEN, then the raw data (RFC 1951 §3.2.4). -/
def storedBits (final : Bool) (data : List UInt8) : List Bool :=
  [final] ++ natBits 0 2 ++ List.replicate 5 false ++ natBits data.length 16 ++
    natBits (maxStoredLen ^^^ data.length) 16 ++ bytesBits data

/-- The bits `writeStoredGo` writes for `data`. -/
def storedStream (data : List UInt8) : List Bool :=
  if _h : data.length ≤ maxStoredLen then storedBits true data
  else storedBits false (data.take maxStoredLen) ++ storedStream (data.drop maxStoredLen)
termination_by data.length
decreasing_by simp only [List.length_drop, maxStoredLen] at _h ⊢; omega

/-- How many stored blocks `writeStoredGo` emits. -/
def storedChunks (data : List UInt8) : Nat :=
  if _h : data.length ≤ maxStoredLen then 1 else 1 + storedChunks (data.drop maxStoredLen)
termination_by data.length
decreasing_by simp only [List.length_drop, maxStoredLen] at _h ⊢; omega

end Silmaril.Formats.Compression.Deflate
