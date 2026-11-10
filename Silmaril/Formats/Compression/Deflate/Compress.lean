module

public import Silmaril.Formats.Compression.Deflate.Decompress

/-!
# DEFLATE compression (RFC 1951)

`compress` emits a single final fixed-Huffman block.  The LZ77 matcher uses hash
chains over an `Array UInt8` with a bounded chain length; `Deflate.LZ77` proves
that the tokens it emits are valid and expand back to the input, *whatever the
chains contain*, because every emitted length is recomputed by `matchLen`.

`writeStoredBlock` writes stored blocks (BTYPE 00) and is what `Zlib` and `Gzip`
use.  It splits at 65535 bytes, the largest payload a single stored block can
carry; `writeStoredBlock_sound` (`Deflate.RoundTrip`) proves it round-trips for
inputs of any size.

Dynamic-Huffman *encoding* is not implemented: `decompress` accepts BTYPE 10 but
`compress` never produces it.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

open Silmaril.Formats.Compression

inductive Token where
  | literal (b : UInt8)
  | lenDist (len dist : Nat)
  | eob
deriving Repr, Inhabited

/-! ### Greedy LZ77 with hash chains

The matcher works on an `Array UInt8` so that every byte access is O(1), and it
only considers the positions on one hash chain, bounded by `chainLimit`.  None
of the chain machinery is trusted: it supplies a *candidate distance* only, and
the match length is always recomputed by `matchLen`, which is the single source
of truth for `lz77Go_spec`.  A chain full of garbage would cost compression
ratio, never correctness.
-/

/-- Length of the common run of `data` starting at `src` and at `pos`, counting
from `i` and capped at `maxLen`. The runs may overlap (`src < pos`). -/
def matchLen (data : Array UInt8) (src pos maxLen : Nat) (i : Nat) : Nat :=
  if i < maxLen then
    if data.getD (src + i) 0 = data.getD (pos + i) 0 then matchLen data src pos maxLen (i + 1)
    else i
  else maxLen
termination_by maxLen - i

/-- Number of hash buckets (a power of two). -/
def hashSize : Nat := 32768

/-- How many chain links to follow before giving up on a position. -/
def chainLimit : Nat := 128

/-- Stop searching a chain once a match this long has been found. -/
def niceLen : Nat := 192

/-- The largest DEFLATE match distance (RFC 1951 §3.2.5). -/
def maxDistance : Nat := 32768

/-- Hash of the three bytes at `pos` (bytes past the end read as 0). -/
def hash3 (data : Array UInt8) (pos : Nat) : Nat :=
  let b0 := (data.getD pos 0).toNat
  let b1 := (data.getD (pos + 1) 0).toNat
  let b2 := (data.getD (pos + 2) 0).toNat
  ((b0 <<< 10) ^^^ (b1 <<< 5) ^^^ b2) % hashSize

/-- Record position `pos` in the hash chains.  `head[h]` and `prev[p]` store a
position *plus one*, so that 0 means "end of chain". -/
def insertHash (data : Array UInt8) (head prev : Array Nat) (pos : Nat) :
    Array Nat × Array Nat :=
  if pos + 2 < data.size then
    let h := hash3 data pos
    let old := head.getD h 0
    (head.setIfInBounds h (pos + 1), prev.setIfInBounds pos old)
  else (head, prev)

/-- Record `k` consecutive positions starting at `pos`. -/
def insertHashRun (data : Array UInt8) (head prev : Array Nat) (pos : Nat) :
    Nat → Array Nat × Array Nat
  | 0 => (head, prev)
  | k + 1 =>
    let hp := insertHash data head prev pos
    insertHashRun data hp.1 hp.2 (pos + 1) k

/-- Follow the hash chain starting at `cur` (a position plus one), keeping the
longest match found.  Returns `(length, distance)`. -/
def chainSearch (data : Array UInt8) (prev : Array Nat) (pos maxLen : Nat) :
    Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, bestLen, bestDist => (bestLen, bestDist)
  | fuel + 1, cur, bestLen, bestDist =>
    if cur = 0 then (bestLen, bestDist)
    else
      let p := cur - 1
      if pos ≤ p ∨ maxDistance < pos - p then (bestLen, bestDist)
      else if 0 < bestLen ∧ data.getD (p + bestLen) 0 ≠ data.getD (pos + bestLen) 0 then
        -- Cheap rejection: a longer match must differ from the current best at
        -- index `bestLen`.
        chainSearch data prev pos maxLen fuel (prev.getD p 0) bestLen bestDist
      else
        let ml := matchLen data p pos maxLen 0
        if bestLen < ml then
          if niceLen ≤ ml ∨ maxLen ≤ ml then (ml, pos - p)
          else chainSearch data prev pos maxLen fuel (prev.getD p 0) ml (pos - p)
        else chainSearch data prev pos maxLen fuel (prev.getD p 0) bestLen bestDist

/-- The candidate distance for a match at `pos`, or 0 when there is none. -/
def bestDistAt (data : Array UInt8) (head prev : Array Nat) (pos maxLen : Nat) : Nat :=
  if pos + 2 < data.size then
    (chainSearch data prev pos maxLen chainLimit (head.getD (hash3 data pos) 0) 0 0).2
  else 0

/-- The best match at `pos` as `(length, distance)`.  The distance is whatever
the hash chains propose; the length is computed by `matchLen`, and is 0 unless
the distance is a legal DEFLATE back-reference. -/
def bestMatchAt (data : Array UInt8) (head prev : Array Nat) (pos maxLen : Nat) : Nat × Nat :=
  let d := bestDistAt data head prev pos maxLen
  if 1 ≤ d ∧ d ≤ min pos maxDistance then (matchLen data (pos - d) pos maxLen 0, d)
  else (0, 0)

/-- Greedy LZ77 tokens for `data` from position `pos` on, using the hash chains
`head` / `prev`.  The candidate distance comes from the chains; the length is
recomputed by `matchLen`, so only lengths that really match are emitted. -/
def lz77Go (data : Array UInt8) (head prev : Array Nat) (pos : Nat) : List Token :=
  if _hp : pos < data.size then
    match hm : bestMatchAt data head prev pos (min (data.size - pos) 258) with
    | (len, d) =>
      if h : 3 ≤ len then
        let hp2 := insertHashRun data head prev pos len
        .lenDist len d :: lz77Go data hp2.1 hp2.2 (pos + len)
      else
        let hp2 := insertHash data head prev pos
        .literal (data.getD pos 0) :: lz77Go data hp2.1 hp2.2 (pos + 1)
  else []
termination_by data.size - pos
decreasing_by
  · omega
  · omega

/-- Greedy LZ77: produce tokens from input bytes, ending with end-of-block. -/
def lz77Greedy (data : Array UInt8) : List Token :=
  lz77Go data (Array.replicate hashSize 0) (Array.replicate data.size 0) 0 ++ [.eob]

/-! ### Fixed-Huffman block writer -/

/-- The largest payload of a single stored block: RFC 1951 §3.2.4 gives LEN 16
bits, so one block carries at most 65535 bytes. -/
abbrev maxStoredLen : Nat := 65535

/-- Write one stored block (BTYPE 00): BFINAL, BTYPE, pad to a byte boundary,
then LEN, its one's complement NLEN, and the raw bytes.  `data.length` must be
at most `maxStoredLen`; `writeStoredGo` is what enforces that. -/
def writeStoredChunk (w : LSBWriter) (final : Bool) (data : List UInt8) : LSBWriter :=
  let w := w.writeBit final
  let w := w.writeVal 0 2
  let w := w.alignToByte
  let len := data.length
  -- `maxStoredLen ^^^ len` is the one's complement of `len` in 16 bits, i.e.
  -- `maxStoredLen - len` for `len ≤ maxStoredLen`, written so that the decoder's
  -- `(len ^^^ nlen) % 65536 = 65535` check is an xor identity.
  let nlen := maxStoredLen ^^^ len
  let w := w.writeVal len 16
  let w := w.writeVal nlen 16
  data.foldl (λ (w' : LSBWriter) (b : UInt8) => w'.writeByte b) w

/-- Write `data` as a sequence of stored blocks of at most `maxStoredLen` bytes
each, with BFINAL set on the last one. -/
def writeStoredGo (w : LSBWriter) (data : List UInt8) : LSBWriter :=
  if _h : data.length ≤ maxStoredLen then writeStoredChunk w true data
  else
    writeStoredGo (writeStoredChunk w false (data.take maxStoredLen)) (data.drop maxStoredLen)
termination_by data.length
decreasing_by simp only [List.length_drop, maxStoredLen] at _h ⊢; omega

/-- Write `data` as stored DEFLATE blocks.  Unlike the previous version this
splits at 65535 bytes: a single block cannot carry more, and writing `LEN`
modulo 65536 produced a stream that `decompress` rejects (or, at exactly
65535 mod 65536 bytes, silently truncates). -/
def writeStoredBlock (data : ByteArray) : LSBWriter :=
  writeStoredGo LSBWriter.empty data.toList

/-- The largest index `i ≤ bound`, searching upwards from `idx`, such that
`bases[i] ≤ x` (assuming `bases` is increasing). -/
def findCode (bases : List Nat) (x bound idx : Nat) : Nat :=
  if idx < bound then
    if bases.getD (idx + 1) 0 ≤ x then findCode bases x bound (idx + 1)
    else idx
  else bound
termination_by bound - idx

/-- The length symbol (257–285) for a match length. -/
def findLenCode (len : Nat) : Nat := 257 + findCode lengthBase len 28 0

/-- The distance symbol (0–29) for a match distance. -/
def findDistCode (d : Nat) : Nat := findCode distanceBase d 29 0

/-- Write one token. -/
def writeToken (litLen dist : HuffmanTable) (w : LSBWriter) : Token → Option LSBWriter
  | .eob => litLen.writeSymbolLSB w 256
  | .literal b => litLen.writeSymbolLSB w b.toNat
  | .lenDist len d =>
    let lenCode := findLenCode len
    match litLen.writeSymbolLSB w lenCode with
    | none => none
    | some w1 =>
      let w1 := w1.writeVal (len - lengthBase.getD (lenCode - 257) 3)
        (lengthExtraBits.getD (lenCode - 257) 0)
      let distCode := findDistCode d
      match dist.writeSymbolLSB w1 distCode with
      | none => none
      | some w2 =>
        some (w2.writeVal (d - distanceBase.getD distCode 1) (distanceExtraBits.getD distCode 0))

/-- Write a list of tokens. -/
def encodeTokens (litLen dist : HuffmanTable) (w : LSBWriter) : List Token → Option LSBWriter
  | [] => some w
  | t :: rest =>
    match writeToken litLen dist w t with
    | none => none
    | some w' => encodeTokens litLen dist w' rest

/-- Write a final fixed-Huffman block (BFINAL = 1, BTYPE = 01). -/
def writeFixedHuffmanBlock (tokens : List Token) (litLen dist : HuffmanTable) :
    Option LSBWriter :=
  encodeTokens litLen dist ((LSBWriter.empty.writeBit true).writeVal 1 2) tokens

/-- Compress a ByteArray into a single final fixed-Huffman DEFLATE block
(RFC 1951 §3.2.6).  Dynamic-Huffman *encoding* is not implemented; the decoder
accepts all three block types. -/
def compress (data : ByteArray) : Option ByteArray :=
  match fixedLitLenTable, fixedDistTable with
  | some litLen, some dist =>
    match writeFixedHuffmanBlock (lz77Greedy data.data) litLen dist with
    | some w => some w.toByteArray
    | none => none
  | _, _ => none

end Silmaril.Formats.Compression.Deflate
