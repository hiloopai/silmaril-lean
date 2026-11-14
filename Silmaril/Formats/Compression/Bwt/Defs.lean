module

public import Init

/-!
# Building blocks for bzip2-style compression

Three reversible transforms that bzip2 chains before its Huffman stage, as total
list functions with exact inverses. The inverses are proved in
`Silmaril.Formats.Compression.Bwt.Thms`.

* **Burrows–Wheeler transform** (M. Burrows and D. J. Wheeler, *A block-sorting
  lossless data compression algorithm*, SRC Research Report 124, Digital Systems
  Research Center, 1994). `bwt s` sorts the rotations of `s` lexicographically
  (`sortedRotations`) and returns the last column of the sorted matrix with the
  index of a row equal to `s`. `ibwt` inverts it with the *LF mapping*:
  `succTable` stably sorts the positions of the last column by their symbol, and
  row `i` of the matrix is followed by row `(succTable L).getD i 0`, its rotation by one
  to the left (`Thms.getD_sortedRotations_succTable`).
* **Move-to-front** over bytes (`mtfEncode`, `mtfDecode`): each byte is replaced
  by its index in a recency list that starts as `0, 1, …, 255`.
* **Zero-run coding** (`zrleEncode`, `zrleDecode`): bzip2's RUNA/RUNB stage. A run
  of `r ≥ 1` zeros in the move-to-front output is written as the digits of `r` in
  bijective base 2, least significant first (`RUNA = 0` has weight `2^i`,
  `RUNB = 1` weight `2^(i+1)`); every other symbol `v ≥ 1` is shifted to `v + 1`.

## This is not bzip2

These are the transforms only, specified on lists. There is no block format,
no Huffman stage, no CRC and no stream container, so no `Decoder` in the sense of
`Silmaril.Formats.Compression.Defs` is defined here. The steps that remain for a
bzip2 decoder (as specified by the reference implementation, bzip2 1.0.8):

1. the stream container: the `BZh1`–`BZh9` header, block magic
   `0x314159265359` and end-of-stream magic `0x177245385090`, read MSB-first from
   a bit stream, and the combined stream CRC; concatenated streams are
   `Decoder.members`;
2. the block header: block CRC (bzip2's CRC-32, MSB-first, a new `Checksum`), the
   randomised bit, the 24-bit original pointer (`(bwt s).2`);
3. the symbol map (bytes in use, a 16 × 16 bitmap), and the alphabet: `RUNA`,
   `RUNB`, the shifted move-to-front values, `EOB`;
4. the Huffman stage: 2–6 tables with delta-coded code lengths, selectors in
   groups of 50 symbols, the selectors themselves move-to-front coded;
5. the inverse of the composition `zrleDecode`, `mtfDecode` on the symbol map,
   `ibwt` (here given), and the initial run-length stage RLE1 (runs of 4–255
   equal bytes written as four bytes and a count), not given here;
6. the block CRC check, and an encoder if wanted (the transforms here are
   already total and invertible).

The transforms are specifications: `bwt` sorts all rotations with an insertion
sort, quadratic in the block length; bzip2 uses suffix sorting.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Bwt

/-! ## Sorting -/

/-- Insert `a` before the first element `b` with `le a b`. -/
def insertSorted {β : Type} (le : β → β → Bool) (a : β) : List β → List β
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: insertSorted le a l

/-- Insertion sort. Structurally recursive, so small instances evaluate by `decide`. -/
def insertionSort {β : Type} (le : β → β → Bool) : List β → List β
  | [] => []
  | a :: l => insertSorted le a (insertionSort le l)

/-! ## Burrows–Wheeler transform -/

/-- Rotate left by one: the next rotation. -/
def rotl {α : Type} : List α → List α
  | [] => []
  | a :: l => l ++ [a]

section Bwt

variable {α : Type} [LT α] [DecidableEq α] [DecidableLT α] [Inhabited α]

/-- The rotation of `s` that starts at position `k` (for `k ≤ s.length`). -/
def rotation (s : List α) (k : Nat) : List α := s.drop k ++ s.take k

/-- The `s.length` rotations of `s`, starting at positions `0, 1, …`. -/
def rotations (s : List α) : List (List α) := (List.range s.length).map (rotation s)

/-- The Burrows–Wheeler matrix: the rotations of `s` in lexicographic order. Equal
rotations (when `s` is periodic) are equal rows, so the order of ties is
irrelevant. -/
def sortedRotations (s : List α) : List (List α) :=
  insertionSort (fun a b => decide (a ≤ b)) (rotations s)

/-- The last symbol of a row (`default` for the empty row, which never occurs). -/
def lastD (r : List α) : α := r.getLast?.getD default

/-- The **Burrows–Wheeler transform**: the last column of the sorted rotation matrix,
and the index of the first row equal to `s` (`0` for the empty string). -/
def bwt (s : List α) : List α × Nat :=
  let m := sortedRotations s
  (m.map lastD, m.findIdx fun r => decide (r = s))

/-- Order of last-column positions: by symbol, then by position. Sorting by it is a
stable sort of the positions by their symbol. -/
def lastColumnLe (L : List α) (i j : Nat) : Bool :=
  decide (L.getD i default < L.getD j default) ||
    (decide (L.getD i default = L.getD j default) && decide (i ≤ j))

/-- The LF table, read forwards: entry `i` is the position in `L` of the `i`-th
symbol of the first column (the first column is the stably sorted last column).
Row `i` of the matrix rotated left by one is row `(succTable L).getD i 0`. -/
def succTable (L : List α) : List Nat :=
  insertionSort (lastColumnLe L) (List.range L.length)

/-- Walk the matrix from row `i` for `fuel` steps, emitting the last symbol of each
row reached. -/
def ibwtWalk (L : List α) (T : List Nat) : Nat → Nat → List α
  | _, 0 => []
  | i, fuel + 1 =>
    let j := T.getD i 0
    L.getD j default :: ibwtWalk L T j fuel

/-- The **inverse Burrows–Wheeler transform**: from row `idx` (the original string),
following the LF table visits the rotations by `1, 2, …, n` positions, whose last
symbols are the string. -/
def ibwt (p : List α × Nat) : List α :=
  ibwtWalk p.1 (succTable p.1) p.2 p.1.length

end Bwt

/-! ## Move-to-front -/

/-- The initial recency list `0, 1, …, 255`. -/
def mtfInit : List UInt8 := (List.range 256).map Nat.toUInt8

/-- Move-to-front encoding against the recency list `tbl`: emit the index of each
byte, then move it to the front. -/
def mtfEncodeWith : List UInt8 → List UInt8 → List Nat
  | _, [] => []
  | tbl, b :: s => tbl.idxOf b :: mtfEncodeWith (b :: tbl.erase b) s

/-- Move-to-front decoding against `tbl`: emit the byte at each index, then move it
to the front. Out-of-range indices read `0`. -/
def mtfDecodeWith : List UInt8 → List Nat → List UInt8
  | _, [] => []
  | tbl, i :: is =>
    let b := tbl.getD i 0
    b :: mtfDecodeWith (b :: tbl.eraseIdx i) is

/-- **Move-to-front** encoding over bytes, from the recency list `0, 1, …, 255`. -/
def mtfEncode (s : List UInt8) : List Nat := mtfEncodeWith mtfInit s

/-- Move-to-front decoding over bytes. -/
def mtfDecode (is : List Nat) : List UInt8 := mtfDecodeWith mtfInit is

/-! ## Zero-run coding (RUNA/RUNB) -/

/-- `RUNA`, the run digit of weight `2^i` at position `i`. -/
abbrev runA : Nat := 0

/-- `RUNB`, the run digit of weight `2^(i+1)` at position `i`. -/
abbrev runB : Nat := 1

/-- The value of a list of run digits, least significant first: digit `d` at
position `i` has weight `(d + 1) * 2^i`. -/
def runValue : List Nat → Nat
  | [] => 0
  | d :: ds => (d + 1) + 2 * runValue ds

/-- Bijective base-2 digits of `r`, least significant first, with `fuel ≥ r` steps. -/
def runDigitsAux : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, r =>
    if r = 0 then []
    else if r % 2 = 1 then runA :: runDigitsAux fuel (r / 2)
    else runB :: runDigitsAux fuel (r / 2 - 1)

/-- The RUNA/RUNB digits of a run of `r` zeros (empty for `r = 0`). -/
def runDigits (r : Nat) : List Nat := runDigitsAux r r

/-- Zero-run encoding with `z` zeros pending. -/
def zrleEncodeAux : Nat → List Nat → List Nat
  | z, [] => runDigits z
  | z, 0 :: l => zrleEncodeAux (z + 1) l
  | z, (v + 1) :: l => runDigits z ++ (v + 2) :: zrleEncodeAux 0 l

/-- **Zero-run encoding** of move-to-front output: each maximal run of zeros becomes
its RUNA/RUNB digits, each `v ≥ 1` becomes `v + 1`. -/
def zrleEncode (l : List Nat) : List Nat := zrleEncodeAux 0 l

/-- Zero-run decoding with the run digits `ds` pending. -/
def zrleDecodeAux : List Nat → List Nat → List Nat
  | ds, [] => List.replicate (runValue ds) 0
  | ds, d :: l =>
    if d ≤ runB then zrleDecodeAux (ds ++ [d]) l
    else List.replicate (runValue ds) 0 ++ (d - 1) :: zrleDecodeAux [] l

/-- Zero-run decoding. -/
def zrleDecode (l : List Nat) : List Nat := zrleDecodeAux [] l

end Silmaril.Formats.Compression.Bwt
