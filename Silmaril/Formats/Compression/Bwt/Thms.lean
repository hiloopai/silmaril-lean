module

public import Silmaril.Formats.Compression.Bwt.Defs
import Silmaril.Proofs.Formats.Compression.Bwt

/-!
# Building blocks for bzip2-style compression: facts

Proved (standard axioms), for any linearly ordered alphabet `α` (bytes in the
examples):

* `ibwt_bwt`: the inverse Burrows–Wheeler transform recovers the input, for every
  string, including periodic ones (`aaaa`, `abab`), whose matrix has equal rows;
* `bwt_fst_perm`, `bwt_fst_length`, `bwt_snd_lt`: the last column is a permutation
  of the input, and the index is a row of the matrix equal to the input;
* `getD_sortedRotations_succTable`: the LF mapping. Row `i` of the sorted rotation
  matrix, rotated left by one, is the row `(succTable L).getD i 0`, where `L` is the
  last column;
* `mtfDecode_mtfEncode`, `mtfEncode_lt`: move-to-front round trip, symbols `< 256`;
* `zrleDecode_zrleEncode`, `runValue_runDigits`: RUNA/RUNB zero-run round trip.

The proof of `ibwt_bwt` (in `Silmaril.Proofs.Formats.Compression.Bwt`):

1. `rotr_le_rotr`: if rows `i`, `j` of the matrix have last symbols `c < d`, or
   `c = d` and `i ≤ j`, then their right rotations by one compare the same way,
   since `c :: x` and `d :: y` compare by `c`, `d` first, and when `c = d`, rows
   `x ++ [c] ≤ y ++ [c]` of equal length give `x ≤ y`.
2. `map_succTable`: so the rows, taken in `succTable` order and rotated right, form
   a sorted list. It is a permutation of the right rotations of all rotations, which
   are the rotations again. Two sorted permutations of each other are equal (the
   order on rows is antisymmetric): rotating right row `succTable[i]` gives row `i`.
   Only rows as strings are compared, so equal rows of a periodic string need no
   tie-breaking convention.
3. `getD_sortedRotations_succTable`: rotating left, row `succTable[i]` is row `i`
   rotated left by one.
4. `ibwtWalk_eq`: starting from a row equal to `s` (the index), the walk visits the
   rotations by `1, 2, …, n` positions; the last symbol of the rotation by `j + 1`
   is `s[j]`.

Checked by `decide`: the classic examples `bwt "banana" = ("nnbaaa", 3)` and
`bwt "abracadabra" = ("rdarcaaaabb", 2)` with their inverses, the move-to-front
code of `"banana"` and of its transform, and RUNA/RUNB codes of small runs.

This is not bzip2: see the plan in `Silmaril.Formats.Compression.Bwt.Defs`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Bwt

/-! ## Burrows–Wheeler transform -/

section Bwt

variable {α : Type} [LT α] [LE α] [DecidableEq α] [DecidableLT α] [Inhabited α]
  [Std.IsLinearOrder α] [Std.LawfulOrderLT α]

/-- **The inverse Burrows–Wheeler transform recovers the input.** -/
theorem ibwt_bwt (s : List α) : ibwt (bwt s) = s :=
  Proofs.Formats.Compression.Bwt.ibwt_bwt s

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
/-- The last column is a permutation of the input. -/
theorem bwt_fst_perm (s : List α) : (bwt s).1.Perm s :=
  Proofs.Formats.Compression.Bwt.bwt_fst_perm s

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
theorem bwt_fst_length (s : List α) : (bwt s).1.length = s.length :=
  Proofs.Formats.Compression.Bwt.bwt_fst_length s

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
/-- The index is a row of the matrix, and that row is the input. -/
theorem bwt_snd_lt {s : List α} (h : 0 < s.length) :
    (bwt s).2 < s.length ∧ (sortedRotations s).getD (bwt s).2 [] = s :=
  Proofs.Formats.Compression.Bwt.bwt_snd_spec h

omit [Inhabited α] in
/-- The matrix is sorted. -/
theorem sortedRotations_pairwise (s : List α) : (sortedRotations s).Pairwise (· ≤ ·) :=
  Proofs.Formats.Compression.Bwt.sortedRotations_pairwise s

omit [LT α] [LE α] [DecidableEq α] [DecidableLT α] [Inhabited α] [Std.IsLinearOrder α]
  [Std.LawfulOrderLT α] in
/-- The rows of the matrix are the rotations of the input. -/
theorem sortedRotations_perm [LT α] [DecidableEq α] [DecidableLT α] (s : List α) :
    (sortedRotations s).Perm (rotations s) :=
  Proofs.Formats.Compression.Bwt.sortedRotations_perm s

/-- **The LF mapping**: following the LF table from row `i` of the matrix reaches
row `i` rotated left by one. -/
theorem getD_sortedRotations_succTable {s : List α} {i : Nat} (hi : i < s.length) :
    (sortedRotations s).getD ((succTable ((sortedRotations s).map lastD)).getD i 0) [] =
      rotl ((sortedRotations s).getD i []) :=
  Proofs.Formats.Compression.Bwt.getD_sortedRotations_succTable hi

end Bwt

/-! ## Move-to-front -/

/-- Move-to-front decoding inverts move-to-front encoding. -/
theorem mtfDecode_mtfEncode (s : List UInt8) : mtfDecode (mtfEncode s) = s :=
  Proofs.Formats.Compression.Bwt.mtfDecodeWith_mtfEncodeWith s mtfInit
    Proofs.Formats.Compression.Bwt.mem_mtfInit

/-- Move-to-front symbols are below `256`. -/
theorem mtfEncode_lt (s : List UInt8) : ∀ i ∈ mtfEncode s, i < 256 :=
  Proofs.Formats.Compression.Bwt.length_mtfInit ▸
    Proofs.Formats.Compression.Bwt.mtfEncodeWith_lt s mtfInit
      Proofs.Formats.Compression.Bwt.mem_mtfInit

/-! ## Zero-run coding -/

/-- The RUNA/RUNB digits of `r` have value `r`. -/
theorem runValue_runDigits (r : Nat) : runValue (runDigits r) = r :=
  Proofs.Formats.Compression.Bwt.runValue_runDigits r

/-- Zero-run decoding inverts zero-run encoding. -/
theorem zrleDecode_zrleEncode (l : List Nat) : zrleDecode (zrleEncode l) = l :=
  Proofs.Formats.Compression.Bwt.zrleDecode_zrleEncodeAux 0 l

/-! ## Known answers -/

/-- `"banana"` transforms to `"nnbaaa"` with the input at row 3 (Burrows and Wheeler's
running example is `"abraca"`; `"banana"` is the textbook one). -/
theorem bwt_banana :
    bwt ([0x62, 0x61, 0x6E, 0x61, 0x6E, 0x61] : List UInt8) =
      ([0x6E, 0x6E, 0x62, 0x61, 0x61, 0x61], 3) := by decide

theorem ibwt_banana :
    ibwt (([0x6E, 0x6E, 0x62, 0x61, 0x61, 0x61], 3) : List UInt8 × Nat) =
      [0x62, 0x61, 0x6E, 0x61, 0x6E, 0x61] := by decide

/-- `"abracadabra"` transforms to `"rdarcaaaabb"` with the input at row 2. -/
theorem bwt_abracadabra :
    bwt ([0x61, 0x62, 0x72, 0x61, 0x63, 0x61, 0x64, 0x61, 0x62, 0x72, 0x61] : List UInt8) =
      ([0x72, 0x64, 0x61, 0x72, 0x63, 0x61, 0x61, 0x61, 0x61, 0x62, 0x62], 2) := by decide

theorem ibwt_abracadabra :
    ibwt (([0x72, 0x64, 0x61, 0x72, 0x63, 0x61, 0x61, 0x61, 0x61, 0x62, 0x62], 2) :
        List UInt8 × Nat) =
      [0x61, 0x62, 0x72, 0x61, 0x63, 0x61, 0x64, 0x61, 0x62, 0x72, 0x61] := by decide

set_option maxRecDepth 8000 in
/-- Move-to-front of `"banana"`. -/
theorem mtfEncode_banana :
    mtfEncode [0x62, 0x61, 0x6E, 0x61, 0x6E, 0x61] = [98, 98, 110, 1, 1, 1] := by decide

set_option maxRecDepth 8000 in
/-- Move-to-front of `"nnbaaa"`, the transform of `"banana"`: runs become zeros. -/
theorem mtfEncode_nnbaaa :
    mtfEncode [0x6E, 0x6E, 0x62, 0x61, 0x61, 0x61] = [110, 0, 99, 99, 0, 0] := by decide

/-- Runs of 1–4 zeros: `RUNA`, `RUNB`, `RUNA RUNA`, `RUNB RUNA`; `v ≥ 1` becomes `v + 1`. -/
theorem zrleEncode_example :
    zrleEncode [0, 3, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 0] = [0, 4, 1, 6, 0, 0, 2, 1, 0] := by decide

end Silmaril.Formats.Compression.Bwt
