module

public import Silmaril.Wasm.Auto2.VCGen.Defs
public import Silmaril.WasmSpec.InsertionSort.Thms

/-!
# Insertion sort through the VC generator (two-memory predicates)

The Wasm specification library's
`insertion_sort` (`Silmaril.WasmSpec.InsertionSort.sortFunc`) against an annotated specification of
the VC generator whose postcondition and invariants relate the current memory to the memory at entry
(`Fm.pr2`, `Fns.pr2`):

* precondition (`pr 0`): the segment `[p, p + 4 n)` is in memory and does not wrap;
* postcondition (`pr2 0 cur (v 0)`): `Sorts` of the specification library (equal outside the
  segment, the segment's words sorted and a permutation of the original ones);
* outer invariant (`pr2 1`): `1 ≤ i ≤ n + 1`, equal outside, a permutation, the prefix of length
  `i` sorted; variant `n - i`;
* inner invariant (`pr2 2`): some array `ys` (the words at the start of the outer iteration) is a
  permutation of the input with a sorted prefix of length `i`, `ys[i] = key`, the words are
  `hole ys i j` and the shifted elements are above `key` (`IFacts` of the hand proof); variant `j`.

The conditions are proved in `Silmaril.Proofs.Wasm.Auto2.VCSort.Conds`, the specification in
`Silmaril.Wasm.Auto2.VCSort.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCSort

open Silmaril.Wasm
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.InsertionSort (Sorts hole)

/-- The precondition: the segment is in memory and does not wrap. -/
def PreS (B : ByteArray) (p n : BitVec 32) : Prop :=
  p.toNat + 4 * n.toNat ≤ B.size ∧ p.toNat + 4 * n.toNat < 2 ^ 32

/-- The outer invariant. -/
def OutS (B B' : ByteArray) (p n i : BitVec 32) : Prop :=
  1 ≤ i.toNat ∧ i.toNat ≤ n.toNat + 1 ∧ SameOutside B B' p.toNat (4 * n.toNat) ∧
    (words B' p.toNat n.toNat).Perm (words B p.toNat n.toNat) ∧
    SortedS ((words B' p.toNat n.toNat).take i.toNat)

/-- The inner invariant. -/
def InS (B B' : ByteArray) (p n i j key : BitVec 32) : Prop :=
  ∃ ys : List (BitVec 32), ys.length = n.toNat ∧ ys.Perm (words B p.toNat n.toNat) ∧
    SortedS (ys.take i.toNat) ∧ 1 ≤ i.toNat ∧ i.toNat < n.toNat ∧ ys.getD i.toNat 0 = key ∧
    j.toNat ≤ i.toNat ∧ SameOutside B B' p.toNat (4 * n.toNat) ∧
    words B' p.toNat n.toNat = hole ys i.toNat j.toNat ∧
    ∀ x ∈ (ys.take i.toNat).drop j.toNat, key.toInt < x.toInt

/-- The specification functions: `pr 0` the precondition, `pr2 0` the postcondition, `pr2 1` and
`pr2 2` the invariants (first memory: the current one, second: the memory at entry). -/
def sortFns : Fns where
  pr k B as := match k, as with
    | 0, [p, n] => PreS B p n
    | _, _ => True
  pr2 k B' B as := match k, as with
    | 0, [p, n] => Sorts B B' p.toNat n.toNat
    | 1, [p, n, i] => OutS B B' p n i
    | 2, [p, n, i, j, key] => InS B B' p n i j key
    | _, _ => True

/-- Parameter `i` and local `j`. -/
abbrev P32 (i : Nat) : Tm .i32 := .var .i32 i
abbrev L32 (j : Nat) : Tm .i32 := .loc .i32 j

/-- **The annotated specification** of `insertion_sort` (locals: `p, n, i, j, key`). -/
def sortSpecV : FnSpec where
  params := [.i32, .i32]
  results := []
  pre := .pr 0 (.v 0) [P32 0, P32 1]
  post := .pr2 0 .cur (.v 0) [P32 0, P32 1]
  inv := [.pr2 1 .cur (.v 0) [L32 0, L32 1, L32 2],
    .pr2 2 .cur (.v 0) [L32 0, L32 1, L32 2, L32 3, L32 4]]
  mem := true
  var := [.bin .sub (L32 1) (L32 2), L32 3]
  total := true

/-- The fuel. -/
def sortFuel : Nat := 100

end Silmaril.Wasm.Auto2.VCSort
