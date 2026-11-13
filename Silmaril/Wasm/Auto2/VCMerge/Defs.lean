module

public import Silmaril.Wasm.Auto2.VCGen.Defs
public import Silmaril.WasmSpec.MergeSort.Thms

/-!
# `merge` of the specification library's merge sort through the VC generator

The function `merge(p, m, n, t)` of
`Silmaril.WasmSpec.MergeSort` (merge the sorted halves `a[0..m)` and `a[m..n)` into the buffer
`t[0..n)`, then copy the buffer back) against an annotated specification whose user predicates
are the hand proof's facts (`Silmaril.Proofs.WasmSpec.MergeSort.Merge`, reached through the header
`Silmaril.WasmSpec.MergeSort.Thms`):

* precondition `pr 0`: `Bounds` (array and buffer in memory, disjoint, no wrap), `m ≤ n`, both
  halves sorted;
* postcondition `pr2 0 cur (v 0)`: the library's `Sorts` (the array's words are a sorted
  permutation of the input's, and only the array and the buffer changed);
* merge-loop invariant `pr2 1`: the hand proof's `MFacts` (the buffer's prefix is a sorted
  permutation of the elements taken, below the rest); copy-loop invariant `pr2 2` (`CFacts`: the
  buffer is a sorted permutation of the input, the array is the buffer's prefix then the input's
  rest); both variants `n - k`.

Conditions in `Silmaril.Proofs.Wasm.Auto2.VCMerge.Conds`; the library's `MergeSpec` in
`Silmaril.Wasm.Auto2.VCMerge.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCMerge

open Silmaril.Wasm
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.MergeSort (Sorts Bounds MFacts half₁ half₂)

/-- The precondition of `merge`. -/
def PreM (B : ByteArray) (p m n t : BitVec 32) : Prop :=
  Bounds B p n t ∧ m.toNat ≤ n.toNat ∧ SortedS (half₁ B p m) ∧ SortedS (half₂ B p m n)

/-- The copy-loop invariant (`B` the memory at entry, `B'` the current one). -/
def CFacts (B B' : ByteArray) (p n t k : BitVec 32) : Prop :=
  k.toNat ≤ n.toNat ∧ SameOutside2 B B' p.toNat (4 * n.toNat) t.toNat (4 * n.toNat) ∧
    SortedS (words B' t.toNat n.toNat) ∧
    (words B' t.toNat n.toNat).Perm (words B p.toNat n.toNat) ∧
    words B' p.toNat n.toNat =
      (words B' t.toNat n.toNat).take k.toNat ++ (words B p.toNat n.toNat).drop k.toNat

/-- The specification functions: `pr 0` the precondition; `pr2 0` the postcondition, `pr2 1` and
`pr2 2` the invariants (first memory: the current one, second: the memory at entry). -/
def mergeFns : Fns where
  pr k B as := match k, as with
    | 0, [p, m, n, t] => PreM B p m n t
    | _, _ => True
  pr2 k B' B as := match k, as with
    | 0, [p, n, t] => Sorts B B' p.toNat n.toNat t.toNat
    | 1, [p, m, n, t, i, j, k] => MFacts B B' p m n t i j k
    | 2, [p, n, t, k] => CFacts B B' p n t k
    | _, _ => True

/-- Parameter `i` and local `j`. -/
abbrev P32 (i : Nat) : Tm .i32 := .var .i32 i
abbrev L32 (j : Nat) : Tm .i32 := .loc .i32 j

/-- **The annotated specification** of `merge` (locals `p, m, n, t, i, j, k, l`). -/
def mergeSpecV : FnSpec where
  params := [.i32, .i32, .i32, .i32]
  results := []
  pre := .pr 0 (.v 0) [P32 0, P32 1, P32 2, P32 3]
  post := .pr2 0 .cur (.v 0) [P32 0, P32 2, P32 3]
  inv := [.pr2 1 .cur (.v 0) [L32 0, L32 1, L32 2, L32 3, L32 4, L32 5, L32 6],
    .pr2 2 .cur (.v 0) [L32 0, L32 2, L32 3, L32 6]]
  mem := true
  var := [.bin .sub (L32 2) (L32 6), .bin .sub (L32 2) (L32 6)]
  total := true

/-- The fuel. -/
def mergeFuel : Nat := 100

end Silmaril.Wasm.Auto2.VCMerge
