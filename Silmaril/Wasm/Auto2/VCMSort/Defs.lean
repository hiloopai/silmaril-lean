module

public import Silmaril.Wasm.Auto2.VCMerge.Defs

/-!
# The specification library's merge sort through the VC generator (recursion)

`merge_sort(p, n, t)` of
`Silmaril.WasmSpec.MergeSort` sorts `a[0..m)` and `a[m..n)` (`m = n / 2`) by two recursive calls,
then calls `merge` (`Silmaril.Wasm.Auto2.VCMerge`). The generator itself has no recursion; the recursive call
is checked against a **recursive callee contract** `msortSpec'` and the generator's
`genFunc_tsound_rec` closes the recursion by induction on a bound `N` of the length:

* the specification functions `msFns N` are `mergeFns` with `pr 5 [p, n, t]`: the layout
  (`Bounds`) and `n < N`, and `pr 6`: the layout and `n < N + 1`;
* `msortSpec` (precondition `pr 6`) calls `merge` (function `0`, with `mergeSpecV`) and itself
  (function `1`, with `msortSpec'`, precondition `pr 5`); both promise the library's `Sorts`
  (`pr2 0`).

Conditions in `Silmaril.Proofs.Wasm.Auto2.VCMSort.Conds`; the library's `Spec` in
`Silmaril.Wasm.Auto2.VCMSort.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCMSort

open Silmaril.Wasm
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.WasmSpec.MergeSort (Bounds)
open Silmaril.Wasm.Auto2.VCMerge (mergeFns mergeSpecV P32)

/-- The specification functions for the bound `N`. -/
def msFns (N : Nat) : Fns :=
  { mergeFns with
    pr := fun k B as => match k, as with
      | 5, [p, n, t] => Bounds B p n t ∧ n.toNat < N
      | 6, [p, n, t] => Bounds B p n t ∧ n.toNat < N + 1
      | k, as => mergeFns.pr k B as }

/-- **The recursive callee contract** of `merge_sort` (`n < N`). -/
def msortSpec' : FnSpec where
  params := [.i32, .i32, .i32]
  results := []
  pre := .pr 5 (.v 0) [P32 0, P32 1, P32 2]
  post := .pr2 0 .cur (.v 0) [P32 0, P32 1, P32 2]
  mem := true
  total := true

/-- **The annotated specification** of `merge_sort` (`n < N + 1`; locals `p, n, t, m`). -/
def msortSpec : FnSpec :=
  { msortSpec' with
    pre := .pr 6 (.v 0) [P32 0, P32 1, P32 2]
    calls := [(0, mergeSpecV, Silmaril.WasmSpec.MergeSort.mergeFunc),
      (1, msortSpec', Silmaril.WasmSpec.MergeSort.sortFunc)] }

/-- The fuel. -/
def msortFuel : Nat := 100

end Silmaril.Wasm.Auto2.VCMSort
