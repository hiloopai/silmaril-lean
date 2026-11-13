module

public import Silmaril.Wasm.Auto2.VCBTree.Defs

/-!
# `btree_search` of the B-tree library through the VC generator

`btree_search(k)` of
`Silmaril.WasmSpec.BTree` descends from the root page: it finds the first key not below `k` with
`oba_find` on the node's keys, returns `1` if that key is `k`, `0` at a leaf, and otherwise
continues at the child pointer read with `oba_get`. Its annotated specification calls two callee
contracts (`FnSpec.calls`):

* `oba_find` (function `1`) with `findSpecV` of `Silmaril.Wasm.Auto2.VCBTree` (`OBA` keys);
* `oba_get` (function `0`) with `getBASpecV`: the array need only be a `BA` (the child pointers are
  not ordered; the library's `getSpec` asks for an `OBA`, so the library's `SearchSpec`, whose
  hypotheses only give `getSpec` for the callee, does not cover the pointer read).

The precondition (`pr 7`) is `IsBTree B t κ` for some `t, κ`; the postcondition (`pr 9`) says for
every `t, κ` with `IsBTree B t κ` that the result is `1` if `κ k` and `0` otherwise; memory is
unchanged. The loop invariant (`pr 8`, `SubTree`) says for every such `t, κ` that page `x`
represents an ordered tree whose bounds contain `k` and which contains `k` iff `κ k` does.

* `searchSpecV`: partial correctness (no variant);
* `searchSpecT`: total correctness, with the ghost variant `mfn 0 (v 0) x 0`: the height of the tree
  page `x` represents in the memory at entry (`hgt`, the least height of such a tree, as a word),
  under the precondition `pr 10` that also bounds the root's height below `2 ^ 32` (an
  assumption: the library's `SearchSpec` has none; it holds for every tree whose pages are
  distinct along each path, but that is not proved here), invariant `pr 11`.

Conditions in `Silmaril.Proofs.Wasm.Auto2.VCBSearch.Conds`; results in
`Silmaril.Wasm.Auto2.VCBSearch.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCBSearch

open Silmaril.Wasm
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.BTree (OBA BA FindsAt Tree Repr Ordered Within InTree IsBTree page)
open Silmaril.Wasm.Auto2.VCBTree (btFns P32 L32 findSpecV)

mutual
/-- The height of a tree. -/
def height : Tree → Nat
  | .node _ _ cs => heightL cs

/-- One more than the greatest height of a list of trees (`0` for none). -/
def heightL : List Tree → Nat
  | [] => 0
  | c :: cs => max (height c + 1) (heightL cs)
end

/-- **Page `x` holds the subtree for key `k`**: for every `t, κ` with `IsBTree B t κ`, page `x`
represents an ordered tree whose bounds contain `k` and which contains `k` iff `κ k`. -/
def SubTree (B : ByteArray) (k x : BitVec 32) : Prop :=
  ∀ t κ, IsBTree B t κ → ∃ (T : Tree) (lo hi : Option (BitVec 32)), Repr B x.toNat T ∧
    Ordered lo hi T ∧ Within lo hi k ∧ (κ k ↔ InTree k T)

open Classical in
/-- **The ghost height** of page `x` in `B`: the least height of a tree it represents (`0` if
none). -/
noncomputable def hgt (B : ByteArray) (x : Nat) : Nat :=
  if h : ∃ T, Repr B x T then Nat.find (p := fun d => ∃ T, Repr B x T ∧ height T = d)
    (let ⟨T, hT⟩ := h; ⟨height T, T, hT, rfl⟩) else 0

/-- The specification functions: `btFns`'s (`oba_find`, `pr 2`–`4`), the `BA` contract of
`oba_get` (`pr 5`, `pr 6`), and `btree_search`'s precondition (`pr 7`), invariant (`pr 8`),
postcondition (`pr 9`), and for total correctness the precondition and invariant with a height
bound (`pr 10`, `pr 11`); `mf 0` the ghost height. -/
noncomputable def searchFns : Fns where
  pr k B as := match k, as with
    | 5, [x, i] => ∃ n α, BA B x.toNat n α ∧ i.toNat < α.length
    | 6, [x, i, r] => ∀ n α, BA B x.toNat n α → i.toNat < α.length → r = α.getD i.toNat 0
    | 7, [_] => ∃ t κ, IsBTree B t κ
    | 8, [k, x] => SubTree B k x
    | 9, [k, b] => ∀ t κ, IsBTree B t κ → (κ k → b = 1) ∧ (¬ κ k → b = 0)
    | 10, [_] => (∃ t κ, IsBTree B t κ) ∧ hgt B (wd B 4).toNat < 2 ^ 32
    | 11, [k, x] => SubTree B k x ∧ hgt B x.toNat < 2 ^ 32
    | k, as => btFns.pr k B as
  mf k B x _ := match k with
    | 0 => BitVec.ofNat 32 (hgt B x.toNat)
    | _ => x

/-- `oba_get(x, i)` on a bounded array (not necessarily ordered): the `i`-th element, memory
unchanged; total. -/
def getBASpecV : FnSpec where
  params := [.i32, .i32]
  results := [.i32]
  pre := .pr 5 (.v 0) [P32 0, P32 1]
  post := .and (.pr 6 (.v 0) [P32 0, P32 1, L32 0]) (.meq .cur (.v 0))
  mem := true
  total := true

/-- The callees of `btree_search`: `oba_get` (function `0`) and `oba_find` (function `1`). -/
def searchCalls : List (Nat × FnSpec × Func) :=
  [(0, getBASpecV, Silmaril.WasmSpec.BTree.getFunc), (1, findSpecV, Silmaril.WasmSpec.BTree.findFunc)]

/-- **`btree_search(k)`, partial correctness** (locals `k, x, i, keys`). -/
def searchSpecV : FnSpec where
  params := [.i32]
  results := [.i32]
  pre := .pr 7 (.v 0) [P32 0]
  post := .and (.pr 9 (.v 0) [P32 0, L32 0]) (.meq .cur (.v 0))
  inv := [.and (.pr 8 (.v 0) [L32 0, L32 1]) (.meq .cur (.v 0))]
  mem := true
  calls := searchCalls

/-- **`btree_search(k)`, total correctness**: the ghost variant is the height of page `x` in the
memory at entry. -/
def searchSpecT : FnSpec :=
  { searchSpecV with
    pre := .pr 10 (.v 0) [P32 0]
    inv := [.and (.pr 11 (.v 0) [L32 0, L32 1]) (.meq .cur (.v 0))]
    var := [.mfn 0 (.v 0) (L32 1) (.lit .i32 0)]
    total := true }

/-- The fuel. -/
def searchFuel : Nat := 100

end Silmaril.Wasm.Auto2.VCBSearch
