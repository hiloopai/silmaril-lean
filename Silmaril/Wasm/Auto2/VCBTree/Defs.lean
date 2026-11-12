module

public import Silmaril.Wasm.Auto2.VCGen.Defs
public import Silmaril.WasmSpec.BTree.Defs

/-!
# The B-tree library's array functions through the VC generator

`oba_get` and `oba_find` of the Wasm
specification library's B-tree entry (`Silmaril.WasmSpec.BTree`, the ordered bounded arrays of Watt
et al.) against annotated specifications of the VC generator, whose user predicates state the
library's `OBA` facts for every capacity and contents:

* `oba_get(x, k)`: if `OBA B x n α` and `k < |α|` for some `n, α` (precondition `pr 0`), the
  result is `α[k]` for all of them (`pr 1`) and memory is unchanged;
* `oba_find(x, e)`: the result is a `FindsAt α e` index for every `n, α` with `OBA B x n α`
  (`pr 3`), memory unchanged; loop invariant `pr 2` (`i ≤ |α|`, everything before `i` below
  `e`), variant `2^32 - 1 - i`.

Conditions in `Silmaril.Proofs.Wasm.Auto2.VCBTree.Conds`, results in `Silmaril.Wasm.Auto2.VCBTree.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCBTree

open Silmaril.Wasm
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.BTree (OBA FindsAt)

/-- Some ordered bounded array at `x`. -/
def SomeOBA (B : ByteArray) (x : BitVec 32) : Prop := ∃ n α, OBA B x.toNat n α

/-- The specification functions (memory: the memory at entry). -/
def btFns : Fns where
  pr k B as := match k, as with
    | 0, [x, k] => ∃ n α, OBA B x.toNat n α ∧ k.toNat < α.length
    | 1, [x, k, r] => ∀ n α, OBA B x.toNat n α → k.toNat < α.length → r = α.getD k.toNat 0
    | 2, [x, e, i] => ∀ n α, OBA B x.toNat n α →
        i.toNat ≤ α.length ∧ ∀ j < i.toNat, (α.getD j 0).toInt < e.toInt
    | 3, [x, e, r] => ∀ n α, OBA B x.toNat n α → FindsAt α e r.toNat
    | 4, [x, _] => SomeOBA B x
    | _, _ => True

abbrev P32 (i : Nat) : Tm .i32 := .var .i32 i
abbrev L32 (j : Nat) : Tm .i32 := .loc .i32 j

/-- `oba_get(x, k)`. -/
def getSpecV : FnSpec where
  params := [.i32, .i32]
  results := [.i32]
  pre := .pr 0 (.v 0) [P32 0, P32 1]
  post := .and (.pr 1 (.v 0) [P32 0, P32 1, L32 0]) (.meq .cur (.v 0))
  mem := true
  total := true

/-- `oba_find(x, e)` (locals `x, e, i`). -/
def findSpecV : FnSpec where
  params := [.i32, .i32]
  results := [.i32]
  pre := .pr 4 (.v 0) [P32 0, P32 1]
  post := .and (.pr 3 (.v 0) [P32 0, P32 1, L32 0]) (.meq .cur (.v 0))
  inv := [.and (.pr 2 (.v 0) [L32 0, L32 1, L32 2]) (.meq .cur (.v 0))]
  mem := true
  var := [.bin .sub (.lit .i32 4294967295) (L32 2)]
  total := true

/-- The fuel. -/
def btFuel : Nat := 100

end Silmaril.Wasm.Auto2.VCBTree
