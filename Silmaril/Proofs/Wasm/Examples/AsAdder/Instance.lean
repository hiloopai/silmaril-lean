module

public import Silmaril.Proofs.Wasm.Examples.AsAdder.Decode
public import Silmaril.Wasm.Examples.Common.Thms
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Game.Signature.Defs

@[expose] public section

/-!
# The compiled AssemblyScript adder: its instance

`asI`: the scalar instance of the decoded module `module` (silmaril-lean's
`instantiateOnce?` against no imports; the module has none): its four function exports
`add`, `mul`, `max`, `odd` (in export order) at addresses `3, 1, 2, 0` (`asc` emits the
functions in a different order from the exports). `asStore_funcs`: the instantiated store
holds the four decoded bodies with their types (by `rfl` and `decide +kernel`).
-/

namespace Silmaril.Wasm.Examples.AsAdder

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game

/-- The instantiation of the decoded module against no imports. -/
def asRun : Option (Store Nat × Frame × Option FuncIdx) :=
  instantiateOnce? (importStore []) module []

/-- The store after instantiation. -/
def asStore : Store Nat :=
  match asRun with
  | some (s, _, _) => s
  | none => {}

/-- The module instance. -/
def asMI : ModuleInst :=
  match asRun with
  | some (_, f, _) => f.module
  | none => {}

/-- The scalar type `i32`. -/
abbrev i32T : ScalarType := .num (.int .i32)

/-- The types of the function exports, in export order: `add`, `mul`, `max`, `odd`. -/
def asExports : List FnType :=
  [⟨[i32T, i32T], [i32T]⟩, ⟨[i32T, i32T], [i32T]⟩, ⟨[i32T, i32T], [i32T]⟩, ⟨[i32T], [i32T]⟩]

/-- **The instance of the compiled module.** -/
def asI : ScalarInstance where
  imports := []
  exports := asExports
  addrs := [3, 1, 2, 0]
  store := asStore

theorem asRun_eq : asRun = some (asStore, (match asRun with
    | some (_, f, _) => f | none => {}), none) := rfl

/-- The function exports of the decoded module are at addresses `3, 1, 2, 0`, in this order. -/
theorem exportFuncAddrs_eq :
    (match asRun with | some (_, f, _) => exportFuncAddrs f.module | none => []) =
      asI.addrs := rfl

/-- The four functions of the instance, by address: the decoded bodies of `odd`, `mul`,
`max`, `add`, with the types of exports `3, 1, 2, 0`. -/
theorem asStore_funcs : ∃ fi₀ fi₁ fi₂ fi₃ : FuncInst Nat,
    asStore.funcs = [fi₀, fi₁, fi₂, fi₃] ∧
    fi₀.module = asMI ∧ fi₁.module = asMI ∧ fi₂.module = asMI ∧ fi₃.module = asMI ∧
    fi₀.code = .wasm ⟨⟨1⟩, locals0, body0⟩ ∧ fi₁.code = .wasm ⟨⟨0⟩, locals1, body1⟩ ∧
    fi₂.code = .wasm ⟨⟨0⟩, locals2, body2⟩ ∧ fi₃.code = .wasm ⟨⟨0⟩, locals3, body3⟩ ∧
    FnType.ofDefType? fi₀.type = some asExports[3] ∧
    FnType.ofDefType? fi₁.type = some asExports[1] ∧
    FnType.ofDefType? fi₂.type = some asExports[2] ∧
    FnType.ofDefType? fi₃.type = some asExports[0] := by
  have hty : asStore.funcs.map (fun fi => FnType.ofDefType? fi.type) =
      [asExports[3], asExports[1], asExports[2], asExports[0]].map some := by decide +kernel
  have hmod : asStore.funcs.map FuncInst.module = [asMI, asMI, asMI, asMI] := rfl
  have hcode : asStore.funcs.map FuncInst.code = module.funcs.map .wasm := rfl
  have hlen : asStore.funcs.length = 4 := rfl
  obtain ⟨fi₀, fi₁, fi₂, fi₃, hf⟩ : ∃ a b c d, asStore.funcs = [a, b, c, d] := by
    match h : asStore.funcs, hlen with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  rw [hf] at hty hmod hcode
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, asExports,
    module] at hty hmod hcode
  exact ⟨fi₀, fi₁, fi₂, fi₃, hf, hmod.1, hmod.2.1, hmod.2.2.1, hmod.2.2.2, hcode.1, hcode.2.1,
    hcode.2.2.1, hcode.2.2.2, hty.1, hty.2.1, hty.2.2.1, hty.2.2.2⟩

end Silmaril.Wasm.Examples.AsAdder
