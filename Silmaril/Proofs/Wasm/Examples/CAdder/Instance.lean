module

public import Silmaril.Proofs.Wasm.Examples.CAdder.Decode
public import Silmaril.Wasm.Examples.Common.Thms
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Game.Signature.Defs

@[expose] public section

/-!
# The compiled C adder: its instance

`adderI`: the scalar instance of the decoded module `module` (silmaril-lean's
`instantiateOnce?` against no imports): its six function exports `add`, `mul`, `max`, `odd`,
`popcount`, `gcd` at addresses `0‥5`. `adderStore_funcs`: the instantiated store holds the six
decoded bodies with their types (by `rfl` and `decide +kernel`). The module's memory, global and
(one-entry, null) table are instantiated too; no function uses them.
-/

namespace Silmaril.Wasm.Examples.CAdder

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game

/-- The instantiation of the decoded module against no imports. -/
def adderRun : Option (Store Nat × Frame × Option FuncIdx) :=
  instantiateOnce? (importStore []) module []

/-- The store after instantiation. -/
def adderStore : Store Nat :=
  match adderRun with
  | some (s, _, _) => s
  | none => {}

/-- The module instance. -/
def adderMI : ModuleInst :=
  match adderRun with
  | some (_, f, _) => f.module
  | none => {}

/-- The scalar type `i32`. -/
abbrev i32T : ScalarType := .num (.int .i32)

/-- The types of the function exports, in export order: `add`, `mul`, `max`, `odd`,
`popcount`, `gcd`. -/
def adderExports : List FnType :=
  [⟨[i32T, i32T], [i32T]⟩, ⟨[i32T, i32T], [i32T]⟩, ⟨[i32T, i32T], [i32T]⟩, ⟨[i32T], [i32T]⟩,
    ⟨[i32T], [i32T]⟩, ⟨[i32T, i32T], [i32T]⟩]

/-- **The instance of the compiled module.** -/
def adderI : ScalarInstance where
  imports := []
  exports := adderExports
  addrs := [0, 1, 2, 3, 4, 5]
  store := adderStore

theorem adderRun_eq : adderRun = some (adderStore, (match adderRun with
    | some (_, f, _) => f | none => {}), none) := rfl

/-- The function exports of the decoded module are at addresses `0‥5`, in this order. -/
theorem exportFuncAddrs_eq :
    (match adderRun with | some (_, f, _) => exportFuncAddrs f.module | none => []) =
      adderI.addrs := rfl

/-- The function at address `j`: the decoded body `j`, in the module instance, with export
type `j`. -/
def FuncAt (j : Nat) (hj : j < 6) (code : Func) : Prop :=
  ∃ fi : FuncInst Nat, adderStore.funcs[j]? = some fi ∧ fi.module = adderMI ∧
    fi.code = .wasm code ∧ FnType.ofDefType? fi.type = some (adderExports[j]'hj)

/-- The six functions of the instance: the decoded bodies, with the export types. -/
theorem adderStore_funcs :
    FuncAt 0 (by decide) ⟨⟨0⟩, locals0, body0⟩ ∧ FuncAt 1 (by decide) ⟨⟨0⟩, locals1, body1⟩ ∧
    FuncAt 2 (by decide) ⟨⟨0⟩, locals2, body2⟩ ∧ FuncAt 3 (by decide) ⟨⟨1⟩, locals3, body3⟩ ∧
    FuncAt 4 (by decide) ⟨⟨1⟩, locals4, body4⟩ ∧ FuncAt 5 (by decide) ⟨⟨0⟩, locals5, body5⟩ := by
  have hty : adderStore.funcs.map (fun fi => FnType.ofDefType? fi.type) =
      adderExports.map some := by decide +kernel
  have hmod : adderStore.funcs.map FuncInst.module =
      [adderMI, adderMI, adderMI, adderMI, adderMI, adderMI] := rfl
  have hcode : adderStore.funcs.map FuncInst.code = module.funcs.map .wasm := rfl
  have hlen : adderStore.funcs.length = 6 := rfl
  obtain ⟨f₀, f₁, f₂, f₃, f₄, f₅, hf⟩ :
      ∃ a b c d e g, adderStore.funcs = [a, b, c, d, e, g] := by
    match h : adderStore.funcs, hlen with
    | [a, b, c, d, e, g], _ => exact ⟨a, b, c, d, e, g, rfl⟩
  rw [hf] at hty hmod hcode
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, adderExports,
    module] at hty hmod hcode
  simp only [FuncAt, hf]
  exact ⟨⟨f₀, rfl, hmod.1, hcode.1, hty.1⟩, ⟨f₁, rfl, hmod.2.1, hcode.2.1, hty.2.1⟩,
    ⟨f₂, rfl, hmod.2.2.1, hcode.2.2.1, hty.2.2.1⟩,
    ⟨f₃, rfl, hmod.2.2.2.1, hcode.2.2.2.1, hty.2.2.2.1⟩,
    ⟨f₄, rfl, hmod.2.2.2.2.1, hcode.2.2.2.2.1, hty.2.2.2.2.1⟩,
    ⟨f₅, rfl, hmod.2.2.2.2.2, hcode.2.2.2.2.2, hty.2.2.2.2.2⟩⟩

end Silmaril.Wasm.Examples.CAdder
