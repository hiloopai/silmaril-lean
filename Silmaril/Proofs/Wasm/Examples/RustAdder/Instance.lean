module

public import Silmaril.Proofs.Wasm.Examples.RustAdder.Decode
public import Silmaril.Wasm.Examples.Common.Thms
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Game.Signature.Defs

@[expose] public section

/-!
# The compiled Rust adder: its instance

`adderI`: the scalar instance of the decoded module `module` (silmaril-lean's
`instantiateOnce?` against no imports): its four function exports `add`, `max`, `mul`, `odd`
at addresses `0‥3`. `adderStore_funcs`: the instantiated store holds the four decoded bodies
with their types (by `rfl` and `decide +kernel`).
-/

namespace Silmaril.Wasm.Examples.RustAdder

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

/-- The types of the function exports, in export order: `add`, `max`, `mul`, `odd`. -/
def adderExports : List FnType :=
  [⟨[i32T, i32T], [i32T]⟩, ⟨[i32T, i32T], [i32T]⟩, ⟨[i32T, i32T], [i32T]⟩, ⟨[i32T], [i32T]⟩]

/-- **The instance of the compiled module.** -/
def adderI : ScalarInstance where
  imports := []
  exports := adderExports
  addrs := [0, 1, 2, 3]
  store := adderStore

theorem adderRun_eq : adderRun = some (adderStore, (match adderRun with
    | some (_, f, _) => f | none => {}), none) := rfl

/-- The function exports of the decoded module are at addresses `0‥3`, in this order. -/
theorem exportFuncAddrs_eq :
    (match adderRun with | some (_, f, _) => exportFuncAddrs f.module | none => []) =
      adderI.addrs := rfl

/-- The four functions of the instance: the decoded bodies, with the export types. -/
theorem adderStore_funcs : ∃ fi₀ fi₁ fi₂ fi₃ : FuncInst Nat,
    adderStore.funcs = [fi₀, fi₁, fi₂, fi₃] ∧
    fi₀.module = adderMI ∧ fi₁.module = adderMI ∧ fi₂.module = adderMI ∧ fi₃.module = adderMI ∧
    fi₀.code = .wasm ⟨⟨0⟩, locals0, body0⟩ ∧ fi₁.code = .wasm ⟨⟨0⟩, locals1, body1⟩ ∧
    fi₂.code = .wasm ⟨⟨0⟩, locals2, body2⟩ ∧ fi₃.code = .wasm ⟨⟨1⟩, locals3, body3⟩ ∧
    FnType.ofDefType? fi₀.type = some adderExports[0] ∧
    FnType.ofDefType? fi₁.type = some adderExports[1] ∧
    FnType.ofDefType? fi₂.type = some adderExports[2] ∧
    FnType.ofDefType? fi₃.type = some adderExports[3] := by
  have hty : adderStore.funcs.map (fun fi => FnType.ofDefType? fi.type) =
      adderExports.map some := by decide +kernel
  have hmod : adderStore.funcs.map FuncInst.module = [adderMI, adderMI, adderMI, adderMI] := rfl
  have hcode : adderStore.funcs.map FuncInst.code = module.funcs.map .wasm := rfl
  have hlen : adderStore.funcs.length = 4 := rfl
  obtain ⟨fi₀, fi₁, fi₂, fi₃, hf⟩ : ∃ a b c d, adderStore.funcs = [a, b, c, d] := by
    match h : adderStore.funcs, hlen with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  rw [hf] at hty hmod hcode
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, adderExports,
    module] at hty hmod hcode
  exact ⟨fi₀, fi₁, fi₂, fi₃, hf, hmod.1, hmod.2.1, hmod.2.2.1, hmod.2.2.2, hcode.1, hcode.2.1,
    hcode.2.2.1, hcode.2.2.2, hty.1, hty.2.1, hty.2.2.1, hty.2.2.2⟩

end Silmaril.Wasm.Examples.RustAdder
