module

public import Silmaril.Wasm.LimeCompile.DirectEx.Defs
public import Silmaril.Wasm.LimeCompile.Direct.Thms
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# The direct 3.0 → Lime compiler on concrete modules

* `pickM_lower`: the lowering of `pickM` is the Core image of `pickL`;
* `compile_pickM`: `pickM` compiles to `pickL` (`pickM_lower` and `compile_lime`); `pickM` is
  valid (`pickM_validates`, silmaril's validator evaluated by `decide`);
* `pickM_equiv`: `pickM`, a module outside Lime1, is exactly export-equivalent to the Core image
  of the Lime1 module `pickL`, at every profile and code-parametric host;
* `compile_pickL`: `pickL` itself compiles to itself;
* `compile_refM`: the module with a `funcref` parameter in its API is rejected.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.DirectEx

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Direct

theorem pickM_lower : lowerModule pickM = pickL.toCore := by
  simp [lowerModule, pickM, pickL, lowerFunc, pickBodyM, pickBodyL, lowerL, lowerI, selectNum,
    isNumType, Lime1.Module.toCore, Lime1.Func.toCore, Lime1.Expr.toCore, Lime1.Instr.toCore]

theorem pickM_validates : ∃ mt, ModuleOk pickM mt := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp (show (validate? pickM).isSome = true by decide)
  exact ⟨mt, validate?_sound hmt⟩

theorem compile_pickL : compile pickL.toCore = some pickL :=
  compile_lime pickL

theorem compile_pickM : compile pickM = some pickL := by
  rw [← compile_pickL, ← pickM_lower]
  unfold compile
  rw [show lowerModule (lowerModule pickM) = lowerModule pickM by
    rw [pickM_lower]; exact Silmaril.Proofs.Wasm.LimeCompile.Direct.lowerModule_toCore pickL]

/-- **A module outside Lime1 is exactly export-equivalent to a Lime1 module.** -/
theorem pickM_equiv {H : Type} {P : Profile} {host : HostSemantics H}
    (hhost : Execution.Core.Sim.HostParametric host) :
    ExportEquiv (· = ·) P host pickM pickL.toCore :=
  compile_correct hhost compile_pickM pickM_validates

/-- **A 3.0-only API is rejected.** -/
theorem compile_refM : compile refM = none :=
  compile_none_of_types (by decide)

/-- info: 'Silmaril.Wasm.LimeCompile.DirectEx.pickM_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pickM_equiv

end Silmaril.Wasm.LimeCompile.DirectEx
