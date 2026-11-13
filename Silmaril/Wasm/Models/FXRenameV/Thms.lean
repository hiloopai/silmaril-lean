module

public import Silmaril.Proofs.Wasm.Models.FXRenameV.Core

/-!
# Exception renaming for `StepFX'`: statements

* `Task.exnRenameBisimFX'` (`Defs`, **frozen**, open): the `StepFX'` analogue of
  `Task.exnRenameBisim`, with FX code and a renamed continuation store.
* **`exnRenameBisimFX'_core`**: it holds on Core code, for any continuation stores.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXRenameV

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

/-- **`Task.exnRenameBisimFX'` on Core code**, with any continuation stores. -/
theorem exnRenameBisimFX'_core {H : Type} {P : Profile} {n : Nat}
    (K₁ K₂ : List (Option ContFX)) (c : Config H) {t : Store H} (h : ExnRen n c.store t) :
    behavioursFX' P noHost noFX ⟨t, K₂, rnFrame n c.frame, rnL n (c.code.map .core)⟩ =
      rnBeh n '' behavioursFX' P noHost noFX ⟨c.store, K₁, c.frame, c.code.map .core⟩ :=
  Silmaril.Proofs.Wasm.Models.FXRenameV.exnRenameBisimFX'_core K₁ K₂ c h

/-- info: 'Silmaril.Wasm.Models.FXRenameV.exnRenameBisimFX'_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exnRenameBisimFX'_core

end Silmaril.Wasm.Models.FXRenameV
