module

public import Silmaril.Wasm.Models.FXRenameV.Defs
public import Silmaril.Wasm.Models.FXRenameSim.Thms
public import Silmaril.Wasm.Models.FXV.Thms

/-!
# Exception renaming for `StepFX'` on Core code

`rnL_map_core`: renaming FX code made of Core code is renaming the Core code.
**`exnRenameBisimFX'_core`**: `Task.exnRenameBisimFX'` holds for configurations whose code is
Core code, with **any** continuation stores on both sides (without FX functions `StepFX'` runs
such code as Core 3.0, `behavioursFX'_ofCoreK`, and the Core renaming is `behaviours_rn_eq`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameV

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.Models.FXRenameV
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

theorem rnL_map_core (n : Nat) (cs : List Admin) :
    rnL n (cs.map AdminFX.core) = (rnAdmins n cs).map AdminFX.core := by
  induction cs with
  | nil => simp [rnL, rnAdmins]
  | cons a cs ih => simp [rnL, rnA, rnAdmins, ih]

/-- **Exception renaming for `StepFX'` on Core code.** -/
theorem exnRenameBisimFX'_core {n : Nat} (K₁ K₂ : List (Option ContFX)) (c : Config H)
    {t : Store H} (h : ExnRen n c.store t) :
    behavioursFX' P noHost noFX ⟨t, K₂, rnFrame n c.frame, rnL n (c.code.map .core)⟩ =
      rnBeh n '' behavioursFX' P noHost noFX ⟨c.store, K₁, c.frame, c.code.map .core⟩ := by
  have hL : behavioursFX' P noHost noFX ⟨t, K₂, rnFrame n c.frame, rnL n (c.code.map .core)⟩ =
      behavioursOf P noHost ⟨t, rnFrame n c.frame, rnAdmins n c.code⟩ := by
    rw [rnL_map_core]
    exact behavioursFX'_ofCoreK K₂ ⟨t, rnFrame n c.frame, rnAdmins n c.code⟩
  have hR : behavioursFX' P noHost noFX ⟨c.store, K₁, c.frame, c.code.map .core⟩ =
      behavioursOf P noHost c := behavioursFX'_ofCoreK K₁ c
  rw [hL, hR]
  exact Silmaril.Wasm.Models.FXRenameSim.behaviours_rn_eq h

end Silmaril.Proofs.Wasm.Models.FXRenameV
