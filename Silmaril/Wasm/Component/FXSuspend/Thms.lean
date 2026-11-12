module

public import Silmaril.Wasm.Component.FXSuspend.Defs
public import Silmaril.Wasm.Component.FXEngineV.Thms
import Silmaril.Proofs.Wasm.Component.FXSuspend.Run

/-!
# A play of a module whose code suspends

**`fxXGV_suspend_play`**: on the module `exNum` (`Silmaril.Wasm.Component.FXSuspend.Defs`), whose
export `run` makes a continuation of the FX function `sus`, resumes it under a handler for tag
0, catches its `suspend 0` by branching out of a block with the captured continuation, and
resumes that continuation to the end of `sus`, the two-move play "call `run` with no arguments,
answer `7`" is a play of the game semantics of the engine with suspension `fxXGV P`, at every
profile.

The run (`Silmaril.Proofs.Wasm.Component.FXSuspend.Run`) takes a `suspend` step (a continuation
capturing the frame and label of `sus` is allocated) and then a `br` with that continuation as
its operand; the answer `7` is computed by the part of `sus` after the `suspend`, so it is
observable only if the suspension and the resumption both happen.

Neither step is available in the WasmFX engine `fxE P` of `fxXG P`: there `ref.func` cannot
name an FX function (FX functions are outside the instance's index space), and a branch with a
continuation operand is stuck under `StepFX` (`suspend_to_label_stuck`). So `fxXG P` has no
play in which a `suspend` completes; this is the reason for `fxEV P`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXSuspend

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
  Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Proofs.Wasm.Component.FXSuspend
open Silmaril.Wasm.Numerics (Profile)

/-- **A play of code that suspends and is resumed**: calling `run` answers `7`. -/
theorem fxXGV_suspend_play (P : Profile) :
    Silmaril.Proofs.Wasm.Component.Reference.two (E := sigN 0)
      (⟨⟨0, by decide⟩, .flat []⟩ : (sigN 1).Op) (some (.flat [y7])) ∈ (fxXGV P).sem.sem exNum := by
  have h : (fxXGV P).sem.sem exNum = engineStrategy (fxEV P) ⟨exS, [(1 : Nat)]⟩ [] exIface := by
    show (match instOf (fxEV P) exMod [] exIface with
      | some I => engineStrategy (fxEV P) I [] exIface
      | none => Silmaril.Wasm.Component.Reference.trapAll _ _) = _
    rw [hI]
  rw [h]
  exact Silmaril.Proofs.Wasm.Component.Param.engineStrategy_two (hq P) (run_ex P)
    (Or.inl ⟨_, status_ex P, rfl⟩)

/-- info: 'Silmaril.Wasm.Component.FXSuspend.fxXGV_suspend_play' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fxXGV_suspend_play

end Silmaril.Wasm.Component.FXSuspend
