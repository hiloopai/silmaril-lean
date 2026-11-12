module

public import Silmaril.Wasm.Component.FXExample.Defs
public import Silmaril.Wasm.Component.FXEngine.Thms
import Silmaril.Proofs.Wasm.Component.FXExample.Run

/-!
# Game semantics of modules with FX functions

`fxXG P` is the game engine over IR modules that carry FX functions
(`Silmaril.Wasm.Component.FXEngine`). This module states what its game semantics is on two kinds of
module.

* **`fxXG_noFX`**: on a module with no FX functions it is the Core 3.0 game semantics
  (`fxXG_ofNum` and `fxG_sem_eq_core3G`).
* **`fxXG_run_play`**: on the module `exNum` (`Silmaril.Wasm.Component.FXExample.Defs`), whose
  export `run` is an FX function that makes a continuation of a Core function `g` (returning `42`)
  and resumes it, the two-move play "call `run` with no arguments, answer `42`" is a play of its
  game semantics, at every profile. The run goes through `cont.new`, `resume`, a handler frame
  and a Core call inside it (`Silmaril.Proofs.Wasm.Component.FXExample.Run`); its final status is
  computed by `statusFX_vals` (an FX thread at values has no other step).

Together with `Silmaril.Wasm.Component.FXInv.engineLTS_atHost` (an FX thread at a host call asks
exactly that import), these are the statements about modules with FX functions that are proved;
an equality of `fxXG P` with a Core translation (CPS or asyncify) is not.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXExample

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
  Silmaril.Wasm.Component.FXEngine
open Silmaril.Proofs.Wasm.Component.FXExample
open Silmaril.Wasm.Numerics (Profile)

/-- **On a module without FX functions, `fxXG P` is Core 3.0.** -/
theorem fxXG_noFX (P : Profile) (m : NumModule) :
    (fxXG P).sem.sem ⟨⟨m.mod, []⟩, m.exports⟩ = (core3G P).sem.sem m :=
  (fxXG_ofNum P m).trans (congrArg (fun C => C.sem m) (fxG_sem_eq_core3G P))

/-- **A play of a module with an FX function**: calling `run` answers `42`. -/
theorem fxXG_run_play (P : Profile) :
    Silmaril.Proofs.Wasm.Component.Reference.two (E := sigN 0)
      (⟨⟨0, by decide⟩, .flat []⟩ : (sigN 1).Op) (some (.flat [y42])) ∈ (fxXG P).sem.sem exNum := by
  have h : (fxXG P).sem.sem exNum = engineStrategy (fxE P) ⟨exS, [(1 : Nat)]⟩ [] exIface := by
    show (match instOf (fxE P) exMod [] exIface with
      | some I => engineStrategy (fxE P) I [] exIface
      | none => Silmaril.Wasm.Component.Reference.trapAll _ _) = _
    rw [hI]
  rw [h]
  exact Silmaril.Proofs.Wasm.Component.Param.engineStrategy_two (hq P) (run_ex P)
    (Or.inl ⟨_, status_ex P, rfl⟩)

end Silmaril.Wasm.Component.FXExample
