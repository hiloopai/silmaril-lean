module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeEntry

/-!
# What `vecNB P` answers at the clause-less lane primitives

Split from `VecWholePrims` for build time.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB vecNB_call_of_ne)

variable {B : Builtins}

/-- `vecNB P` satisfies `IntB`. -/
theorem intB_vecNB (P : Profile) : Sim.IntNumeric.IntB (vecNB P) := by
  intro x ws v h
  by_cases h₁ : x = "vunop_"
  · subst h₁; simp [Sim.IntNumeric.intCall] at h
  by_cases h₂ : x = "vbinop_"
  · subst h₂; simp [Sim.IntNumeric.intCall] at h
  by_cases h₃ : x = "vrelop_"
  · subst h₃; simp [Sim.IntNumeric.intCall] at h
  by_cases h₄ : x = "inv_lanes_"
  · subst h₄; simp [Sim.IntNumeric.intCall] at h
  by_cases h₅ : x = "lanes_"
  · subst h₅; simp [Sim.IntNumeric.intCall] at h
  rw [vecNB_call_of_ne h₁ h₂ h₃, VecLane.vecB_call_of_ne h₄ h₅]
  exact Whole.intB_storeB P x ws v h

/-- **`$iavgr_`, `$iq15mulr_sat_`, `$fpmin_` and `$fpmax_` are answered by no name of `vecNB P`.** -/
theorem vecNB_unanswered (P : Profile) {x : IL.Id}
    (hx : x ∈ ["iavgr_", "iq15mulr_sat_", "fpmin_", "fpmax_"]) (ws : List ArgV) :
    (vecNB P).call x ws = none := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    rw [vecNB_call_of_ne (by decide) (by decide) (by decide),
      VecLane.vecB_call_of_ne (by decide) (by decide), Whole.storeB_call_of_ne (by decide),
      Whole.laneB_call_of_ne (by decide) (by decide), Whole.vbytesB_call_of_ne (by decide),
      Whole.growB_call_of_ne (by decide) (by decide)] <;>
    simp [Sim.Floats.floatIntB, Sim.Floats.floatNames, Sim.IntNumeric.intCall]

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
