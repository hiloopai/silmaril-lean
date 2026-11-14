module

public import Silmaril.Numeric.Libm.Exact.Defs
import Silmaril.Numeric.Ieee754.RneBridge

/-! # Proofs for the batch-1 references

The integral roundings are exact and `sqrt` is correctly rounded, from the
executable-rounding theorems of `Silmaril.Numeric.Ieee754.Flags`. -/

@[expose] public section

namespace Silmaril.Proofs.Numeric.Libm.Exact

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec Silmaril.Numeric.Libm
open Silmaril.Numeric.Libm.B64 Silmaril.Numeric.Libm.Double

theorem onFinite_some {D : ℝ → Prop} {R : ℝ → ℝ} {x : F64} {r : ℝ}
    (h : onFinite D R x = some r) : ∃ a, x.toRat? = some a ∧ D a ∧ R a = r := by
  unfold onFinite at h
  rcases hx : x.toRat? with _ | a <;> rw [hx] at h
  · cases h
  · simp only at h
    split_ifs at h with hD
    exact ⟨a, rfl, hD, Option.some.inj h⟩

theorem integral_exact (name : String) (mode : RoundingMode) (inexact : Bool) :
    (integral name mode inexact).Exact (Outcome.pure (F64.roundIntegral mode)) := by
  intro x r hr
  have hr' : onFinite (fun _ => True) (fun a => (roundInt mode a : ℝ)) x = some r := hr
  obtain ⟨a, hx, -, rfl⟩ := onFinite_some hr'
  refine ⟨(roundInt mode a : ℚ), F64.roundIntegral_rounded? mode hx, ?_⟩
  rw [roundInt_ratCast]
  push_cast
  rfl

theorem sqrt_correctlyRounded : Double.sqrt.CorrectlyRounded (Outcome.pure Ref.sqrt) := by
  intro x r hr
  have hr' : onFinite (0 ≤ ·) Real.sqrt x = some r := hr
  obtain ⟨a, hx, ha, rfl⟩ := onFinite_some hr'
  have ha' : (0 : ℚ) ≤ a := by exact_mod_cast ha
  show (F64.sqrt x).rounded?.map Rounded.cast = some (deliver .binary64 .nearestTiesToEven _)
  rw [← F64.sqrtWith_rne]
  exact F64.sqrtWith_rounded? .nearestTiesToEven hx ha'

end Silmaril.Proofs.Numeric.Libm.Exact
