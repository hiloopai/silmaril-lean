module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Common

/-!
# Float track: one concrete interpretation of the primitives

`floatIntB P` answers the float and conversion primitives by `floatCall P` and the integer
primitives by `IntNumeric.intCall`; it satisfies both `IntNumeric.IntB` and `FloatB P`, so the
integer and float facts hold together for one `B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Numerics

/-- The integer primitives answer no float name. -/
theorem intCall_floatName {x : IL.Id} (hx : x ∈ floatNames) (ws : List ArgV) :
    IntNumeric.intCall x ws = none := by
  simp only [floatNames, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  (unfold IntNumeric.intCall; split <;> simp_all)

/-- `floatIntB P` extends the float primitives. -/
theorem floatB_floatIntB (P : Profile) : FloatB P (floatIntB P) := by
  intro x ws v h
  by_cases hx : x ∈ floatNames
  · simpa [floatCall, floatIntB, hx] using h
  · simp [floatCall, hx] at h

/-- `floatIntB P` extends the integer primitives. -/
theorem intB_floatIntB (P : Profile) : IntNumeric.IntB (floatIntB P) := by
  intro x ws v h
  by_cases hx : x ∈ floatNames
  · rw [intCall_floatName hx ws] at h
    exact absurd h (by simp)
  · simpa [floatIntB, hx] using h

end Silmaril.Wasm.SpecTec.Sim.Floats
