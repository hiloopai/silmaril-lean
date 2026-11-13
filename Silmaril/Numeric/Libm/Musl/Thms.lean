module

public import Silmaril.Numeric.Libm.Musl.Defs
public import Silmaril.Numeric.Libm.Elementary.Defs
public import Silmaril.Numeric.Libm.Lattice.Thms

/-!
# musl's `sin` and `cos` as lattice nodes

`Musl.sin` is defined on the finite inputs below `2^20 · π/2` in magnitude
(`Musl.MediumRange`). The error bound of the algorithm there is assumed, not
proved: `Task.sin_faithful` and `Task.cos_faithful` state "within 1 ulp"
(fdlibm documents an error below 1 ulp). Conditionally on them, an
implementation that is bit-exact with musl on that range meets the 1-ulp bound
there (the edge (e) → (b)).
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.Musl

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm.Double

/-- Finite inputs whose high word is below `0x413921fb` (about `2^20 · π/2`). -/
def MediumRange : Set F64 := {x | x.isFinite = true ∧ highWord x < 0x413921fb}

namespace Task

/-- Assumed: musl's `sin` is within 1 ulp of `Real.sin` on `MediumRange`. -/
def sin_faithful : Prop :=
  ∀ x ∈ MediumRange, ∀ r, Double.sin.exact x = some r → ∀ y, Musl.sin x = some y →
    LibmFloat.Close 1 r y

/-- Assumed: musl's `cos` is within 1 ulp of `Real.cos` on `MediumRange`. -/
def cos_faithful : Prop :=
  ∀ x ∈ MediumRange, ∀ r, Double.cos.exact x = some r → ∀ y, Musl.cos x = some y →
    LibmFloat.Close 1 r y

/-- Open: the transcription is defined on all of `MediumRange`. -/
def sin_defined : Prop := ∀ x ∈ MediumRange, (Musl.sin x).isSome
def cos_defined : Prop := ∀ x ∈ MediumRange, (Musl.cos x).isSome

end Task

/-- (e) → (b), conditionally: bit-exact with musl's `sin` on its range gives
the assumed 1-ulp bound there. -/
theorem sin_errorOn_of_bitExactWhere {impl : F64 → Outcome F64}
    (h : BitExactWhere impl Musl.sin) (hdef : Task.sin_defined) (hb : Task.sin_faithful) :
    Double.sin.ErrorOn impl MediumRange 1 :=
  h.errorOn hdef hb

theorem cos_errorOn_of_bitExactWhere {impl : F64 → Outcome F64}
    (h : BitExactWhere impl Musl.cos) (hdef : Task.cos_defined) (hb : Task.cos_faithful) :
    Double.cos.ErrorOn impl MediumRange 1 :=
  h.errorOn hdef hb

end Silmaril.Numeric.Libm.Musl
