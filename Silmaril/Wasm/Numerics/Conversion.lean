module

public import Silmaril.Wasm.Numerics.Float
public import Silmaril.Numeric.Integer.Conversion

/-!
# Agreement of Wasm truncation and saturating conversion

The generic scalar agreement theorem specializes to every Wasm floating and
integer width and both signedness choices. Failed truncations remain outside
this equality: saturation intentionally handles their NaNs and overflow.
-/

@[expose] public section

namespace Silmaril.Wasm.Numerics

/-- `trunc_sat` preserves every successful `trunc` result. -/
theorem truncSatFloat_agrees (source : FloatType) (target : IntType) (sign : Signedness)
    (x : FloatValue source) (y : IntValue target) (h : truncFloat source target sign x = .ok y) :
    truncSatFloat source target sign x = y := by
  unfold truncFloat at h
  cases converted : Silmaril.Numeric.Integer.fromFloat? (integerFormat target sign)
      (unpackFloat source x) with
  | none => simp only [converted] at h; split at h <;> contradiction
  | some result =>
    simp only [converted] at h
    have hy : result.bits = y := Except.ok.inj h
    rw [← hy]
    exact congrArg Silmaril.Numeric.Integer.bits
      (Silmaril.Numeric.Integer.fromFloatSaturating_agrees converted)

/-- The instruction-level executable conversions inherit the same agreement. -/
theorem convert_truncSat_of_trunc (source : FloatType) (target : IntType) (sign : Signedness)
    (x : FloatValue source) (y : IntValue target)
    (h : convert (.trunc source target sign) x = .ok y) :
    convert (.truncSat source target sign) x = .ok y :=
  congrArg Except.ok (truncSatFloat_agrees source target sign x y h)

/-- Successful trapping results are also admitted by the saturating instruction relation. -/
theorem convertRel_truncSat_of_trunc (source : FloatType) (target : IntType) (sign : Signedness)
    (x : FloatValue source) (y : IntValue target)
    (h : convertRel (.trunc source target sign) x (.ok y)) :
    convertRel (.truncSat source target sign) x (.ok y) :=
  (convert_truncSat_of_trunc source target sign x y h.symm).symm

end Silmaril.Wasm.Numerics
