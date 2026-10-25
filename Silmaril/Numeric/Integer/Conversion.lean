module

public import Silmaril.Numeric.Integer

/-!
# Agreement of checked and saturating integer conversions

Saturation preserves every successful checked result, at every positive integer
width and in every rounding direction. These results compare the two conversion
policies already defined by the scalar model; they introduce no new arithmetic.
-/

@[expose] public section

namespace Silmaril.Numeric

namespace Integer

/-- Clamping is inactive on the successful domain of checked integer construction. -/
theorem ofIntSaturating_agrees {f : IntFormat} {n : Int} {x : Integer f}
    (h : ofInt? f n = some x) : ofIntSaturating f n = x := by
  have bounds := ofInt?_bounds h
  simp only [ofInt?, ite_eq_left bounds, Option.some.injEq] at h
  simpa [ofIntSaturating, ofIntWrapping, Int.min_eq_right bounds.2, Int.max_eq_right bounds.1] using h

/-- Once rounding produces an integer, saturation acts on exactly that integer. -/
theorem fromFloatSaturating_of_toInt {f : IntFormat} {value : Float.Model.UnpackedFloat}
    {mode : Ieee754.RoundingMode} {n : Int}
    (h : Ieee754.Rounding.toInt? mode value = some n) :
    fromFloatSaturating f value mode = ofIntSaturating f n := by
  cases value with
  | notANumber => cases h
  | infinity sign => cases h
  | zero sign => simp [fromFloatSaturating, h]
  | finite sign mantissa exponent positive => simp [fromFloatSaturating, h]

/-- Trapping and saturating policies agree whenever rounding and range checking succeed. -/
theorem fromFloatSaturating_agrees {f : IntFormat} {value : Float.Model.UnpackedFloat}
    {mode : Ieee754.RoundingMode} {x : Integer f}
    (h : fromFloat? f value mode = some x) : fromFloatSaturating f value mode = x := by
  unfold fromFloat? at h
  cases rounded : Ieee754.Rounding.toInt? mode value with
  | none => simp [rounded] at h
  | some n =>
    simp only [rounded, Option.bind_some] at h
    rw [fromFloatSaturating_of_toInt rounded]
    exact ofIntSaturating_agrees h

@[simp] theorem ofIntSaturating_toInt {f : IntFormat} (x : Integer f) :
    ofIntSaturating f x.toInt = x := ofIntSaturating_agrees (ofInt?_toInt x)

/-- Exact unpacking also round-trips through saturation in every rounding direction.
No bounded floating format is inserted in this statement. -/
@[simp] theorem fromFloatSaturating_unpack {f : IntFormat} (x : Integer f)
    (mode : Ieee754.RoundingMode) : fromFloatSaturating f x.unpack mode = x :=
  fromFloatSaturating_agrees (fromFloat?_unpack x mode)

end Integer

namespace Ieee754.F32

/-- Saturation preserves every successful binary32-to-integer conversion. -/
theorem toIntegerSaturating_agrees {input : F32} {target : IntFormat}
    {mode : RoundingMode} {output : Integer target}
    (h : input.toInteger? target mode = some output) :
    input.toIntegerSaturating target mode = output := Integer.fromFloatSaturating_agrees h

end Ieee754.F32

namespace Ieee754.F64

/-- Saturation preserves every successful binary64-to-integer conversion. -/
theorem toIntegerSaturating_agrees {input : F64} {target : IntFormat}
    {mode : RoundingMode} {output : Integer target}
    (h : input.toInteger? target mode = some output) :
    input.toIntegerSaturating target mode = output := Integer.fromFloatSaturating_agrees h

end Ieee754.F64

end Silmaril.Numeric
