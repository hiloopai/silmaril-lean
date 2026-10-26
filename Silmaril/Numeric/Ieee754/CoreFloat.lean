module

public import Silmaril.Numeric.Ieee754.Relations
public import Silmaril.Numeric.Ieee754.EncodingCorrectness
public import Batteries.Data.Float.Lemmas

/-!
# Lean's runtime `Float` and `Float32` as raw IEEE wrappers

Since Lean v4.35, core `Float` is a structure over `Float.Model` (and `Float32`
over `Float32.Model`), and the basic operations are `@[extern]` definitions
whose logical bodies are the model operations. The compiler runs C (`double`
and `float` arithmetic, `sqrt`, `fma`, ...) in their place; that the C
code agrees with the model is a trust boundary of the compiler, not an axiom.

Silmaril's raw wrappers `F64`/`F32` compute through the same model functions,
so the correspondence below holds by definition: arithmetic, square root,
fused multiply-add and comparisons on `F64` are the runtime `Float` operations
read back through `Float.toBits`, and likewise for `F32`/`Float32`. Runtime
`toBits` canonicalizes NaNs, which `ofFloat_isCanonicalized` reflects.

Operations that core leaves `opaque` (`floor`, `ceil`, `round`, `scaleB`,
`frExp`, `Float.toFloat32`, `Float32.toFloat`, transcendental functions) have no
logical definition; `Silmaril.Numeric.Ieee754.CoreFloatTest` compares them with
Silmaril's executable operations on edge cases and pseudo-random encodings.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754

namespace F64

/-- The runtime `Float` with these bits (NaN payloads are canonicalized). -/
def toFloat (x : F64) : Float := Float.ofBits x.bits

/-- The raw encoding of a runtime `Float`. -/
def ofFloat (f : Float) : F64 := ⟨f.toBits⟩

theorem toFloat_toModel (x : F64) : x.toFloat.toModel = x.model := rfl

theorem ofFloat_eq_ofModel (f : Float) : ofFloat f = ofModel f.toModel := rfl

theorem toFloat_ofFloat (f : Float) : (ofFloat f).toFloat = f := Float.ofBits_toBits f

theorem ofFloat_toFloat (x : F64) (h : ¬x.IsNaN) : ofFloat x.toFloat = x := by
  obtain ⟨b⟩ := x
  change (⟨(F64.mk b).model.toBits⟩ : F64) = ⟨b⟩
  rw [Conformance.model_bits64_of_not_nan _ h]

theorem ofFloat_isCanonicalized (f : Float) : (ofFloat f).IsNonNaNOrCanonicalNaN :=
  ofModel_isCanonicalized f.toModel

theorem add_eq_float (x y : F64) : x + y = ofFloat (x.toFloat + y.toFloat) := rfl
theorem sub_eq_float (x y : F64) : x - y = ofFloat (x.toFloat - y.toFloat) := rfl
theorem mul_eq_float (x y : F64) : x * y = ofFloat (x.toFloat * y.toFloat) := rfl
theorem div_eq_float (x y : F64) : x / y = ofFloat (x.toFloat / y.toFloat) := rfl
theorem sqrt_eq_float (x : F64) : x.sqrt = ofFloat x.toFloat.sqrt := rfl
theorem fma_eq_float (x y z : F64) :
    x.fma y z = ofFloat (Float.fma x.toFloat y.toFloat z.toFloat) := rfl
theorem equal_eq_float (x y : F64) : x.equal y = (x.toFloat == y.toFloat) := rfl
theorem lessThan_eq_float (x y : F64) : x.lessThan y = x.toFloat.lt y.toFloat := rfl
theorem lessEqual_eq_float (x y : F64) : x.lessEqual y = x.toFloat.le y.toFloat := by
  show Float.Model.le x.model y.model = decide (x.model.le y.model = true)
  cases Float.Model.le x.model y.model <;> rfl

end F64

namespace F32

/-- The runtime `Float32` with these bits (NaN payloads are canonicalized). -/
def toFloat32 (x : F32) : Float32 := Float32.ofBits x.bits

/-- The raw encoding of a runtime `Float32`. -/
def ofFloat32 (f : Float32) : F32 := ⟨f.toBits⟩

theorem toFloat32_toModel (x : F32) : x.toFloat32.toModel = x.model := rfl

theorem ofFloat32_eq_ofModel (f : Float32) : ofFloat32 f = ofModel f.toModel := rfl

theorem toFloat32_ofFloat32 (f : Float32) : (ofFloat32 f).toFloat32 = f :=
  Float32.ofBits_toBits f

theorem ofFloat32_toFloat32 (x : F32) (h : ¬x.IsNaN) : ofFloat32 x.toFloat32 = x := by
  obtain ⟨b⟩ := x
  change (⟨(F32.mk b).model.toBits⟩ : F32) = ⟨b⟩
  rw [Conformance.model_bits32_of_not_nan _ h]

theorem ofFloat32_isCanonicalized (f : Float32) : (ofFloat32 f).IsNonNaNOrCanonicalNaN :=
  ofModel_isCanonicalized f.toModel

theorem add_eq_float32 (x y : F32) : x + y = ofFloat32 (x.toFloat32 + y.toFloat32) := rfl
theorem sub_eq_float32 (x y : F32) : x - y = ofFloat32 (x.toFloat32 - y.toFloat32) := rfl
theorem mul_eq_float32 (x y : F32) : x * y = ofFloat32 (x.toFloat32 * y.toFloat32) := rfl
theorem div_eq_float32 (x y : F32) : x / y = ofFloat32 (x.toFloat32 / y.toFloat32) := rfl
theorem sqrt_eq_float32 (x : F32) : x.sqrt = ofFloat32 x.toFloat32.sqrt := rfl
theorem fma_eq_float32 (x y z : F32) :
    x.fma y z = ofFloat32 (Float32.fma x.toFloat32 y.toFloat32 z.toFloat32) := rfl
theorem equal_eq_float32 (x y : F32) : x.equal y = (x.toFloat32 == y.toFloat32) := rfl
theorem lessThan_eq_float32 (x y : F32) : x.lessThan y = x.toFloat32.lt y.toFloat32 := rfl
theorem lessEqual_eq_float32 (x y : F32) : x.lessEqual y = x.toFloat32.le y.toFloat32 := by
  show Float32.Model.le x.model y.model = decide (x.model.le y.model = true)
  cases Float32.Model.le x.model y.model <;> rfl

end F32

end Silmaril.Numeric.Ieee754
