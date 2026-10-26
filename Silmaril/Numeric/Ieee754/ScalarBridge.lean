module

public import Silmaril.Numeric.Scalar
public import Silmaril.Numeric.Ieee754.Exact

/-! # Exact scalar decoding and the independent rational arithmetic specification

This bridge applies to every scalar storage format. It identifies the executable
low-precision decoder with the rational value used by the conformance proofs.
-/

@[expose] public section

namespace Silmaril.Numeric.LowPrecision

open Float.Model Float.Model.UnpackedFloat

theorem unpackedRat_unpackBits (spec : FormatSpec) (bits : Nat) :
    unpackedRat? (unpackBits spec bits) = exactValue? spec bits := by
  cases hn : isNaNBits spec bits <;> cases hi : isInfinityBits spec bits <;>
    cases hs : encodingSign spec bits <;> by_cases he : exponentField spec bits = 0 <;>
    by_cases hf : fractionField spec bits = 0 <;>
    simp_all [unpackBits, exactValue?, unpackedRat?, encodingSign, signBit, signedRat]

end Silmaril.Numeric.LowPrecision

namespace Silmaril.Numeric.Scalar

theorem unpack_toRat {format : FloatFormat} (x : Scalar format) :
    LowPrecision.unpackedRat? x.unpack = x.toRat? :=
  LowPrecision.unpackedRat_unpackBits format.spec x.bits.toNat

end Silmaril.Numeric.Scalar

namespace Silmaril.Numeric.Ieee754.Conformance
open Float.Model Float.Model.UnpackedFloat

theorem value?_eq_unpackedRat (x : UnpackedFloat) : value? x = LowPrecision.unpackedRat? x := by
  cases x with
  | notANumber | infinity | zero => rfl
  | finite sign m e hm =>
    cases sign <;> simp [value?, dyadic, Sign.apply, LowPrecision.unpackedRat?, LowPrecision.signedRat]

theorem value?_scalar_unpack {format : FloatFormat} (x : Scalar format) : value? x.unpack = x.toRat? :=
  (value?_eq_unpackedRat x.unpack).trans x.unpack_toRat

end Silmaril.Numeric.Ieee754.Conformance
