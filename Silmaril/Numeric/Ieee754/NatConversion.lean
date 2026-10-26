module

public import Silmaril.Numeric.Ieee754.MaximumCorrectness
public import Silmaril.Numeric.ScalarNat

/-! # Exact small dimension constants in binary32 -/

@[expose] public section
namespace Silmaril.Numeric.Arithmetic
open Ieee754 Ieee754.Conformance Float.Model Float.Model.UnpackedFloat

/-- Every natural below the binary32 significand limit converts exactly.
The tutorial layer-normalization host limit is strictly smaller. -/
theorem nat32_toRat (n : Nat) (bound : n < 2 ^ 24) : (nat32 n).toRat? = some (n : ℚ) := by
  change (output .f32 {} (Rounding.packRounded .binary32 .nearestTiesToEven
    (Rounding.ofInt n))).toRat? = some (n : ℚ)
  by_cases hn : n = 0
  · subst n
    rw [← value?_scalar_unpack, output32_unpack]
    simp [Rounding.ofInt, Rounding.ofDyadic, Rounding.packRounded_zero]
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    have hv : Rounding.ofInt (n : Int) = .finite .positive n 0 hp := by
      simp [Rounding.ofInt, Rounding.ofDyadic, hn]
    have hl : n.log2 < 24 := (Nat.log2_lt hn).mpr bound
    have ht : Format.binary32.targetExponent (totalExponent n 0) ≤ 0 := by
      norm_num [Format.targetExponent, totalExponent, Format.minExponent, Format.mantissaBits,
        Format.binary32]
      omega
    have ho : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 .nearestTiesToEven
        (.finite .positive n 0 hp)) := by
      rw [roundUnpacked_finite_of_target_le .binary32 .nearestTiesToEven .positive n 0 hp ht]
      change (Format.binary32.targetExponent (totalExponent n 0) + 127 + 23).toNat < 255
      omega
    rw [← value?_scalar_unpack, output32_unpack, hv, unpack_packRounded _ _ _ ho,
      value?_roundUnpacked_of_target_le .binary32 .nearestTiesToEven .positive n 0 hp ht]
    simp [value?, dyadic, Sign.apply]

end Silmaril.Numeric.Arithmetic
