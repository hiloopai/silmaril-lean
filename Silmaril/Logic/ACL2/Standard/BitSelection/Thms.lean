module

public import Silmaril.Logic.ACL2.Standard.BitSelection.Source
public import Silmaril.Logic.ACL2.Standard.IntegerBits.Thms
import Silmaril.Proofs.Logic.ACL2.Standard.BitSelection

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Object

open Silmaril.Logic.ACL2.Standard.BitSelection

theorem loghead_source (width x : Object) : loghead width x = Source.loghead width x :=
  Proofs.Logic.ACL2.Standard.BitSelection.loghead_source width x

theorem logtail_source (low x : Object) : logtail low x = Source.logtail low x :=
  Proofs.Logic.ACL2.Standard.BitSelection.logtail_source low x

theorem partSelectWidthLow_source (x width low : Object) :
    partSelectWidthLow x width low = Source.partSelectWidthLow x width low := by
  simp only [partSelectWidthLow, Source.partSelectWidthLow, loghead_source, logtail_source]

/-- Agreement with the translated BITOPS::PART-SELECT-LOW-HIGH$INLINE body on all objects. -/
theorem partSelectLowHigh_source (x low high : Object) :
    partSelectLowHigh x low high = Source.partSelectLowHigh x low high := by
  simp only [partSelectLowHigh, Source.partSelectLowHigh, partSelectWidthLow_source, selectionWidth]

theorem logtail_ash (low x : Object) : logtail low x = x.ash (integer (-(low.natRank : Int))) :=
  Proofs.Logic.ACL2.Standard.BitSelection.logtail_ash low x

theorem selectionWidth_parts (low high : Object) :
    selectionWidth low high = ofParts (1 + (high.real - low.real)) (high.imag - low.imag) :=
  Proofs.Logic.ACL2.Standard.BitSelection.selectionWidth_parts low high

theorem selectionWidth_integer (low high : Int) :
    selectionWidth (integer low) (integer high) = integer (1 + (high - low)) :=
  Proofs.Logic.ACL2.Standard.BitSelection.selectionWidth_integer low high

/-- The all-object quotient and remainder formula, with the width computed before nfix. -/
theorem partSelectLowHigh_eq (x low high : Object) :
    partSelectLowHigh x low high = integer
      ((x.integerFix / (2 ^ low.natRank : Nat)) % (2 ^ (selectionWidth low high).natRank : Nat)) := by
  simp only [partSelectLowHigh, partSelectWidthLow, loghead, logtail, integerFix_integer]

/-- In particular, signed integer bounds of either order have this total interpretation. -/
theorem partSelectLowHigh_integerBounds (x : Object) (low high : Int) :
    partSelectLowHigh x (integer low) (integer high) = integer
      ((x.integerFix / (2 ^ low.toNat : Nat)) % (2 ^ (1 + (high - low)).toNat : Nat)) := by
  rw [partSelectLowHigh_eq, selectionWidth_integer]
  rfl

theorem loghead_of_fixed_width_zero {width : Object} (h : width.natRank = 0) (x : Object) :
    loghead width x = integer 0 := by simp [loghead, h]

theorem logtail_of_fixed_low_zero {low : Object} (h : low.natRank = 0) (x : Object) :
    logtail low x = x.ifix := by simp [logtail, h, integer_integerFix]

theorem partSelectLowHigh_of_noninteger {x : Object} (h : x.integerValue? = none) (low high : Object) :
    partSelectLowHigh x low high = integer 0 := by
  simp [partSelectLowHigh_eq, integerFix_of_noninteger h]

theorem partSelectLowHigh_of_fixed_width_zero {low high : Object}
    (h : (selectionWidth low high).natRank = 0) (x : Object) :
    partSelectLowHigh x low high = integer 0 :=
  loghead_of_fixed_width_zero h (logtail low x)

theorem partSelectLowHigh_of_reversed_bounds (x : Object) {low high : Int} (h : high < low) :
    partSelectLowHigh x (integer low) (integer high) = integer 0 := by
  have width : (1 + (high - low)).toNat = 0 := by omega
  simp [partSelectLowHigh_integerBounds, width]

theorem loghead_range (width x : Object) :
    0 ≤ (loghead width x).integerFix ∧ (loghead width x).integerFix < (2 ^ width.natRank : Nat) :=
  Proofs.Logic.ACL2.Standard.BitSelection.loghead_range width x

end Silmaril.Logic.ACL2.Standard.Object
