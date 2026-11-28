module

public import Silmaril.Logic.ACL2.Standard.FixedWidth.Source
public import Silmaril.Logic.ACL2.Standard.BitSelection.Thms
import Silmaril.Proofs.Logic.ACL2.Standard.FixedWidth

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Object

/-- An in-bounds field sees the same bits before and after the container fix. -/
theorem fixedWidthProjection_eq_select (x : Object) {container width offset : Nat}
    (h : offset + width ≤ container) :
    fixedWidthProjection container width offset x =
      partSelectWidthLow x (integer width) (integer offset) :=
  Proofs.Logic.ACL2.Standard.FixedWidth.fixedWidthProjection_eq_select x h

theorem fixedWidthProjection_range (x : Object) (container width offset : Nat) :
    0 ≤ (fixedWidthProjection container width offset x).integerFix ∧
      (fixedWidthProjection container width offset x).integerFix < (2 ^ width : Nat) :=
  loghead_range (integer width) (logtail (integer offset) (loghead (integer container) x))

theorem fixedWidthProjection_of_noninteger {x : Object} (h : x.integerValue? = none)
    (container width offset : Nat) : fixedWidthProjection container width offset x = integer 0 := by
  simp [fixedWidthProjection, partSelectWidthLow, loghead, logtail, integerFix_of_noninteger h]

theorem prefixesFix_source (x : Object) : prefixesFix x = FixedWidth.Source.prefixesFix x :=
  loghead_source (integer 52) x

theorem prefixesAdr_source (x : Object) : prefixesAdr x = FixedWidth.Source.prefixesAdr x := by
  simp only [prefixesAdr, fixedWidthProjection, FixedWidth.Source.prefixesAdr, FixedWidth.Source.prefixesFix,
    loghead_source, partSelectWidthLow_source]
  rfl

theorem prefixesNum_source (x : Object) : prefixesNum x = FixedWidth.Source.prefixesNum x := by
  simp only [prefixesNum, fixedWidthProjection, FixedWidth.Source.prefixesNum, FixedWidth.Source.prefixesFix,
    loghead_source, partSelectWidthLow_source]
  rfl

theorem prefixesNxt_source (x : Object) : prefixesNxt x = FixedWidth.Source.prefixesNxt x := by
  simp only [prefixesNxt, fixedWidthProjection, FixedWidth.Source.prefixesNxt, FixedWidth.Source.prefixesFix,
    loghead_source, partSelectWidthLow_source]
  rfl

theorem prefixesAdr_eq_select (x : Object) :
    prefixesAdr x = partSelectWidthLow x (integer 8) (integer 36) :=
  fixedWidthProjection_eq_select x (by decide)

theorem prefixesNum_eq_select (x : Object) :
    prefixesNum x = partSelectWidthLow x (integer 4) (integer 0) :=
  fixedWidthProjection_eq_select x (by decide)

theorem prefixesNxt_eq_select (x : Object) :
    prefixesNxt x = partSelectWidthLow x (integer 8) (integer 44) :=
  fixedWidthProjection_eq_select x (by decide)

end Silmaril.Logic.ACL2.Standard.Object
