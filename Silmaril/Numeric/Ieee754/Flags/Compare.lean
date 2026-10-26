module

public import Silmaril.Numeric.Ieee754.Flags.Denormal

/-!
# Exception flags of comparisons and of minimum and maximum

Comparisons and the minimum/maximum operations deliver no rounded result, so
only the invalid-operation exception can arise, and it depends only on NaN
operands:

* Comparisons (IEEE 754-2019 §5.11): the quiet predicates
  (`compareQuietEqual`, …) signal invalid only for signaling NaN operands; the
  signaling predicates (`compareSignalingLess`, …) signal invalid for any NaN
  operand (§5.11, Table 5.2 and Table 5.3).
* `minimum`, `maximum`, `minimumNumber`, `maximumNumber` (§9.6) and the
  IEEE 754-2008 `minNum`/`maxNum` (§5.3.1) signal invalid only for signaling NaN
  operands (§6.2, §7.2(a)).

Architectures depart from these rules per instruction. For example x86
`MINSS`/`MAXSS` signal invalid for any NaN operand, the rule of a signaling
comparison; the profile layer (`Silmaril.Numeric.Float`) states such departures
against the functions here.

Neither rule inspects the value of a finite operand, so input flushing does not
change these flags (`compare_flushInput`, `minMax_flushInput`).
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

open Float.Model

/-- Flags of a comparison (§5.11). `signaling` selects the signaling predicates. -/
def compare (signaling : Bool) (x y : Datum) : Flags :=
  if x.isSignaling || y.isSignaling || (signaling && (x.isNaN || y.isNaN)) then invalid
  else Flags.empty

/-- Flags of `minimum`, `maximum`, `minimumNumber` and `maximumNumber` (§9.6), and
of IEEE 754-2008 `minNum`/`maxNum`: invalid exactly for a signaling NaN operand. -/
def minMax (x y : Datum) : Flags :=
  if x.isSignaling || y.isSignaling then invalid else Flags.empty

theorem compare_coherent (signaling : Bool) (x y : Datum) : Coherent (compare signaling x y) := by
  unfold compare
  split
  · exact coherent_invalid
  · exact coherent_empty

theorem minMax_coherent (x y : Datum) : Coherent (minMax x y) := by
  unfold minMax
  split
  · exact coherent_invalid
  · exact coherent_empty

/-- A quiet comparison raises the flags of the IEEE minimum and maximum. -/
theorem compare_false (x y : Datum) : compare false x y = minMax x y := by
  simp [compare, minMax]

/-- A signaling comparison signals invalid exactly when some operand is a NaN. -/
theorem compare_true (x y : Datum) :
    compare true x y = if x.isNaN || y.isNaN then invalid else Flags.empty := by
  unfold compare
  have hx := @Datum.isNaN_of_isSignaling x
  have hy := @Datum.isNaN_of_isSignaling y
  cases h1 : x.isSignaling <;> cases h2 : y.isSignaling <;> cases h3 : x.isNaN <;> cases h4 : y.isNaN <;> simp_all

/-- The flags of a signaling comparison agree with those of the IEEE minimum and
maximum unless some operand is a quiet NaN and none is signaling. -/
theorem compare_true_eq_minMax_iff (x y : Datum) :
    compare true x y = minMax x y ↔
      ((x.isNaN || y.isNaN) = true → (x.isSignaling || y.isSignaling) = true) := by
  rw [compare_true]
  unfold minMax
  have hx := @Datum.isNaN_of_isSignaling x
  have hy := @Datum.isNaN_of_isSignaling y
  cases h1 : x.isSignaling <;> cases h2 : y.isSignaling <;> cases h3 : x.isNaN <;> cases h4 : y.isNaN <;>
    simp_all <;> decide

@[simp] theorem compare_flushInput (f : Format) (signaling : Bool) (x y : Datum) :
    compare signaling (flushInput f x) (flushInput f y) = compare signaling x y := by
  simp [compare]

@[simp] theorem minMax_flushInput (f : Format) (x y : Datum) :
    minMax (flushInput f x) (flushInput f y) = minMax x y := by
  simp [minMax]

end Silmaril.Numeric.Ieee754.FlagSpec
