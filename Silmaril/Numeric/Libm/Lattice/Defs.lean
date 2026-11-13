module

public import Silmaril.Numeric.Ieee754.Flags
public import Silmaril.Numeric.Ieee754.Operations

/-!
# The libm specification lattice

A C99/POSIX math function is specified here by a `Spec`: its exact mathematical
result on the inputs where one is defined (a real number, before rounding), and
the list of special cases that C99 Annex F and POSIX prescribe (NaN, signed
zeros, infinities, poles and domain errors, with their exception flags and
`errno`). An implementation is a function from inputs to `Outcome`s: a returned
encoding, the IEEE flags raised and the `errno` set.

The nodes of the lattice, for one function, are:

* (a) `SpecialValues`, `SpecialFlags`, `SpecialErrno`, and their conjunction
  `Special`: Annex F and POSIX special cases.
* (b) `ErrorOn D k`: on the inputs in `D`, the result is within `k` ulps of the
  exact result.
* (c) `ErrorGlobal k`: (b) on every input.
* (d) `CorrectlyRounded` (the IEEE round-to-nearest result, at most 1/2 ulp),
  `CRWithin n` (at most `n` ulps from the correctly rounded result, the measure
  of glibc's `libm-test-ulps` tables), and `Exact` (the exact result itself, for
  functions such as `floor` whose result is always representable).
* (e) `BitExact ref`: the returned encodings are those of a fixed pure Lean
  function `ref`, for instance a transcription of a particular libm's algorithm.

`Accuracy` names the accuracy nodes, `Spec.Valid` is "exports a valid `f` at
accuracy `a`" (the special cases and the accuracy node) and `ValidLibm` combines
per-function problems into "exports a valid libm at level `L`". The edges
between the nodes are proved in `Silmaril.Numeric.Libm.Lattice.Thms`.

Units in the last place follow the usual definition for an exact result `r`
(Goldberg; Muller, *Elementary Functions*, §2.1): `ulp r = 2 ^ quantum r`, the
spacing of the format's numbers at `r`'s binade, never finer than the subnormal
spacing (`FlagSpec.quantum`). An infinite result is measured against the first
power of two beyond the format, `2 ^ (emax + 1)`, in units of the top binade's
spacing; at `k = 1/2` this is exactly IEEE 754's round-to-nearest overflow
threshold.

References: ISO/IEC 9899:2018 §7.12 and Annex F; POSIX.1-2024 `<math.h>`;
IEEE Std 754-2019 §§4.3, 7.4, 9.2.
-/

@[expose] public section

namespace Silmaril.Numeric.Libm

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec Float.Model

/-! ## Return formats -/

/-- A binary interchange format returned by a libm function: its rounding
format, the delivered value of an encoding (`none` for a NaN), and its sign bit.
`representable` records that a finite encoding denotes a number of the format. -/
class LibmFloat (τ : Type) where
  format : Format
  rounded? : τ → Option (Rounded ℚ)
  isNaN : τ → Bool
  signBit : τ → Bool
  representable : ∀ y v, rounded? y = some (.finite v) → Representable format v

instance : LibmFloat F64 where
  format := .binary64
  rounded? := F64.rounded?
  isNaN := F64.isNaN
  signBit := F64.signBit
  representable y v h := by
    obtain ⟨_, hd⟩ := (F64.toRat?_eq_some_iff y v).mp ((F64.toRat?_eq_iff_rounded? y v).mpr h)
    exact F64.datum_finite_representable y hd

instance : LibmFloat F32 where
  format := .binary32
  rounded? := F32.rounded?
  isNaN := F32.isNaN
  signBit := F32.signBit
  representable y v h := by
    obtain ⟨_, hd⟩ := (F32.toRat?_eq_some_iff y v).mp ((F32.toRat?_eq_iff_rounded? y v).mpr h)
    exact F32.datum_finite_representable y hd

/-! ## Distances to an exact result -/

/-- The unit in the last place at an exact result `r`. -/
noncomputable def ulp (f : Format) (r : ℝ) : ℝ := 2 ^ quantum f r

/-- A delivered value is within `k` ulps of the exact result `r`. A NaN is never
close; an infinity is close when it has the sign of `r` and `r` is within `k`
top-binade ulps of `2 ^ (emax + 1)` or beyond it. -/
def UlpClose (f : Format) (k r : ℝ) : Option (Rounded ℚ) → Prop
  | some (.finite v) => |(v : ℝ) - r| ≤ k * ulp f r
  | some (.infinite negative) =>
    negative = decide (r < 0) ∧ (2 : ℝ) ^ (emax f + 1) - |r| ≤ k * 2 ^ maxQuantum f
  | none => False

/-- A delivered value is the IEEE result of rounding `r` in direction `mode`
(§4.3, with overflow per §7.4). The sign of a zero result is not constrained. -/
def RoundsTo (f : Format) (mode : RoundingMode) (r : ℝ) (y : Option (Rounded ℚ)) : Prop :=
  y.map Rounded.cast = some (deliver f mode r)

/-- A delivered value is within `n` ulps of the correctly rounded result, the
ulps being those of the correctly rounded result. This is the measure of
glibc's `libm-test-ulps` tables (`math/libm-test-support.c`), where an
infinite expected result must be matched exactly. -/
def CRDistance (f : Format) (n : ℝ) (r : ℝ) (y : Option (Rounded ℚ)) : Prop :=
  match deliver f .nearestTiesToEven r, y with
  | .finite c, some (.finite v) => |(v : ℝ) - c| ≤ n * ulp f c
  | .infinite negative, some (.infinite negative') => negative = negative'
  | _, _ => False

namespace LibmFloat

variable {τ : Type} [LibmFloat τ]

/-- `y` is within `k` ulps of the exact result `r`. -/
def Close (k r : ℝ) (y : τ) : Prop := UlpClose (format τ) k r (rounded? y)

/-- `y` is the round-to-nearest-even result for `r`. -/
def CR (r : ℝ) (y : τ) : Prop := RoundsTo (format τ) .nearestTiesToEven r (rounded? y)

/-- `y` is exactly `r`. -/
def IsExactly (r : ℝ) (y : τ) : Prop := ∃ v : ℚ, rounded? y = some (.finite v) ∧ (v : ℝ) = r

/-- `y` is within `n` ulps of the correctly rounded result for `r`. -/
def NearCR (n : ℝ) (r : ℝ) (y : τ) : Prop := CRDistance (format τ) n r (rounded? y)

end LibmFloat

/-! ## Outcomes and special cases -/

/-- The `errno` values of `<math.h>` (C 2018 §7.12.1; POSIX `math_errhandling`). -/
inductive Errno where
  /-- Domain error. -/
  | edom
  /-- Pole error or range error. -/
  | erange
  deriving DecidableEq, Repr

/-- One call of a libm entry point: the returned value, the IEEE exception
flags raised (under default, non-trapping handling) and the `errno` set, if
any. Value-only models use empty flags and no `errno`; the flag and `errno`
nodes then do not hold, and the value nodes are unaffected. -/
structure Outcome (τ : Type) where
  value : τ
  flags : Flags := {}
  errno : Option Errno := none

/-- A reference function without flags or `errno`, as an implementation. -/
def Outcome.pure {α τ : Type} (ref : α → τ) : α → Outcome τ := fun x => { value := ref x }

/-- The result a special case requires. -/
inductive Expect (τ : Type) where
  /-- Some NaN (Annex F leaves the payload unspecified). -/
  | nan
  /-- Exactly this encoding, including the sign of a zero or infinity. -/
  | bits (y : τ)
  /-- The correctly rounded value of a real constant, such as `π/2` for `atan(+∞)`. -/
  | near (r : ℝ)
  /-- No value requirement; the case only constrains flags and `errno`. -/
  | any

namespace Expect

variable {τ : Type} [LibmFloat τ]

/-- The returned encoding meets the expectation. -/
def Holds : Expect τ → τ → Prop
  | .nan, y => LibmFloat.isNaN y = true
  | .bits z, y => y = z
  | .near r, y => LibmFloat.CR r y
  | .any, _ => True

end Expect

/-- One special case of Annex F or POSIX: when `applies x` holds, the result
must meet `expect x`, the flags `raises` must be raised and, under
`MATH_ERRNO`, `errno` must be set to `errno`. -/
structure SpecialCase (α τ : Type) where
  /-- A short description, such as `"sin(±∞)"`. -/
  name : String
  applies : α → Bool
  expect : α → Expect τ
  raises : Flags := {}
  errno : Option Errno := none

/-! ## Function specifications -/

/-- The specification of one libm function with inputs `α` and result `τ`.
`exact x` is the exact mathematical result where the function has one to be
rounded; it is `none` on the inputs settled by special cases alone. -/
structure Spec (α τ : Type) where
  name : String
  exact : α → Option ℝ
  special : List (SpecialCase α τ)

namespace Spec

variable {α τ : Type} [LibmFloat τ] (S : Spec α τ) (impl : α → Outcome τ)

/-! ### (a) Special cases -/

/-- (a) Every applicable special case returns its required value. -/
def SpecialValues : Prop :=
  ∀ c ∈ S.special, ∀ x, c.applies x = true → (c.expect x).Holds (impl x).value

/-- (a) Every applicable special case raises its required flags. -/
def SpecialFlags : Prop :=
  ∀ c ∈ S.special, ∀ x, c.applies x = true → c.raises.Subset (impl x).flags

/-- (a) Every applicable special case sets its required `errno`. -/
def SpecialErrno : Prop :=
  ∀ c ∈ S.special, ∀ x, c.applies x = true → ∀ e, c.errno = some e → (impl x).errno = some e

/-- (a) All special-case requirements. -/
def Special : Prop := S.SpecialValues impl ∧ S.SpecialFlags impl ∧ S.SpecialErrno impl

/-! ### (b), (c) Error bounds -/

/-- (b) On the inputs `D`, results are within `k` ulps of the exact result. -/
def ErrorOn (D : Set α) (k : ℝ) : Prop :=
  ∀ x ∈ D, ∀ r, S.exact x = some r → LibmFloat.Close k r (impl x).value

/-- (c) Results are within `k` ulps of the exact result on every input. -/
def ErrorGlobal (k : ℝ) : Prop := S.ErrorOn impl Set.univ k

/-! ### (d) Sane bounds -/

/-- (d) Every result with an exact value is correctly rounded (≤ 1/2 ulp). -/
def CorrectlyRounded : Prop :=
  ∀ x r, S.exact x = some r → LibmFloat.CR r (impl x).value

/-- (d) Every result is within `n` ulps of the correctly rounded one
(glibc's `libm-test-ulps` measure). -/
def CRWithin (n : ℝ) : Prop :=
  ∀ x r, S.exact x = some r → LibmFloat.NearCR n r (impl x).value

/-- (d) Every result is exactly the exact result (for functions whose results
are always representable, such as `floor` or `fmod`). -/
def Exact : Prop :=
  ∀ x r, S.exact x = some r → LibmFloat.IsExactly r (impl x).value

end Spec

/-! ### (e) A fixed implementation -/

/-- (e) The implementation returns, bit for bit, the encodings of `ref`. -/
def BitExact {α τ : Type} (impl : α → Outcome τ) (ref : α → τ) : Prop := ∀ x, (impl x).value = ref x

/-- (e) On the inputs where the partial reference `ref` is defined, the
implementation returns its encodings (for references transcribed on a range). -/
def BitExactWhere {α τ : Type} (impl : α → Outcome τ) (ref : α → Option τ) : Prop :=
  ∀ x y, ref x = some y → (impl x).value = y

/-! ## Accuracy levels and combined problems -/

/-- The accuracy nodes of the lattice, from weakest to strongest. -/
inductive Accuracy where
  /-- No accuracy requirement: special cases only. -/
  | none
  /-- (c) Within `k` ulps of the exact result. -/
  | ulps (k : ℚ)
  /-- (d) Within `n` ulps of the correctly rounded result (glibc's measure). -/
  | glibc (n : ℕ)
  /-- (d) Correctly rounded. -/
  | correctlyRounded
  /-- (d) Exact. -/
  | exact
  deriving DecidableEq, Repr

/-- `a.Implies b`: the accuracy node `a` is at least as strong as `b`. Each case
is an edge proved in `Spec.accurate_mono` (`Lattice.Thms`). -/
def Accuracy.Implies : Accuracy → Accuracy → Prop
  | _, .none => True
  | .ulps k, .ulps k' => k ≤ k'
  | .glibc n, .ulps k => n = 0 ∧ 1 / 2 ≤ k
  | .glibc n, .glibc n' => n ≤ n'
  | .glibc n, .correctlyRounded => n = 0
  | .correctlyRounded, .ulps k => 1 / 2 ≤ k
  | .correctlyRounded, .glibc _ => True
  | .correctlyRounded, .correctlyRounded => True
  | .exact, .ulps k => 1 / 2 ≤ k
  | .exact, .glibc _ => True
  | .exact, .correctlyRounded => True
  | .exact, .exact => True
  | _, _ => False

namespace Spec

variable {α τ : Type} [LibmFloat τ] (S : Spec α τ) (impl : α → Outcome τ)

/-- The accuracy node named by `a`. -/
def Accurate : Accuracy → Prop
  | .none => True
  | .ulps k => S.ErrorGlobal impl k
  | .glibc n => S.CRWithin impl n
  | .correctlyRounded => S.CorrectlyRounded impl
  | .exact => S.Exact impl

/-- "Exports a valid `f` at accuracy `a`": the values, flags and `errno` of the
special cases, and the accuracy node `a`. -/
def Valid (a : Accuracy) : Prop := S.Special impl ∧ S.Accurate impl a

/-- The value-level part of `Valid`, for value-only models (Wasm, pure Lean). -/
def ValidValues (a : Accuracy) : Prop := S.SpecialValues impl ∧ S.Accurate impl a

end Spec

/-- One entry of a libm catalogue: a named function with its own input and
result types, and its validity problem at each accuracy level. Entries need
not return a float (`frexp` returns a pair), so validity is given per entry. -/
structure Entry where
  name : String
  In : Type
  Out : Type
  valid : Accuracy → (In → Outcome Out) → Prop

/-- An entry for a function specified by a `Spec`. -/
def Spec.entry {α τ : Type} [LibmFloat τ] (S : Spec α τ) : Entry where
  name := S.name
  In := α
  Out := τ
  valid a impl := S.Valid impl a

/-- An implementation of every catalogue entry. -/
abbrev LibmImpl := (e : Entry) → e.In → Outcome e.Out

/-- "Exports a valid libm at level `L`": every entry of the catalogue is valid
at its level `L e.name`. Each conjunct is a separate per-function problem. -/
def ValidLibm (catalogue : List Entry) (L : String → Accuracy) (impl : LibmImpl) : Prop :=
  ∀ e ∈ catalogue, e.valid (L e.name) (impl e)

end Silmaril.Numeric.Libm
