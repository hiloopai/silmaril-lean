module

public import Silmaril.Numeric.Ieee754.Flags.Outcome

/-!
# Denormal flushing hooks

IEEE 754-2019 requires gradual underflow. Several architectures also provide
non-conforming modes that replace subnormal values by zeros. This module gives
them as pure functions, parameterized so that each architecture profile states
its own rule:

* `flushInput` (denormals-are-zero) replaces a subnormal operand by the zero
  with the same sign bit, before the operation's outcome is computed. Whether a
  flushed operand raises a separate, non-IEEE status flag is left to the profile;
  `Datum.IsSubnormal` identifies the operands concerned.
* `FlushToZero` describes output flushing: when enabled and the exact result is
  tiny (under the profile's `Tininess` convention), the delivered result is the
  zero with the sign of the exact result and `raises` is signaled instead of the
  IEEE flags. `requiresUnderflowMasked` records whether flushing applies only
  when the underflow exception is masked.

`FlushToZero.maskedUnderflowInexact` is the rule stated in the Intel 64 and
IA-32 Architectures Software Developer's Manual, Vol. 1, §10.2.3.3
("Flush-To-Zero"): flushing applies only when underflow is masked, and it sets
the underflow and precision (inexact) flags. The theorems below show that these
are the flags the IEEE §7.5 underflow and §7.6 inexact tests assign to the
flushed delivery `deliverFlushed` (`maskedUnderflowInexact_raises_eq`), and that
the rule departs from default IEEE flags exactly on exact tiny results
(`roundingFlagsFlushed_eq_roundingFlags_iff`).

`RoundingStage.flushToZero` packages output flushing as a rounding stage for
`Outcome.flags`, and `flushInput` composes with every operation on operands.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

open Float.Model

/-! ## Input flushing -/

/-- A nonzero finite operand of magnitude below `2 ^ emin`. For decoded
operands this is exactly the subnormal class (§3.4). -/
def Datum.IsSubnormal (f : Format) : Datum → Prop
  | .finite _ value => value ≠ 0 ∧ |value| < 2 ^ emin f
  | _ => False

instance (f : Format) : DecidablePred (Datum.IsSubnormal f) := fun x =>
  match x with
  | .nan _ => isFalse id
  | .infinity _ => isFalse id
  | .finite _ value => inferInstanceAs (Decidable (value ≠ 0 ∧ |value| < 2 ^ emin f))

/-- Denormals-are-zero: replace a subnormal operand by the zero with its sign
bit. Other operands are unchanged. -/
def flushInput (f : Format) (x : Datum) : Datum :=
  match x with
  | .finite negative value => if value ≠ 0 ∧ |value| < 2 ^ emin f then .finite negative 0 else x
  | _ => x

theorem flushInput_of_subnormal (f : Format) {negative : Bool} {value : ℚ}
    (h : (Datum.finite negative value).IsSubnormal f) :
    flushInput f (.finite negative value) = .finite negative 0 := by
  have h' : value ≠ 0 ∧ |value| < 2 ^ emin f := h
  simp only [flushInput, h', ne_eq, not_false_eq_true, and_self, ↓reduceIte]

theorem flushInput_of_not_subnormal (f : Format) {x : Datum} (h : ¬ x.IsSubnormal f) :
    flushInput f x = x := by
  cases x with
  | nan s => rfl
  | infinity n => rfl
  | finite n v =>
    have h' : ¬ (v ≠ 0 ∧ |v| < 2 ^ emin f) := h
    simp only [flushInput, h', ↓reduceIte]

theorem flushInput_not_subnormal (f : Format) (x : Datum) : ¬ (flushInput f x).IsSubnormal f := by
  cases x with
  | nan s => exact id
  | infinity n => exact id
  | finite n v =>
    simp only [flushInput]
    split
    · simp [Datum.IsSubnormal]
    · assumption

@[simp] theorem flushInput_flushInput (f : Format) (x : Datum) :
    flushInput f (flushInput f x) = flushInput f x :=
  flushInput_of_not_subnormal f (flushInput_not_subnormal f x)

@[simp] theorem flushInput_isSignaling (f : Format) (x : Datum) :
    (flushInput f x).isSignaling = x.isSignaling := by
  cases x with
  | nan s => rfl
  | infinity n => rfl
  | finite n v =>
    simp only [flushInput]
    split <;> rfl

@[simp] theorem flushInput_isNaN (f : Format) (x : Datum) : (flushInput f x).isNaN = x.isNaN := by
  cases x with
  | nan s => rfl
  | infinity n => rfl
  | finite n v =>
    simp only [flushInput]
    split <;> rfl

/-- With denormals-are-zero, a finite nonzero dividend and a subnormal divisor
raise divide-by-zero rather than the flags of the exact quotient. -/
theorem div_flushInput_divisor (f : Format) (mode : RoundingMode) (tininess : Tininess)
    {nx ny : Bool} {a b : ℚ} (ha : a ≠ 0) (hb : (Datum.finite ny b).IsSubnormal f) :
    div f mode tininess (.finite nx a) (flushInput f (.finite ny b)) = divideByZero := by
  rw [flushInput_of_subnormal f hb]
  simp [div, ha, Datum.isSignaling]

/-! ## Output flushing -/

/-- An output-flushing control. When enabled and the exact result is tiny, the
delivered result is the zero with the sign of the exact result, and `raises` is
signaled in place of the IEEE flags. -/
structure FlushToZero where
  /-- Flushing applies only when the underflow exception is masked. -/
  requiresUnderflowMasked : Bool
  /-- The flags raised by a flushed result. -/
  raises : Flags
  deriving DecidableEq, Repr

/-- The Intel SDM Vol. 1 §10.2.3.3 rule: flushing applies only when underflow is
masked, and raises underflow and inexact. -/
def FlushToZero.maskedUnderflowInexact : FlushToZero where
  requiresUnderflowMasked := true
  raises := (Flags.singleton .underflow).union (Flags.singleton .inexact)

@[simp] theorem FlushToZero.maskedUnderflowInexact_raises :
    FlushToZero.maskedUnderflowInexact.raises = { underflow := true, inexact := true } := by
  decide

/-- Whether the control is active, given the underflow mask. -/
def FlushToZero.Enabled (ftz : FlushToZero) (underflowMasked : Bool) : Prop :=
  ftz.requiresUnderflowMasked = false ∨ underflowMasked = true

instance (ftz : FlushToZero) (underflowMasked : Bool) : Decidable (ftz.Enabled underflowMasked) :=
  inferInstanceAs (Decidable (_ ∨ _))

section Output

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- Rounding-stage flags with output flushing. -/
def roundingFlagsFlushed (ftz : FlushToZero) (underflowMasked : Bool) (f : Format)
    (mode : RoundingMode) (tininess : Tininess) (x : K) : Flags :=
  if ftz.Enabled underflowMasked ∧ Tiny f tininess mode x then ftz.raises
  else roundingFlags f mode tininess x

/-- The delivered result with output flushing. A flushed zero has the sign of
`x`, which `Rounded` does not record. -/
def deliverFlushed (ftz : FlushToZero) (underflowMasked : Bool) (f : Format)
    (mode : RoundingMode) (tininess : Tininess) (x : K) : Rounded K :=
  if ftz.Enabled underflowMasked ∧ Tiny f tininess mode x then .finite 0
  else deliver f mode x

omit [IsStrictOrderedRing K] in
theorem roundingFlagsFlushed_of_not_tiny (ftz : FlushToZero) (underflowMasked : Bool)
    (f : Format) (mode : RoundingMode) (tininess : Tininess) {x : K}
    (h : ¬ Tiny f tininess mode x) :
    roundingFlagsFlushed ftz underflowMasked f mode tininess x = roundingFlags f mode tininess x := by
  simp [roundingFlagsFlushed, h]

omit [IsStrictOrderedRing K] in
theorem roundingFlagsFlushed_of_not_enabled (ftz : FlushToZero) (underflowMasked : Bool)
    (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : K)
    (h : ¬ ftz.Enabled underflowMasked) :
    roundingFlagsFlushed ftz underflowMasked f mode tininess x = roundingFlags f mode tininess x := by
  simp [roundingFlagsFlushed, h]

omit [IsStrictOrderedRing K] in
theorem deliverFlushed_of_not_tiny (ftz : FlushToZero) (underflowMasked : Bool)
    (f : Format) (mode : RoundingMode) (tininess : Tininess) {x : K}
    (h : ¬ Tiny f tininess mode x) :
    deliverFlushed ftz underflowMasked f mode tininess x = deliver f mode x := by
  simp [deliverFlushed, h]

/-- A flushed result never replaces an overflow. -/
theorem not_overflows_of_flushed {ftz : FlushToZero} {underflowMasked : Bool} {f : Format}
    {mode : RoundingMode} {tininess : Tininess} {x : K}
    (h : ftz.Enabled underflowMasked ∧ Tiny f tininess mode x) : ¬ Overflows f mode x :=
  not_overflows_of_tiny h.2

/-- When underflow is masked, the x86 rule does not change the flags of a tiny
inexact result: IEEE default handling already raises exactly underflow and
inexact. -/
theorem roundingFlags_of_underflows {f : Format} {mode : RoundingMode} {tininess : Tininess} {x : K}
    (h : Underflows f tininess mode x) :
    roundingFlags f mode tininess x = FlushToZero.maskedUnderflowInexact.raises := by
  have hno := not_overflows_of_tiny h.1
  simp [roundingFlags, hno, h, h.2]

omit [IsStrictOrderedRing K] in
/-- The x86 flags are the IEEE classification of the delivered zero. Applying
the §7.6 inexact test (`Inexact`: the delivered result differs from the exact
one) and the §7.5 default underflow test (`Underflows`: tiny and inexact) to the
flushed delivery `deliverFlushed` gives exactly the flags the rule raises: a
tiny result is nonzero, so the delivered zero differs from it. -/
theorem maskedUnderflowInexact_raises_eq {f : Format} {mode : RoundingMode}
    {tininess : Tininess} {x : K} (h : Tiny f tininess mode x) :
    FlushToZero.maskedUnderflowInexact.raises =
      { underflow := decide (Tiny f tininess mode x ∧
          deliverFlushed .maskedUnderflowInexact true f mode tininess x ≠ .finite x)
        inexact := decide
          (deliverFlushed .maskedUnderflowInexact true f mode tininess x ≠ .finite x) } := by
  have hen : FlushToZero.maskedUnderflowInexact.Enabled true := Or.inr rfl
  have hne : (Rounded.finite (0 : K)) ≠ .finite x := by
    intro heq
    exact h.1 (Rounded.finite.inj heq).symm
  simp only [deliverFlushed, hen, h, and_self, ↓reduceIte, hne, ne_eq, not_false_eq_true,
    decide_true, FlushToZero.maskedUnderflowInexact_raises]

/-- With underflow masked, the x86 rule agrees with IEEE default flags except
on results that are tiny and exact, which it reports as underflow and inexact. -/
theorem roundingFlagsFlushed_eq_roundingFlags_iff (f : Format) (mode : RoundingMode)
    (tininess : Tininess) (x : K) :
    roundingFlagsFlushed .maskedUnderflowInexact true f mode tininess x =
        roundingFlags f mode tininess x ↔
      ¬ (Tiny f tininess mode x ∧ Representable f x) := by
  by_cases ht : Tiny f tininess mode x
  · have hen : FlushToZero.maskedUnderflowInexact.Enabled true := Or.inr rfl
    simp only [roundingFlagsFlushed, hen, ht, and_self, ↓reduceIte, true_and]
    rw [← not_inexact_iff_representable f mode x, not_not]
    constructor
    · intro heq
      have hu : (roundingFlags f mode tininess x).inexact = true := by
        rw [← heq]
        rfl
      exact decide_eq_true_iff.mp hu
    · intro hin
      exact (roundingFlags_of_underflows ⟨ht, hin⟩).symm
  · simp [roundingFlagsFlushed, ht]

/-- An exact tiny result raises nothing under IEEE default handling, and
underflow with inexact under the x86 flush rule. -/
theorem roundingFlagsFlushed_of_tiny_representable {f : Format} {mode : RoundingMode}
    {tininess : Tininess} {x : K} (ht : Tiny f tininess mode x) (hr : Representable f x) :
    roundingFlags f mode tininess x = Flags.empty ∧
      roundingFlagsFlushed .maskedUnderflowInexact true f mode tininess x =
        FlushToZero.maskedUnderflowInexact.raises := by
  refine ⟨roundingFlags_of_representable f mode tininess hr, ?_⟩
  have hen : FlushToZero.maskedUnderflowInexact.Enabled true := Or.inr rfl
  simp [roundingFlagsFlushed, hen, ht]

theorem coherent_maskedUnderflowInexact : Coherent FlushToZero.maskedUnderflowInexact.raises := by
  decide

theorem coherent_roundingFlagsFlushed {ftz : FlushToZero} (hc : Coherent ftz.raises)
    (underflowMasked : Bool) (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : K) :
    Coherent (roundingFlagsFlushed ftz underflowMasked f mode tininess x) := by
  unfold roundingFlagsFlushed
  split
  · exact hc
  · exact coherent_roundingFlags f mode tininess x

end Output

/-- Output flushing as a rounding stage for `Outcome.flags`. Square roots are
classified by `SqrtTiny`, which agrees with `Tiny` of the real square root. -/
def RoundingStage.flushToZero (ftz : FlushToZero) (underflowMasked : Bool) (f : Format)
    (mode : RoundingMode) (tininess : Tininess) : RoundingStage where
  finite := roundingFlagsFlushed ftz underflowMasked f mode tininess
  sqrt a :=
    if ftz.Enabled underflowMasked ∧ SqrtTiny f tininess mode a then ftz.raises
    else sqrtRoundingFlags f mode tininess a

/-- The square-root part of the flushing stage is output flushing applied to
the real square root. -/
theorem RoundingStage.flushToZero_sqrt (ftz : FlushToZero) (underflowMasked : Bool) (f : Format)
    (mode : RoundingMode) (tininess : Tininess) {a : ℚ} (ha : 0 ≤ a) :
    (RoundingStage.flushToZero ftz underflowMasked f mode tininess).sqrt a =
      roundingFlagsFlushed ftz underflowMasked f mode tininess (Real.sqrt (a : ℝ)) := by
  simp only [RoundingStage.flushToZero, roundingFlagsFlushed,
    propext (sqrtTiny_iff f tininess mode ha), sqrtRoundingFlags_eq f mode tininess ha]

/-- Without an enabled control, the flushing stage is the IEEE stage. -/
theorem RoundingStage.flushToZero_of_not_enabled (ftz : FlushToZero) (underflowMasked : Bool)
    (f : Format) (mode : RoundingMode) (tininess : Tininess) (h : ¬ ftz.Enabled underflowMasked) :
    RoundingStage.flushToZero ftz underflowMasked f mode tininess = .ieee f mode tininess := by
  simp only [RoundingStage.flushToZero, RoundingStage.ieee, h, false_and, ↓reduceIte]
  congr 1
  funext x
  exact roundingFlagsFlushed_of_not_enabled ftz underflowMasked f mode tininess x h

/-! ## Output flushing of outcomes -/

/-- The exact result of an outcome is tiny: a finite rational result or a square
root that `Tiny` (respectively `SqrtTiny`) classifies as tiny. Invalid, NaN,
infinite and divide-by-zero outcomes are never tiny. -/
def Outcome.IsTiny (f : Format) (tininess : Tininess) (mode : RoundingMode) : Outcome → Prop
  | .finite value => Tiny f tininess mode value
  | .sqrt radicand => SqrtTiny f tininess mode radicand
  | _ => False

instance (f : Format) (tininess : Tininess) (mode : RoundingMode) (o : Outcome) :
    Decidable (o.IsTiny f tininess mode) :=
  match o with
  | .invalid | .nan | .infinity _ | .divideByZero _ => isFalse id
  | .finite value => inferInstanceAs (Decidable (Tiny f tininess mode value))
  | .sqrt radicand => inferInstanceAs (Decidable (SqrtTiny f tininess mode radicand))

/-- Output flushing changes the flags of an outcome exactly when the control is
enabled and the exact result is tiny, and then raises `ftz.raises` alone. -/
theorem Outcome.flags_flushToZero (ftz : FlushToZero) (underflowMasked : Bool) (f : Format)
    (mode : RoundingMode) (tininess : Tininess) (o : Outcome) :
    o.flags (.flushToZero ftz underflowMasked f mode tininess) =
      if ftz.Enabled underflowMasked ∧ o.IsTiny f tininess mode then ftz.raises
      else o.flags (.ieee f mode tininess) := by
  cases o <;> simp only [Outcome.flags, Outcome.IsTiny, RoundingStage.flushToZero,
    RoundingStage.ieee, roundingFlagsFlushed, and_false, ite_false] <;> congr

/-- A nonzero integer is never tiny, under either tininess convention: its
magnitude is at least `1`, and `2 ^ emin ≤ 1`. -/
theorem not_tiny_intCast (f : Format) (tininess : Tininess) (mode : RoundingMode) (n : ℤ) :
    ¬ Tiny f tininess mode (n : ℚ) := by
  have hbefore : ¬ Tiny f .beforeRounding mode (n : ℚ) := by
    rintro ⟨hn, hsmall⟩
    simp only [tininessMagnitude] at hsmall
    have hn' : n ≠ 0 := by exact_mod_cast hn
    have h1 : (1 : ℚ) ≤ |(n : ℚ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn'
    have hemin : emin f ≤ 0 := by
      have := one_le_emax f
      unfold emin
      omega
    have h2 : (2 : ℚ) ^ emin f ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hemin
    linarith
  cases tininess with
  | beforeRounding => exact hbefore
  | afterRounding => exact fun h => hbefore (tiny_before_of_after h)

/-- Integer-to-float conversion is never flushed. -/
theorem not_isTiny_ofIntOutcome (f : Format) (tininess : Tininess) (mode : RoundingMode) (n : ℤ) :
    ¬ (ofIntOutcome n).IsTiny f tininess mode :=
  not_tiny_intCast f tininess mode n

end Silmaril.Numeric.Ieee754.FlagSpec
