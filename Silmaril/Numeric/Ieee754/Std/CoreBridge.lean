module

public import Silmaril.Numeric.Ieee754.Std.EncodingCorrect
public import Silmaril.Numeric.Ieee754.ArithmeticCorrectness

/-!
# Proved bridge: the `Float.Model` rounding engine computes the `Std` rounding

Lean core's `Float.Model` (through Silmaril's mode-parametric `Rounding.*`
functions and the `F32`/`F64` wrappers) and the `Std` core were written
independently. This module proves that they agree.

* `CoreBridge.mantissaRounds_eq_pick`: the significand specification
  `MantissaRounds` of `Ieee754.MantissaCorrectness` selects exactly the
  candidate that `Std.pick` selects, in all five rounding directions.
* `CoreBridge.value_roundUnpacked`: for every format and direction, the value of
  `Rounding.roundUnpacked` on any input with a rational value is the `Std` grid
  rounding (`Grid.roundMagQ`) of that value, with its sign. This is the rounding
  stage shared by every `Float.Model` operation, so the two rounding engines
  coincide on every finite value (signed zeros are identified by `value?`).
* `Interchange.finiteValue_eq`: the `F32`/`F64` decoder (`toRat?`) and the `Std`
  interchange decoder agree on every bit pattern.
* `F32.addWith_deliver` etc.: for finite operands and a result that does not
  overflow, the value of `F32.addWith mode` / `subWith` / `mulWith` / `fmaWith`
  (and of `F64`) is the value of *every* datum allowed by the `Std`
  specification `Deliver` of the exact sum / difference / product / fused
  product-sum, in every direction. Under round to nearest, ties to even, these
  are Lean core's `Float32.Model`/`Float.Model` operations (`F32.add_deliver`
  etc.), via the existing `addWith_rne` equalities.

The hypothesis `NoExponentOverflow` is the one of the existing correctness
theorems (`ArithmeticCorrectness`). Division and square root are covered by the
executable differential checks of `Std.Bridge`, not by a proof here.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754 Conformance Float.Model Float.Model.UnpackedFloat

namespace CoreBridge

/-- The `Std` sign of a `Float.Model` sign. -/
def negOf (s : Sign) : Bool := decide (s = .negative)

/-! ## Significand rounding -/

theorem nearest_cases {s : ℚ} (hs : 0 ≤ s) {k : ℕ} (h : NearestMagnitude s k) :
    k = ⌊s⌋₊ ∨ k = ⌈s⌉₊ := by
  have h1 := h ⌊s⌋₊
  have h2 := h ⌈s⌉₊
  have hf : (⌊s⌋₊ : ℚ) ≤ s := Nat.floor_le hs
  have hc : s ≤ (⌈s⌉₊ : ℚ) := Nat.le_ceil s
  rcases lt_trichotomy k ⌊s⌋₊ with hk | hk | hk
  · exfalso
    have : (k : ℚ) + 1 ≤ ⌊s⌋₊ := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h1
    linarith
  · exact Or.inl hk
  · right
    have hk' : ⌈s⌉₊ ≤ k := by
      rw [Nat.ceil_le]
      have : (⌊s⌋₊ : ℚ) + 1 ≤ k := by exact_mod_cast hk
      have := Nat.lt_floor_add_one s
      linarith
    rcases hk'.lt_or_eq with hlt | heq
    · exfalso
      have : (⌈s⌉₊ : ℚ) + 1 ≤ k := by exact_mod_cast hlt
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h2
      linarith
    · exact heq.symm

theorem lower_eq {s : ℚ} (hs : 0 ≤ s) {k : ℕ} (h : LowerMagnitude s k) : k = ⌊s⌋₊ :=
  le_antisymm (Nat.le_floor h.1) (h.2 _ (Nat.floor_le hs))

theorem upper_eq {s : ℚ} {k : ℕ} (h : UpperMagnitude s k) : k = ⌈s⌉₊ :=
  le_antisymm (h.2 _ (Nat.le_ceil s)) (Nat.ceil_le.mpr h.1)

/-- `MantissaRounds` selects the `Std.pick` candidate between floor and ceiling. -/
theorem mantissaRounds_eq_pick {mode : RoundingMode} {sign : Sign} {s : ℚ} (hs : 0 ≤ s)
    {k : ℕ} (h : MantissaRounds mode sign s k) :
    (k : ℚ) = pick mode (negOf sign) (⌊s⌋₊ % 2 = 0) s (⌊s⌋₊ : ℚ) (⌈s⌉₊ : ℚ) := by
  have hf : (⌊s⌋₊ : ℚ) ≤ s := Nat.floor_le hs
  have hc : s ≤ (⌈s⌉₊ : ℚ) := Nat.le_ceil s
  have hfc : (⌈s⌉₊ : ℚ) ≤ ⌊s⌋₊ + 1 := by
    have := Nat.ceil_le_floor_add_one s
    exact_mod_cast this
  have af : |s - (⌊s⌋₊ : ℚ)| = s - ⌊s⌋₊ := abs_of_nonneg (by linarith)
  have ac : |s - (⌈s⌉₊ : ℚ)| = ⌈s⌉₊ - s := by rw [abs_of_nonpos (by linarith)]; ring
  cases mode with
  | towardZero =>
    simp only [MantissaRounds] at h
    simp [pick, pickBy, lower_eq hs h]
  | towardPositive =>
    cases sign
    · have h' : LowerMagnitude s k := by simpa [MantissaRounds] using h
      simp [pick, pickBy, negOf, lower_eq hs h']
    · have h' : UpperMagnitude s k := by simpa [MantissaRounds] using h
      simp [pick, pickBy, negOf, upper_eq h']
  | towardNegative =>
    cases sign
    · have h' : UpperMagnitude s k := by simpa [MantissaRounds] using h
      simp [pick, pickBy, negOf, upper_eq h']
    · have h' : LowerMagnitude s k := by simpa [MantissaRounds] using h
      simp [pick, pickBy, negOf, lower_eq hs h']
  | nearestTiesToAway =>
    obtain ⟨hn, ht⟩ := h
    have n1 := hn ⌊s⌋₊
    have n2 := hn ⌈s⌉₊
    simp only [pick, pickBy]
    rcases nearest_cases hs hn with rfl | rfl
    · split_ifs with hlt
      · rfl
      · have := ht ⌈s⌉₊ (by rw [af, ac]; rw [af, ac] at n2; linarith)
        exact_mod_cast le_antisymm (Nat.floor_le_ceil s) this
    · split_ifs with hlt
      · rw [af, ac] at n1; linarith
      · rfl
  | nearestTiesToEven =>
    obtain ⟨hn, ht⟩ := h
    have n1 := hn ⌊s⌋₊
    have n2 := hn ⌈s⌉₊
    simp only [pick, pickBy]
    rcases nearest_cases hs hn with rfl | rfl
    · rw [af, ac] at n2
      split_ifs with hlt hgt hev
      · rfl
      · linarith
      · rfl
      · rcases ht ⌈s⌉₊ (by rw [af, ac]; linarith) with h | h
        · exact absurd h hev
        · rw [h]
    · rw [af, ac] at n1
      split_ifs with hlt hgt hev
      · linarith
      · rfl
      · rcases ht ⌊s⌋₊ (by rw [af, ac]; linarith) with h | h
        · -- both candidates even and distinct is impossible
          by_cases heq : ⌊s⌋₊ = ⌈s⌉₊
          · rw [heq]
          · exfalso
            have : ⌈s⌉₊ = ⌊s⌋₊ + 1 := by
              have := Nat.ceil_le_floor_add_one s
              have := Nat.floor_le_ceil s
              omega
            omega
        · rw [h]
      · rfl

/-- Scaling the exact value and both candidates by a positive factor commutes with `pick`. -/
theorem pick_scale (mode : RoundingMode) (neg : Bool) (E : Prop) [Decidable E] {x d u c : ℚ}
    (hc : 0 < c) : pick mode neg E x (d * c) (u * c) = pick mode neg E (x / c) d u * c := by
  unfold pick
  rw [pickBy_map (· * c)]
  have e1 : x - d * c = (x / c - d) * c := by field_simp
  have e2 : u * c - x = (u - x / c) * c := by field_simp
  have e3 : x - d * c < u * c - x ↔ x / c - d < u - x / c := by
    rw [e1, e2]; exact mul_lt_mul_iff_of_pos_right hc
  have e4 : u * c - x < x - d * c ↔ u - x / c < x / c - d := by
    rw [e1, e2]; exact mul_lt_mul_iff_of_pos_right hc
  exact pickBy_congr _ _ e3 e4 Iff.rfl _ _

/-! ## The rounding stage -/

/-- The `Std` grid of a `Float.Model` format: its precision and least exponent. -/
def coreGrid (fm : Format) : Grid := ⟨fm.mantissaBits, some fm.minExponent⟩

theorem floorLog2_dyadic {n : ℕ} (hn : 0 < n) (e : ℤ) :
    Grid.floorLog2 ((n : ℚ) * 2 ^ e) = (n.log2 : ℤ) + e := by
  have hx : (0 : ℚ) < (n : ℚ) * 2 ^ e := by positivity
  rw [Grid.floorLog2_eq hx]
  have hlo : (2 : ℚ) ^ n.log2 ≤ n := by exact_mod_cast Nat.log2_self_le (by omega)
  have hhi : (n : ℚ) < 2 ^ (n.log2 + 1) := by exact_mod_cast Nat.lt_log2_self
  apply Grid.log_eq_of_bounds hx
  · rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    exact mul_le_mul_of_nonneg_right hlo (by positivity)
  · rw [show (n.log2 : ℤ) + e + 1 = ((n.log2 + 1 : ℕ) : ℤ) + e by push_cast; ring,
      zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    exact mul_lt_mul_of_pos_right hhi (by positivity)

theorem qexpQ_coreGrid (fm : Format) {n : ℕ} (hn : 0 < n) (e : ℤ) :
    (coreGrid fm).qexpQ ((n : ℚ) * 2 ^ e) = fm.targetExponent (totalExponent n e) := by
  simp only [Grid.qexpQ, Grid.clamp, coreGrid, floorLog2_dyadic hn, Format.targetExponent,
    totalExponent]
  congr 1
  omega

/-- The value of a finite rounding is the `Std` grid rounding of the exact value. -/
theorem value_roundUnpacked_finite (fm : Format) (mode : RoundingMode) (sign : Sign) (n : ℕ)
    (e : ℤ) (hn : 0 < n) :
    value? (Rounding.roundUnpacked fm mode (.finite sign n e hn)) =
      some (Std.signed (negOf sign) ((coreGrid fm).roundMagQ mode (negOf sign) ((n : ℚ) * 2 ^ e))) := by
  obtain ⟨k, hk, hv⟩ := roundUnpacked_finite_correct fm mode sign n e hn
  rw [hv]
  congr 1
  set T := fm.targetExponent (totalExponent n e)
  have hT : (coreGrid fm).qexpQ ((n : ℚ) * 2 ^ e) = T := qexpQ_coreGrid fm hn e
  have hpos : (0 : ℚ) < 2 ^ T := zpow_pos (by norm_num) _
  have hs : 0 ≤ (n : ℚ) * 2 ^ e / 2 ^ T := by positivity
  have hpick := mantissaRounds_eq_pick hs hk
  have hround : (coreGrid fm).roundMagQ mode (negOf sign) ((n : ℚ) * 2 ^ e) = (k : ℚ) * 2 ^ T := by
    simp only [Grid.roundMagQ, hT]
    rw [pick_scale _ _ _ hpos, ← hpick]
  rw [hround]
  cases sign <;> simp [dyadic, Sign.apply, Std.signed, negOf]

theorem roundMagQ_zero (g : Grid) (mode : RoundingMode) (neg : Bool) : g.roundMagQ mode neg 0 = 0 := by
  simp [Grid.roundMagQ, pick_self]

/-- The rounding stage of `Float.Model`, for every format, direction and input
with a rational value, computes the `Std` rounding of that value. -/
theorem value_roundUnpacked (fm : Format) (mode : RoundingMode) (v : UnpackedFloat) {q : ℚ}
    (hq : value? v = some q) :
    value? (Rounding.roundUnpacked fm mode v) =
      some (Std.signed (decide (q < 0)) ((coreGrid fm).roundMagQ mode (decide (q < 0)) |q|)) := by
  cases v with
  | notANumber | infinity _ => simp [value?] at hq
  | zero sign =>
    have hq : q = 0 := by simpa [value?] using hq.symm
    subst hq
    obtain ⟨k, hk, hv⟩ := roundUnpacked_zero_correct fm mode sign
    rw [hv]
    have hk0 : k = 0 := by
      have := mantissaRounds_eq_pick (le_refl 0) (by simpa using hk)
      simpa [pick_self] using this
    subst hk0
    cases sign <;> simp [Std.signed, roundMagQ_zero, Sign.apply]
  | finite sign n e hn =>
    have hq : q = dyadic (sign.apply n) e := by simpa [value?] using hq.symm
    subst hq
    rw [value_roundUnpacked_finite]
    have hpos : (0 : ℚ) < (n : ℚ) * 2 ^ e := by positivity
    cases sign
    · have hneg : dyadic (Sign.negative.apply n) e < 0 := by
        simp only [dyadic, Sign.apply]; push_cast; nlinarith
      have habs : |dyadic (Sign.negative.apply n) e| = (n : ℚ) * 2 ^ e := by
        rw [abs_of_neg hneg]; simp [dyadic, Sign.apply]
      simp [hneg, habs, negOf]
    · have hnn : ¬ dyadic (Sign.positive.apply n) e < 0 := by
        simp only [dyadic, Sign.apply]; push_cast; exact not_lt.mpr hpos.le
      have habs : |dyadic (Sign.positive.apply n) e| = (n : ℚ) * 2 ^ e := by
        rw [abs_of_pos (by simpa [dyadic, Sign.apply] using hpos)]; simp [dyadic, Sign.apply]
      simp [hnn, habs, negOf]

/-! ## Decoders -/

/-- The value of a datum: the signed magnitude of a finite datum. -/
def datumValue? : Datum → Option ℚ
  | .fin s m => some (Std.signed s m)
  | _ => none

theorem signed_eq (neg : Bool) (q : ℚ) : Ieee754.signed neg q = Std.signed neg q := rfl

/-- The `F32`/`F64` field decoder and the `Std` interchange decoder agree on every
bit pattern (finite values; `none` for infinities and NaNs). -/
theorem finiteValue_eq (F : Interchange) (bias : ℤ) (hb : bias = ((2 ^ (F.w - 1) - 1 : ℕ) : ℤ))
    (n : ℕ) :
    finiteValue F.w F.t bias (decode F.w F.t n) =
      datumValue? (F.decode (Fields.ofNat F.encoding n)) := by
  have hs : (Fields.ofNat F.encoding n).sign = (field n (F.w + F.t) 1 == 1) := by
    simp only [Fields.ofNat, Interchange.encoding, field, Nat.testBit_eq_decide_div_mod_eq]
    rw [Bool.eq_iff_iff]; simp
  have he : (Fields.ofNat F.encoding n).exp = field n F.t F.w := rfl
  have hf : (Fields.ofNat F.encoding n).frac = field n 0 F.t := by
    simp [Fields.ofNat, Interchange.encoding, field]
  have hqmin : F.fmt.qmin = 1 - bias - F.t := by
    simp only [BinFormat.qmin, BinFormat.emin, Interchange.fmt, hb]; push_cast; ring
  generalize Fields.ofNat F.encoding n = b at hs he hf
  obtain ⟨sg, ex, fr⟩ := b
  simp only at hs he hf
  subst hs he hf
  simp only [decode]
  generalize field n F.t F.w = E
  generalize field n 0 F.t = M
  have h2 : (2 : ℚ) ^ (F.t : ℤ) ≠ 0 := zpow_ne_zero _ (by norm_num)
  unfold finiteValue Interchange.decode
  simp only [maxExponentField, Interchange.expMax, beq_iff_eq]
  have two : (2 : ℚ) ≠ 0 := by norm_num
  by_cases h1 : E = 2 ^ F.w - 1
  · simp only [h1, ite_true]
    split_ifs <;> rfl
  · by_cases h0 : E = 0
    · subst h0
      simp only [h1, ite_true, ite_false, datumValue?, signed_eq, hqmin]
      congr 2
      rw [zpow_sub₀ two, zpow_sub₀ two, zpow_sub₀ two, zpow_one, zpow_natCast]
      push_cast
      ring
    · simp only [h1, h0, ite_false, datumValue?, signed_eq, hqmin]
      congr 2
      rw [show (E : ℤ) - 1 + (1 - bias - (F.t : ℤ)) = ((E : ℤ) - bias) - (F.t : ℤ) by ring,
        zpow_sub₀ two, zpow_sub₀ two, zpow_natCast (2 : ℚ) F.t]
      push_cast
      field_simp
      rw [← zpow_add₀ two]
      congr 1
      ring

/-- Finite encodings are at most the largest finite magnitude. -/
theorem decode_fin_le (F : Interchange) (n : ℕ) {s : Bool} {m : ℚ}
    (h : F.decode (Fields.ofNat F.encoding n) = .fin s m) : m ≤ F.fmt.maxFinite := by
  set b := Fields.ofNat F.encoding n
  have hexp : b.exp < 2 ^ F.w := Nat.mod_lt _ (by positivity)
  have hfrac : b.frac < 2 ^ F.t := Nat.mod_lt _ (by positivity)
  have hw := F.two_le_pow
  have h2w := F.two_pow_w
  have hp : F.fmt.prec = F.t + 1 := rfl
  have hemax : (F.fmt.emax : ℤ) = ((2 ^ (F.w - 1) - 1 : ℕ) : ℤ) := rfl
  have hqmin : F.fmt.qmin = 1 - (F.fmt.emax : ℤ) - F.t := by
    simp only [BinFormat.qmin, BinFormat.emin, hp]; push_cast; ring
  have hmax : F.fmt.maxFinite = ((2 ^ (F.t + 1) - 1 : ℕ) : ℚ) * 2 ^ ((F.fmt.emax : ℤ) - F.t) := by
    unfold BinFormat.maxFinite
    rw [hp]
    push_cast [Nat.one_le_two_pow]
    congr 2
    ring
  have hpow : ∀ e : ℤ, e ≤ (F.fmt.emax : ℤ) - F.t → (2 : ℚ) ^ e ≤ 2 ^ ((F.fmt.emax : ℤ) - F.t) :=
    fun e he => zpow_le_zpow_right₀ (by norm_num) he
  unfold Interchange.decode at h
  rw [hmax]
  split_ifs at h with h1 h2
  · simp only [Datum.fin.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have hf : (b.frac : ℚ) ≤ ((2 ^ (F.t + 1) - 1 : ℕ) : ℚ) := by
      have : b.frac ≤ 2 ^ (F.t + 1) - 1 := by rw [pow_succ]; omega
      exact_mod_cast this
    apply mul_le_mul hf (hpow _ _) (by positivity) (by positivity)
    rw [hqmin]
    have : (1 : ℤ) ≤ F.fmt.emax := by exact_mod_cast F.fmt.one_le_emax
    omega
  · simp only [Datum.fin.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have hf : (((2 ^ F.t + b.frac : ℕ)) : ℚ) ≤ ((2 ^ (F.t + 1) - 1 : ℕ) : ℚ) := by
      have : 2 ^ F.t + b.frac ≤ 2 ^ (F.t + 1) - 1 := by rw [pow_succ]; omega
      exact_mod_cast this
    apply mul_le_mul hf (hpow _ _) (by positivity) (by positivity)
    rw [hqmin]
    have hne : b.exp ≠ 2 ^ F.w - 1 := h1
    have hle : b.exp ≤ 2 * (2 ^ (F.w - 1) - 1) := by omega
    have hle' : (b.exp : ℤ) ≤ 2 * (F.fmt.emax : ℤ) := by rw [hemax]; exact_mod_cast hle
    omega

/-! ## Delivery of a value computed by the core -/

theorem roundQ_fst (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode) (neg : Bool)
    (x : ℚ) : (roundQ f tin mode neg x).1 =
      if f.maxFinite < f.grid.roundMagQ mode neg x then overflowResult f mode neg
      else .fin neg (f.grid.roundMagQ mode neg x) := rfl

/-- The magnitude of a value given by an encoding is at most `maxFinite`. -/
theorem le_maxFinite_of_value (F : Interchange) (out : ℕ) {neg : Bool} {r : ℚ} (hr0 : 0 ≤ r)
    (hout : datumValue? (F.decode (Fields.ofNat F.encoding out)) = some (Std.signed neg r)) :
    r ≤ F.fmt.maxFinite := by
  cases hd : F.decode (Fields.ofNat F.encoding out) with
  | fin s m =>
    rw [hd] at hout
    simp only [datumValue?, Option.some.injEq] at hout
    have hm := decode_fin_le F out hd
    have hm0 : 0 ≤ m := F.encoding.decode_nonneg _ s m hd
    have habs : |Std.signed s m| = |Std.signed neg r| := by rw [hout]
    have e1 : |Std.signed s m| = m := by
      unfold Std.signed; split_ifs <;> simp [abs_of_nonneg hm0]
    have e2 : |Std.signed neg r| = r := by
      unfold Std.signed; split_ifs <;> simp [abs_of_nonneg hr0]
    rw [e1, e2] at habs
    rw [← habs]; exact hm
  | _ => simp [hd, datumValue?] at hout

theorem roundMagQ_nonneg (f : BinFormat) (mode : RoundingMode) (neg : Bool) {x : ℚ} (hx : 0 ≤ x) :
    0 ≤ f.grid.roundMagQ mode neg x :=
  Grid.rep_nonneg ((f.grid.roundMagQ_spec f.one_le_prec mode neg hx).rep (K := ℚ))

/-- Whatever datum the `Std` specification delivers for the exact outcome
`.num neg m` (of value `v`) has the value of an encoding `out` whose value is the
`Std` rounding of `v`. -/
theorem deliver_num_value (F : Interchange) {tin : TininessDetection} {mode : RoundingMode}
    {v : ℚ} {neg : Bool} {m : ℚ} {res : Datum} {fl : Flags} (out : ℕ)
    (hout : datumValue? (F.decode (Fields.ofNat F.encoding out)) =
      some (Std.signed (decide (v < 0)) (F.fmt.grid.roundMagQ mode (decide (v < 0)) |v|)))
    (hm : 0 ≤ m) (hv : Std.signed neg m = v)
    (h : Deliver F.fmt tin mode (.num neg m) res fl) :
    datumValue? res = datumValue? (F.decode (Fields.ofNat F.encoding out)) := by
  rw [hout]
  have hres := congrArg Prod.fst ((deliver_iff F.fmt tin mode _ res fl).mp h)
  simp only [deliverQ, abs_of_nonneg hm, roundQ_fst] at hres
  rcases hm.lt_or_eq with hm | rfl
  · -- a nonzero value: same sign and magnitude
    have hneg : decide (v < 0) = neg := by
      subst hv; cases neg <;> simp [Std.signed, hm, hm.le]
    have habs : |v| = m := by
      subst hv; cases neg <;> simp [Std.signed, abs_of_pos hm]
    rw [hneg, habs] at hout ⊢
    have hrle := le_maxFinite_of_value F out (roundMagQ_nonneg _ _ _ hm.le) hout
    simp only [not_lt.mpr hrle, ite_false] at hres
    subst hres
    rfl
  · have hv0 : v = 0 := by subst hv; cases neg <;> simp [Std.signed]
    subst hv0
    simp only [roundMagQ_zero, not_lt.mpr F.fmt.maxFinite_pos.le, ite_false] at hres
    subst hres
    simp [datumValue?, Std.signed, roundMagQ_zero]

theorem deliver_value (F : Interchange) {tin : TininessDetection} {mode : RoundingMode} {v : ℚ}
    {z : Bool} {res : Datum} {fl : Flags} (out : ℕ)
    (hout : datumValue? (F.decode (Fields.ofNat F.encoding out)) =
      some (Std.signed (decide (v < 0)) (F.fmt.grid.roundMagQ mode (decide (v < 0)) |v|)))
    (h : Deliver F.fmt tin mode (ofSigned v z) res fl) :
    datumValue? res = datumValue? (F.decode (Fields.ofNat F.encoding out)) := by
  unfold ofSigned at h
  split_ifs at h with hv
  · exact deliver_num_value F out hout le_rfl (by simp [Std.signed, hv]) h
  · refine deliver_num_value F out hout (abs_nonneg v) ?_ h
    by_cases hlt : v < 0
    · simp [Std.signed, hlt, abs_of_neg hlt]
    · simp [Std.signed, hlt, abs_of_nonneg (not_lt.mp hlt)]

theorem fin_of_value {d : Datum} {a : ℚ} (h : datumValue? d = some a) :
    ∃ s m, d = .fin s m ∧ Std.signed s m = a := by
  cases d with
  | fin s m => exact ⟨s, m, rfl, by simpa [datumValue?] using h⟩
  | _ => simp [datumValue?] at h

theorem signed_mul (a b : Bool) (m n : ℚ) :
    Std.signed (a ^^ b) (m * n) = Std.signed a m * Std.signed b n := by
  cases a <;> cases b <;> simp [Std.signed]

theorem signed_neg (b : Bool) (m : ℚ) : Std.signed (!b) m = -Std.signed b m := by
  cases b <;> simp [Std.signed]

/-- The bit-level results of a `Std` profile have the value of the specified datum,
when that value is finite. -/
theorem opSpec_value (F : Interchange) {P : NaNSpec} {tin : TininessDetection}
    {mode : RoundingMode} {ins : List Fields} {e : Exact ℚ} {out : Fields} {fl : Flags}
    (h : OpSpec F.encoding P tin mode ins e out fl) {q : ℚ}
    (hq : ∀ res fl', Deliver F.fmt tin mode e res fl' → datumValue? res = some q) :
    datumValue? (F.decode out) = some q := by
  obtain ⟨res, hd, hdec⟩ := Interchange.OpSpec.decode_out F h
  have hv := hq res fl hd
  obtain ⟨s, m, rfl, -⟩ := fin_of_value hv
  rw [hdec rfl]
  exact hv

end CoreBridge

/-! ## `F32` and `F64` -/

open CoreBridge

namespace CoreBridge

theorem coreGrid_binary32 : coreGrid Format.binary32 = Interchange.binary32.fmt.grid := by decide
theorem coreGrid_binary64 : coreGrid Format.binary64 = Interchange.binary64.fmt.grid := by decide

end CoreBridge


end Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754.Std Silmaril.Numeric.Ieee754.Std.CoreBridge
open Silmaril.Numeric.Ieee754.Conformance Float.Model Float.Model.UnpackedFloat

namespace Silmaril.Numeric.Ieee754.F32

/-- The `Std` fields of a `F32` encoding. -/
def toStd (x : F32) : Fields := Fields.ofNat Interchange.binary32.encoding x.bits.toNat

/-- `F32.toRat?` is the value of the `Std` decoding. -/
theorem toRat?_eq_std (x : F32) :
    x.toRat? = datumValue? (Interchange.binary32.decode x.toStd) :=
  finiteValue_eq Interchange.binary32 binary32Bias (by decide) x.bits.toNat

/-- A rounded result that does not overflow has the `Std` rounding of its exact value. -/
theorem packRounded_toRat? (mode : RoundingMode) (u : UnpackedFloat) {v : ℚ}
    (hv : value? u = some v)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode u)) :
    (⟨UInt32.ofBitVec (Rounding.packRounded .binary32 mode u)⟩ : F32).toRat? =
      some (Std.signed (decide (v < 0))
        (Interchange.binary32.fmt.grid.roundMagQ mode (decide (v < 0)) |v|)) := by
  rw [← value?_unpack_bits]
  change value? (UnpackedFloat.unpack .binary32 (Rounding.packRounded .binary32 mode u)) = _
  rw [unpack_packRounded _ _ _ inRange, value_roundUnpacked _ _ _ hv, coreGrid_binary32]

theorem std_fin {x : F32} {a : ℚ} (hx : x.toRat? = some a) :
    ∃ s m, Interchange.binary32.decode x.toStd = .fin s m ∧ Std.signed s m = a :=
  fin_of_value ((toRat?_eq_std x).symm.trans hx)

/-- `addWith mode` has the value of every result the `Std` specification allows for
the exact sum, when it does not overflow; for every rounding direction. -/
theorem addWith_deliver (mode : RoundingMode) (x y : F32) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode x.model.unpack y.model.unpack)))
    {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary32.fmt tin mode
      (exactAdd mode (Interchange.binary32.decode x.toStd) (Interchange.binary32.decode y.toStd))
      res fl) :
    datumValue? res = (addWith mode x y).toRat? := by
  have hcore := packRounded_toRat? mode _
    (value?_addExact mode ((value?_model_unpack32 x).trans hx) ((value?_model_unpack32 y).trans hy))
    inRange
  obtain ⟨sa, ma, hda, rfl⟩ := std_fin hx
  obtain ⟨sb, mb, hdb, rfl⟩ := std_fin hy
  rw [hda, hdb] at h
  simp only [exactAdd, nanOutcome, List.any, Datum.isNaN, Bool.or_false] at h
  change datumValue? res = (⟨UInt32.ofBitVec (Rounding.packRounded .binary32 mode _)⟩ : F32).toRat?
  rw [toRat?_eq_std] at hcore ⊢
  exact deliver_value _ _ hcore h


/-- `subWith mode` has the value of every result the `Std` specification allows for
the exact difference, when it does not overflow. -/
theorem subWith_deliver (mode : RoundingMode) (x y : F32) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode x.model.unpack y.model.unpack.neg)))
    {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary32.fmt tin mode
      (exactSub mode (Interchange.binary32.decode x.toStd) (Interchange.binary32.decode y.toStd))
      res fl) :
    datumValue? res = (subWith mode x y).toRat? := by
  have hcore := packRounded_toRat? mode _
    (value?_subExact mode ((value?_model_unpack32 x).trans hx) ((value?_model_unpack32 y).trans hy))
    inRange
  obtain ⟨sa, ma, hda, rfl⟩ := std_fin hx
  obtain ⟨sb, mb, hdb, rfl⟩ := std_fin hy
  rw [hda, hdb] at h
  simp only [exactSub, exactAdd, nanOutcome, List.any, Datum.isNaN, Datum.neg, Bool.or_false] at h
  rw [signed_neg, ← sub_eq_add_neg] at h
  change datumValue? res = (⟨UInt32.ofBitVec (Rounding.packRounded .binary32 mode _)⟩ : F32).toRat?
  rw [toRat?_eq_std] at hcore ⊢
  exact deliver_value _ _ hcore h

/-- `mulWith mode` has the value of every result the `Std` specification allows for
the exact product, when it does not overflow. -/
theorem mulWith_deliver (mode : RoundingMode) (x y : F32) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.mulExact x.model.unpack y.model.unpack)))
    {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary32.fmt tin mode
      (exactMul (Interchange.binary32.decode x.toStd) (Interchange.binary32.decode y.toStd)) res fl) :
    datumValue? res = (mulWith mode x y).toRat? := by
  have hcore := packRounded_toRat? mode _
    (value?_mulExact ((value?_model_unpack32 x).trans hx) ((value?_model_unpack32 y).trans hy))
    inRange
  obtain ⟨sa, ma, hda, rfl⟩ := std_fin hx
  obtain ⟨sb, mb, hdb, rfl⟩ := std_fin hy
  have ha0 := Interchange.binary32.encoding.decode_nonneg _ _ _ hda
  have hb0 := Interchange.binary32.encoding.decode_nonneg _ _ _ hdb
  rw [hda, hdb] at h
  simp only [exactMul, nanOutcome, List.any, Datum.isNaN, Bool.or_false] at h
  change datumValue? res = (⟨UInt32.ofBitVec (Rounding.packRounded .binary32 mode _)⟩ : F32).toRat?
  rw [toRat?_eq_std] at hcore ⊢
  exact deliver_num_value _ _ hcore (mul_nonneg ha0 hb0) (signed_mul _ _ _ _) h

/-- `fmaWith mode` has the value of every result the `Std` specification allows for
the exact `x * y + z` (one rounding), when it does not overflow; this holds for
either choice of the `fma(∞, 0, qNaN)` parameter. -/
theorem fmaWith_deliver (mode : RoundingMode) (x y z : F32) {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode (Rounding.mulExact x.model.unpack y.model.unpack) z.model.unpack)))
    (iz : FmaInfZeroQNaN) {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary32.fmt tin mode
      (exactFma iz mode (Interchange.binary32.decode x.toStd) (Interchange.binary32.decode y.toStd)
        (Interchange.binary32.decode z.toStd)) res fl) :
    datumValue? res = (fmaWith mode x y z).toRat? := by
  have hcore := packRounded_toRat? mode _
    (value?_fmaExact mode ((value?_model_unpack32 x).trans hx) ((value?_model_unpack32 y).trans hy)
      ((value?_model_unpack32 z).trans hz))
    inRange
  obtain ⟨sa, ma, hda, rfl⟩ := std_fin hx
  obtain ⟨sb, mb, hdb, rfl⟩ := std_fin hy
  obtain ⟨sc, mc, hdc, rfl⟩ := std_fin hz
  rw [hda, hdb, hdc] at h
  unfold exactFma at h
  simp only [nanOutcome, List.any, Datum.isNaN, Bool.or_false, Datum.isSignaling,
    Bool.false_eq_true, ite_false] at h
  rw [signed_mul] at h
  change datumValue? res = (⟨UInt32.ofBitVec (Rounding.packRounded .binary32 mode _)⟩ : F32).toRat?
  rw [toRat?_eq_std] at hcore ⊢
  exact deliver_value _ _ hcore h

/-! ### Lean core's `Float.Model` operations (round to nearest, ties to even) -/

theorem add_deliver (x y : F32) {a b : ℚ} (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : AddNoOverflow x y) {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary32.fmt tin .nearestTiesToEven
      (exactAdd .nearestTiesToEven (Interchange.binary32.decode x.toStd)
        (Interchange.binary32.decode y.toStd)) res fl) :
    datumValue? res = (add x y).toRat? := by
  rw [← addWith_rne]; exact addWith_deliver _ x y hx hy inRange h

theorem sub_deliver (x y : F32) {a b : ℚ} (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : SubNoOverflow x y) {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary32.fmt tin .nearestTiesToEven
      (exactSub .nearestTiesToEven (Interchange.binary32.decode x.toStd)
        (Interchange.binary32.decode y.toStd)) res fl) :
    datumValue? res = (sub x y).toRat? := by
  rw [← subWith_rne]; exact subWith_deliver _ x y hx hy inRange h

theorem mul_deliver (x y : F32) {a b : ℚ} (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : MulNoOverflow x y) {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary32.fmt tin .nearestTiesToEven
      (exactMul (Interchange.binary32.decode x.toStd) (Interchange.binary32.decode y.toStd)) res fl) :
    datumValue? res = (mul x y).toRat? := by
  rw [← mulWith_rne]; exact mulWith_deliver _ x y hx hy inRange h

theorem fma_deliver (x y z : F32) {a b c : ℚ} (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hz : z.toRat? = some c) (inRange : FmaNoOverflow x y z) (iz : FmaInfZeroQNaN)
    {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary32.fmt tin .nearestTiesToEven
      (exactFma iz .nearestTiesToEven (Interchange.binary32.decode x.toStd)
        (Interchange.binary32.decode y.toStd) (Interchange.binary32.decode z.toStd)) res fl) :
    datumValue? res = (fma x y z).toRat? := by
  rw [← fmaWith_rne]; exact fmaWith_deliver _ x y z hx hy hz inRange iz h

/-! ### Every `Std` profile computes the core value -/

/-- For every ISA profile (x86 SSE, x87 NaN rules, RISC-V, ...) and every rounding
direction, the executable `Std` sum has the value of `addWith`; under round to
nearest even, of Lean core's model. -/
theorem isa_add (I : Isa) (mode : RoundingMode) (x y : F32) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode x.model.unpack y.model.unpack))) :
    datumValue? (Interchange.binary32.decode
      (I.add Interchange.binary32.encoding mode x.toStd y.toStd).1) = (addWith mode x y).toRat? := by
  obtain ⟨q, hq⟩ : ∃ q, (addWith mode x y).toRat? = some q :=
    ⟨_, packRounded_toRat? mode _ (value?_addExact mode ((value?_model_unpack32 x).trans hx)
      ((value?_model_unpack32 y).trans hy)) inRange⟩
  rw [hq]
  exact opSpec_value _ (I.add_spec _ mode _ _)
    (fun _ _ hd => (addWith_deliver mode x y hx hy inRange hd).trans hq)

theorem isa_sub (I : Isa) (mode : RoundingMode) (x y : F32) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode x.model.unpack y.model.unpack.neg))) :
    datumValue? (Interchange.binary32.decode
      (I.sub Interchange.binary32.encoding mode x.toStd y.toStd).1) = (subWith mode x y).toRat? := by
  obtain ⟨q, hq⟩ : ∃ q, (subWith mode x y).toRat? = some q :=
    ⟨_, packRounded_toRat? mode _ (value?_subExact mode ((value?_model_unpack32 x).trans hx)
      ((value?_model_unpack32 y).trans hy)) inRange⟩
  rw [hq]
  exact opSpec_value _ (I.sub_spec _ mode _ _)
    (fun _ _ hd => (subWith_deliver mode x y hx hy inRange hd).trans hq)

theorem isa_mul (I : Isa) (mode : RoundingMode) (x y : F32) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.mulExact x.model.unpack y.model.unpack))) :
    datumValue? (Interchange.binary32.decode
      (I.mul Interchange.binary32.encoding mode x.toStd y.toStd).1) = (mulWith mode x y).toRat? := by
  obtain ⟨q, hq⟩ : ∃ q, (mulWith mode x y).toRat? = some q :=
    ⟨_, packRounded_toRat? mode _ (value?_mulExact ((value?_model_unpack32 x).trans hx)
      ((value?_model_unpack32 y).trans hy)) inRange⟩
  rw [hq]
  exact opSpec_value _ (I.mul_spec _ mode _ _)
    (fun _ _ hd => (mulWith_deliver mode x y hx hy inRange hd).trans hq)

theorem isa_fma (I : Isa) (mode : RoundingMode) (x y z : F32) {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode (Rounding.mulExact x.model.unpack y.model.unpack) z.model.unpack))) :
    datumValue? (Interchange.binary32.decode
      (I.fma Interchange.binary32.encoding mode x.toStd y.toStd z.toStd).1) =
      (fmaWith mode x y z).toRat? := by
  obtain ⟨q, hq⟩ : ∃ q, (fmaWith mode x y z).toRat? = some q :=
    ⟨_, packRounded_toRat? mode _ (value?_fmaExact mode ((value?_model_unpack32 x).trans hx)
      ((value?_model_unpack32 y).trans hy) ((value?_model_unpack32 z).trans hz)) inRange⟩
  rw [hq]
  exact opSpec_value _ (I.fma_spec _ mode _ _ _)
    (fun _ _ hd => (fmaWith_deliver mode x y z hx hy hz inRange _ hd).trans hq)

/-- Lean core's model addition agrees in value with the x86 SSE profile. -/
theorem x86SSE_add_eq_core (x y : F32) {a b : ℚ} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (inRange : AddNoOverflow x y) :
    datumValue? (Interchange.binary32.decode
      (Isa.x86SSE.add Interchange.binary32.encoding .nearestTiesToEven x.toStd y.toStd).1) =
      (add x y).toRat? := by
  rw [← addWith_rne]; exact isa_add _ _ x y hx hy inRange

end Silmaril.Numeric.Ieee754.F32

namespace Silmaril.Numeric.Ieee754.F64

/-- The `Std` fields of a `F64` encoding. -/
def toStd (x : F64) : Fields := Fields.ofNat Interchange.binary64.encoding x.bits.toNat

/-- `F64.toRat?` is the value of the `Std` decoding. -/
theorem toRat?_eq_std (x : F64) :
    x.toRat? = datumValue? (Interchange.binary64.decode x.toStd) :=
  finiteValue_eq Interchange.binary64 binary64Bias (by decide) x.bits.toNat

/-- A rounded result that does not overflow has the `Std` rounding of its exact value. -/
theorem packRounded_toRat? (mode : RoundingMode) (u : UnpackedFloat) {v : ℚ}
    (hv : value? u = some v)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode u)) :
    (⟨UInt64.ofBitVec (Rounding.packRounded .binary64 mode u)⟩ : F64).toRat? =
      some (Std.signed (decide (v < 0))
        (Interchange.binary64.fmt.grid.roundMagQ mode (decide (v < 0)) |v|)) := by
  rw [← value?_unpack_bits]
  change value? (UnpackedFloat.unpack .binary64 (Rounding.packRounded .binary64 mode u)) = _
  rw [unpack_packRounded _ _ _ inRange, value_roundUnpacked _ _ _ hv, coreGrid_binary64]

theorem std_fin {x : F64} {a : ℚ} (hx : x.toRat? = some a) :
    ∃ s m, Interchange.binary64.decode x.toStd = .fin s m ∧ Std.signed s m = a :=
  fin_of_value ((toRat?_eq_std x).symm.trans hx)

/-- `addWith mode` has the value of every result the `Std` specification allows for
the exact sum, when it does not overflow; for every rounding direction. -/
theorem addWith_deliver (mode : RoundingMode) (x y : F64) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode x.model.unpack y.model.unpack)))
    {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary64.fmt tin mode
      (exactAdd mode (Interchange.binary64.decode x.toStd) (Interchange.binary64.decode y.toStd))
      res fl) :
    datumValue? res = (addWith mode x y).toRat? := by
  have hcore := packRounded_toRat? mode _
    (value?_addExact mode ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy))
    inRange
  obtain ⟨sa, ma, hda, rfl⟩ := std_fin hx
  obtain ⟨sb, mb, hdb, rfl⟩ := std_fin hy
  rw [hda, hdb] at h
  simp only [exactAdd, nanOutcome, List.any, Datum.isNaN, Bool.or_false] at h
  change datumValue? res = (⟨UInt64.ofBitVec (Rounding.packRounded .binary64 mode _)⟩ : F64).toRat?
  rw [toRat?_eq_std] at hcore ⊢
  exact deliver_value _ _ hcore h


/-- `subWith mode` has the value of every result the `Std` specification allows for
the exact difference, when it does not overflow. -/
theorem subWith_deliver (mode : RoundingMode) (x y : F64) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode x.model.unpack y.model.unpack.neg)))
    {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary64.fmt tin mode
      (exactSub mode (Interchange.binary64.decode x.toStd) (Interchange.binary64.decode y.toStd))
      res fl) :
    datumValue? res = (subWith mode x y).toRat? := by
  have hcore := packRounded_toRat? mode _
    (value?_subExact mode ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy))
    inRange
  obtain ⟨sa, ma, hda, rfl⟩ := std_fin hx
  obtain ⟨sb, mb, hdb, rfl⟩ := std_fin hy
  rw [hda, hdb] at h
  simp only [exactSub, exactAdd, nanOutcome, List.any, Datum.isNaN, Datum.neg, Bool.or_false] at h
  rw [signed_neg, ← sub_eq_add_neg] at h
  change datumValue? res = (⟨UInt64.ofBitVec (Rounding.packRounded .binary64 mode _)⟩ : F64).toRat?
  rw [toRat?_eq_std] at hcore ⊢
  exact deliver_value _ _ hcore h

/-- `mulWith mode` has the value of every result the `Std` specification allows for
the exact product, when it does not overflow. -/
theorem mulWith_deliver (mode : RoundingMode) (x y : F64) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.mulExact x.model.unpack y.model.unpack)))
    {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary64.fmt tin mode
      (exactMul (Interchange.binary64.decode x.toStd) (Interchange.binary64.decode y.toStd)) res fl) :
    datumValue? res = (mulWith mode x y).toRat? := by
  have hcore := packRounded_toRat? mode _
    (value?_mulExact ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy))
    inRange
  obtain ⟨sa, ma, hda, rfl⟩ := std_fin hx
  obtain ⟨sb, mb, hdb, rfl⟩ := std_fin hy
  have ha0 := Interchange.binary64.encoding.decode_nonneg _ _ _ hda
  have hb0 := Interchange.binary64.encoding.decode_nonneg _ _ _ hdb
  rw [hda, hdb] at h
  simp only [exactMul, nanOutcome, List.any, Datum.isNaN, Bool.or_false] at h
  change datumValue? res = (⟨UInt64.ofBitVec (Rounding.packRounded .binary64 mode _)⟩ : F64).toRat?
  rw [toRat?_eq_std] at hcore ⊢
  exact deliver_num_value _ _ hcore (mul_nonneg ha0 hb0) (signed_mul _ _ _ _) h

/-- `fmaWith mode` has the value of every result the `Std` specification allows for
the exact `x * y + z` (one rounding), when it does not overflow; this holds for
either choice of the `fma(∞, 0, qNaN)` parameter. -/
theorem fmaWith_deliver (mode : RoundingMode) (x y z : F64) {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode (Rounding.mulExact x.model.unpack y.model.unpack) z.model.unpack)))
    (iz : FmaInfZeroQNaN) {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary64.fmt tin mode
      (exactFma iz mode (Interchange.binary64.decode x.toStd) (Interchange.binary64.decode y.toStd)
        (Interchange.binary64.decode z.toStd)) res fl) :
    datumValue? res = (fmaWith mode x y z).toRat? := by
  have hcore := packRounded_toRat? mode _
    (value?_fmaExact mode ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy)
      ((value?_model_unpack64 z).trans hz))
    inRange
  obtain ⟨sa, ma, hda, rfl⟩ := std_fin hx
  obtain ⟨sb, mb, hdb, rfl⟩ := std_fin hy
  obtain ⟨sc, mc, hdc, rfl⟩ := std_fin hz
  rw [hda, hdb, hdc] at h
  unfold exactFma at h
  simp only [nanOutcome, List.any, Datum.isNaN, Bool.or_false, Datum.isSignaling,
    Bool.false_eq_true, ite_false] at h
  rw [signed_mul] at h
  change datumValue? res = (⟨UInt64.ofBitVec (Rounding.packRounded .binary64 mode _)⟩ : F64).toRat?
  rw [toRat?_eq_std] at hcore ⊢
  exact deliver_value _ _ hcore h

/-! ### Lean core's `Float.Model` operations (round to nearest, ties to even) -/

theorem add_deliver (x y : F64) {a b : ℚ} (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : AddNoOverflow x y) {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary64.fmt tin .nearestTiesToEven
      (exactAdd .nearestTiesToEven (Interchange.binary64.decode x.toStd)
        (Interchange.binary64.decode y.toStd)) res fl) :
    datumValue? res = (add x y).toRat? := by
  rw [← addWith_rne]; exact addWith_deliver _ x y hx hy inRange h

theorem sub_deliver (x y : F64) {a b : ℚ} (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : SubNoOverflow x y) {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary64.fmt tin .nearestTiesToEven
      (exactSub .nearestTiesToEven (Interchange.binary64.decode x.toStd)
        (Interchange.binary64.decode y.toStd)) res fl) :
    datumValue? res = (sub x y).toRat? := by
  rw [← subWith_rne]; exact subWith_deliver _ x y hx hy inRange h

theorem mul_deliver (x y : F64) {a b : ℚ} (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : MulNoOverflow x y) {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary64.fmt tin .nearestTiesToEven
      (exactMul (Interchange.binary64.decode x.toStd) (Interchange.binary64.decode y.toStd)) res fl) :
    datumValue? res = (mul x y).toRat? := by
  rw [← mulWith_rne]; exact mulWith_deliver _ x y hx hy inRange h

theorem fma_deliver (x y z : F64) {a b c : ℚ} (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hz : z.toRat? = some c) (inRange : FmaNoOverflow x y z) (iz : FmaInfZeroQNaN)
    {tin : TininessDetection} {res : Datum} {fl : Flags}
    (h : Deliver Interchange.binary64.fmt tin .nearestTiesToEven
      (exactFma iz .nearestTiesToEven (Interchange.binary64.decode x.toStd)
        (Interchange.binary64.decode y.toStd) (Interchange.binary64.decode z.toStd)) res fl) :
    datumValue? res = (fma x y z).toRat? := by
  rw [← fmaWith_rne]; exact fmaWith_deliver _ x y z hx hy hz inRange iz h

/-! ### Every `Std` profile computes the core value -/

/-- For every ISA profile (x86 SSE, x87 NaN rules, RISC-V, ...) and every rounding
direction, the executable `Std` sum has the value of `addWith`; under round to
nearest even, of Lean core's model. -/
theorem isa_add (I : Isa) (mode : RoundingMode) (x y : F64) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode x.model.unpack y.model.unpack))) :
    datumValue? (Interchange.binary64.decode
      (I.add Interchange.binary64.encoding mode x.toStd y.toStd).1) = (addWith mode x y).toRat? := by
  obtain ⟨q, hq⟩ : ∃ q, (addWith mode x y).toRat? = some q :=
    ⟨_, packRounded_toRat? mode _ (value?_addExact mode ((value?_model_unpack64 x).trans hx)
      ((value?_model_unpack64 y).trans hy)) inRange⟩
  rw [hq]
  exact opSpec_value _ (I.add_spec _ mode _ _)
    (fun _ _ hd => (addWith_deliver mode x y hx hy inRange hd).trans hq)

theorem isa_sub (I : Isa) (mode : RoundingMode) (x y : F64) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode x.model.unpack y.model.unpack.neg))) :
    datumValue? (Interchange.binary64.decode
      (I.sub Interchange.binary64.encoding mode x.toStd y.toStd).1) = (subWith mode x y).toRat? := by
  obtain ⟨q, hq⟩ : ∃ q, (subWith mode x y).toRat? = some q :=
    ⟨_, packRounded_toRat? mode _ (value?_subExact mode ((value?_model_unpack64 x).trans hx)
      ((value?_model_unpack64 y).trans hy)) inRange⟩
  rw [hq]
  exact opSpec_value _ (I.sub_spec _ mode _ _)
    (fun _ _ hd => (subWith_deliver mode x y hx hy inRange hd).trans hq)

theorem isa_mul (I : Isa) (mode : RoundingMode) (x y : F64) {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.mulExact x.model.unpack y.model.unpack))) :
    datumValue? (Interchange.binary64.decode
      (I.mul Interchange.binary64.encoding mode x.toStd y.toStd).1) = (mulWith mode x y).toRat? := by
  obtain ⟨q, hq⟩ : ∃ q, (mulWith mode x y).toRat? = some q :=
    ⟨_, packRounded_toRat? mode _ (value?_mulExact ((value?_model_unpack64 x).trans hx)
      ((value?_model_unpack64 y).trans hy)) inRange⟩
  rw [hq]
  exact opSpec_value _ (I.mul_spec _ mode _ _)
    (fun _ _ hd => (mulWith_deliver mode x y hx hy inRange hd).trans hq)

theorem isa_fma (I : Isa) (mode : RoundingMode) (x y z : F64) {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode (Rounding.mulExact x.model.unpack y.model.unpack) z.model.unpack))) :
    datumValue? (Interchange.binary64.decode
      (I.fma Interchange.binary64.encoding mode x.toStd y.toStd z.toStd).1) =
      (fmaWith mode x y z).toRat? := by
  obtain ⟨q, hq⟩ : ∃ q, (fmaWith mode x y z).toRat? = some q :=
    ⟨_, packRounded_toRat? mode _ (value?_fmaExact mode ((value?_model_unpack64 x).trans hx)
      ((value?_model_unpack64 y).trans hy) ((value?_model_unpack64 z).trans hz)) inRange⟩
  rw [hq]
  exact opSpec_value _ (I.fma_spec _ mode _ _ _)
    (fun _ _ hd => (fmaWith_deliver mode x y z hx hy hz inRange _ hd).trans hq)

/-- Lean core's model addition agrees in value with the x86 SSE profile. -/
theorem x86SSE_add_eq_core (x y : F64) {a b : ℚ} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (inRange : AddNoOverflow x y) :
    datumValue? (Interchange.binary64.decode
      (Isa.x86SSE.add Interchange.binary64.encoding .nearestTiesToEven x.toStd y.toStd).1) =
      (add x y).toRat? := by
  rw [← addWith_rne]; exact isa_add _ _ x y hx hy inRange

end Silmaril.Numeric.Ieee754.F64

