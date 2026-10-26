module

public import Silmaril.Numeric.Ieee754.Environment
public import Mathlib.Data.Int.Log
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Correct rounding onto a binary grid: specification and implementation

This module is the arithmetic heart of the `Std` IEEE 754 core.

*Specification.* A `Grid` fixes a precision `p` (number of significand bits)
and an optional least quantum exponent. Its representable magnitudes are
`n * 2^e` with `n < 2^p` and `e` admitted by the bound (`Grid.Rep`); there is no
largest exponent, as required by IEEE 754-2019 §4.3 ("as if with unbounded
exponent range"), and overflow is decided afterwards. For a magnitude `x ≥ 0`
in any ordered field with a floor:

* `Grid.IsDown x d`: `d` is the greatest representable magnitude `≤ x`;
* `Grid.IsUp x u`: `u` is the least representable magnitude `≥ x`;
* `Grid.RoundMag mode neg x r`: `r` is chosen from `d` and `u` by the rounding
  direction (§4.3.1, §4.3.2) for an exact value of sign `neg` and magnitude `x`.
  Ties to even pick the candidate whose integral significand at the quantum of
  `x` is even (§4.3.1: "the one with an even least significant digit").

The specification is order-theoretic: `IsDown` and `IsUp` quantify over every
representable magnitude, and they determine `r` uniquely (`RoundMag.unique`).

*Implementation.* `Grid.roundMagQ` computes the binary exponent of a rational
with `Nat.log2`, scales to the quantum, and takes a floor and a ceiling.
`Grid.roundMagQ_spec` proves that it meets the specification for every grid,
direction, sign and nonnegative rational, so the executable rounder *is* the
specified one. The generic lemma `Grid.roundMag_floor_ceil` is stated over any
`FloorRing` field, so irrational exact values (square roots, in `ℝ`) use the
same specification.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

/-- A binary precision with an optional least quantum exponent. `lo = none` is
the grid with unbounded exponent range in both directions (used for tininess
detection after rounding, IEEE 754-2019 §7.5). -/
structure Grid where
  prec : ℕ
  lo : Option ℤ
  deriving DecidableEq, Repr

/-- The direction choice between the round-down candidate `d` and the round-up
candidate `u` of a value of sign `neg`, given the decisions `lt` (the exact value
is nearer to `d`), `gt` (nearer to `u`) and `even` (`d` has an even integral
significand). -/
def pickBy {K : Type*} (mode : RoundingMode) (neg : Bool) (lt gt even : Prop) [Decidable lt]
    [Decidable gt] [Decidable even] (d u : K) : K :=
  match mode with
  | .towardZero => d
  | .towardPositive => if neg then d else u
  | .towardNegative => if neg then u else d
  | .nearestTiesToAway => if lt then d else u
  | .nearestTiesToEven => if lt then d else if gt then u else if even then d else u

/-- The tie-breaking and direction choice between the round-down candidate `d`
and the round-up candidate `u` of the magnitude `x` of a value of sign `neg`.
`evenDown` says that `d` has an even integral significand. -/
def pick {K : Type*} [LinearOrder K] [Sub K] (mode : RoundingMode) (neg : Bool)
    (evenDown : Prop) [Decidable evenDown] (x d u : K) : K :=
  pickBy mode neg (x - d < u - x) (u - x < x - d) evenDown d u

theorem pickBy_map {K L : Type*} (φ : K → L) (mode : RoundingMode) (neg : Bool)
    (lt gt even : Prop) [Decidable lt] [Decidable gt] [Decidable even] (d u : K) :
    φ (pickBy mode neg lt gt even d u) = pickBy mode neg lt gt even (φ d) (φ u) := by
  cases mode <;> simp only [pickBy] <;> (try split_ifs) <;> rfl

theorem pickBy_congr {K : Type*} (mode : RoundingMode) (neg : Bool)
    {lt gt even lt' gt' even' : Prop} [Decidable lt] [Decidable gt] [Decidable even]
    [Decidable lt'] [Decidable gt'] [Decidable even'] (h1 : lt ↔ lt') (h2 : gt ↔ gt')
    (h3 : even ↔ even') (d u : K) :
    pickBy mode neg lt gt even d u = pickBy mode neg lt' gt' even' d u := by
  cases mode <;> simp only [pickBy, h1, h2, h3]

theorem pickBy_self {K : Type*} (mode : RoundingMode) (neg : Bool)
    (lt gt even : Prop) [Decidable lt] [Decidable gt] [Decidable even] (d : K) :
    pickBy mode neg lt gt even d d = d := by
  cases mode <;> simp only [pickBy] <;> (try split_ifs) <;> rfl

theorem pickBy_cases {K : Type*} (mode : RoundingMode) (neg : Bool)
    (lt gt even : Prop) [Decidable lt] [Decidable gt] [Decidable even] (d u : K) :
    pickBy mode neg lt gt even d u = d ∨ pickBy mode neg lt gt even d u = u := by
  cases mode <;> simp only [pickBy] <;> (try split_ifs) <;> simp

theorem pick_self {K : Type*} [LinearOrder K] [Sub K] (mode : RoundingMode) (neg : Bool)
    (evenDown : Prop) [Decidable evenDown] (x d : K) :
    pick mode neg evenDown x d d = d := by
  cases mode <;> simp [pick, pickBy]

namespace Grid

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- The exponent `e` is allowed by the grid's lower bound. -/
def Admits (g : Grid) (e : ℤ) : Prop := ∀ l ∈ g.lo, l ≤ e

/-- Raise an exponent to the grid's lower bound. -/
def clamp (g : Grid) (e : ℤ) : ℤ :=
  match g.lo with
  | none => e
  | some l => max e l

/-- Representable magnitudes: `n * 2^e` with `n < 2^p`, `e` admitted. -/
def Rep (g : Grid) (r : K) : Prop :=
  ∃ n : ℕ, ∃ e : ℤ, n < 2 ^ g.prec ∧ g.Admits e ∧ r = n * (2 : K) ^ e

/-- `d` is the greatest representable magnitude at most `x`. -/
def IsDown (g : Grid) (x d : K) : Prop :=
  g.Rep d ∧ d ≤ x ∧ ∀ c : K, g.Rep c → c ≤ x → c ≤ d

/-- `u` is the least representable magnitude at least `x`. -/
def IsUp (g : Grid) (x u : K) : Prop :=
  g.Rep u ∧ x ≤ u ∧ ∀ c : K, g.Rep c → x ≤ c → u ≤ c

/-- The quantum exponent of a positive magnitude `x`: the exponent of the unit
in the last place of `p`-digit numbers in the binade of `x`, raised to the
grid's bound (IEEE 754-2019 §2.1 "quantum"). -/
noncomputable def qexp (g : Grid) (x : K) : ℤ := g.clamp (Int.log 2 x - ((g.prec : ℤ) - 1))

/-- Specification of rounding the magnitude `x ≥ 0` of a value of sign `neg`. -/
def RoundMag (g : Grid) (mode : RoundingMode) (neg : Bool) (x r : K) : Prop :=
  ∃ d u : K, g.IsDown x d ∧ g.IsUp x u ∧
    r = pick mode neg (⌊x / (2 : K) ^ g.qexp x⌋₊ % 2 = 0) x d u

theorem admits_clamp (g : Grid) (e : ℤ) : g.Admits (g.clamp e) := by
  intro l hl
  unfold clamp
  rw [Option.mem_def] at hl
  simp [hl]

theorem le_clamp (g : Grid) (e : ℤ) : e ≤ g.clamp e := by
  unfold clamp
  cases g.lo <;> simp

theorem clamp_eq_of_lt (g : Grid) {e e' : ℤ} (he' : g.Admits e') (hlt : e' < g.clamp e) :
    g.clamp e = e := by
  unfold clamp at hlt ⊢
  cases h : g.lo with
  | none => rfl
  | some l =>
    have := he' l (by simp [h])
    simp only [h] at hlt ⊢
    omega

theorem Admits.mono {g : Grid} {e e' : ℤ} (he : g.Admits e) (hle : e ≤ e') : g.Admits e' :=
  fun l hl => le_trans (he l hl) hle

theorem rep_nonneg {g : Grid} {c : K} (hc : g.Rep c) : 0 ≤ c := by
  obtain ⟨n, e, -, -, rfl⟩ := hc
  positivity

theorem rep_zero (g : Grid) : g.Rep (0 : K) :=
  ⟨0, g.clamp 0, Nat.two_pow_pos _, g.admits_clamp 0, by simp⟩

/-- Integer multiples `k * 2^q` with `k ≤ 2^p` are representable when `q` is
admitted; `k = 2^p` uses the next exponent (precision `p ≥ 1`). -/
theorem rep_mul (g : Grid) (hp : 1 ≤ g.prec) {k : ℕ} (hk : k ≤ 2 ^ g.prec) {q : ℤ}
    (hq : g.Admits q) : g.Rep ((k : K) * (2 : K) ^ q) := by
  rcases Nat.lt_or_eq_of_le hk with hk | hk
  · exact ⟨k, q, hk, hq, rfl⟩
  · refine ⟨2 ^ (g.prec - 1), q + 1, Nat.pow_lt_pow_right (by norm_num) (by omega),
      hq.mono (by omega), ?_⟩
    subst hk
    rw [zpow_add₀ (by norm_num : (2 : K) ≠ 0), zpow_one]
    push_cast
    rw [show g.prec = (g.prec - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring

section Positive

variable (g : Grid) {x : K}

theorem two_zpow_log_le (hx : 0 < x) : (2 : K) ^ Int.log 2 x ≤ x := by
  have := Int.zpow_log_le_self (R := K) (b := 2) (by norm_num) hx
  simpa using this

theorem lt_two_zpow_log_succ (x : K) : x < (2 : K) ^ (Int.log 2 x + 1) := by
  have := Int.lt_zpow_succ_log_self (R := K) (b := 2) (by norm_num) x
  simpa using this

/-- `Int.log 2` is characterized by its binade. -/
theorem log_eq_of_bounds {x : K} (hx : 0 < x) {L : ℤ} (hl : (2 : K) ^ L ≤ x)
    (hu : x < (2 : K) ^ (L + 1)) : Int.log 2 x = L := by
  have h1 : L ≤ Int.log 2 x := (Int.zpow_le_iff_le_log (R := K) (b := 2) (by norm_num) hx).mp
    (by simpa using hl)
  have h2 : Int.log 2 x < L + 1 := (Int.lt_zpow_iff_log_lt (R := K) (b := 2) (by norm_num) hx).mp
    (by simpa using hu)
  omega

/-- Every representable magnitude is an integer multiple of the quantum of `x`,
or lies below the binade of `x` (and then the quantum is not clamped). -/
theorem rep_dichotomy {c : K} (hc : g.Rep c) :
    (∃ k : ℕ, c = (k : K) * (2 : K) ^ g.qexp x) ∨
      (c < (2 : K) ^ Int.log 2 x ∧ g.qexp x = Int.log 2 x - ((g.prec : ℤ) - 1)) := by
  obtain ⟨m, e, hm, he, rfl⟩ := hc
  by_cases hle : g.qexp x ≤ e
  · left
    refine ⟨m * 2 ^ (e - g.qexp x).toNat, ?_⟩
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
    congr 2
    omega
  · right
    have hlt : e < g.qexp x := lt_of_not_ge hle
    have hq : g.qexp x = Int.log 2 x - ((g.prec : ℤ) - 1) := clamp_eq_of_lt g he hlt
    refine ⟨?_, hq⟩
    have hm' : (m : K) < (2 : K) ^ g.prec := by exact_mod_cast hm
    have hpow : (2 : K) ^ e ≤ (2 : K) ^ (g.qexp x - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc (m : K) * 2 ^ e < (2 : K) ^ g.prec * 2 ^ e :=
          mul_lt_mul_of_pos_right hm' (zpow_pos (by norm_num) _)
      _ ≤ (2 : K) ^ g.prec * 2 ^ (g.qexp x - 1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (2 : K) ^ Int.log 2 x := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
          congr 1
          omega

theorem scaled_lt :
    x / (2 : K) ^ g.qexp x < (2 : K) ^ g.prec := by
  rw [div_lt_iff₀ (zpow_pos (by norm_num) _)]
  calc x < (2 : K) ^ (Int.log 2 x + 1) := lt_two_zpow_log_succ x
    _ ≤ (2 : K) ^ ((g.prec : ℤ) + g.qexp x) := by
        apply zpow_le_zpow_right₀ (by norm_num)
        have := g.le_clamp (Int.log 2 x - ((g.prec : ℤ) - 1))
        unfold qexp
        omega
    _ = (2 : K) ^ g.prec * (2 : K) ^ g.qexp x := by
        rw [zpow_add₀ (by norm_num : (2 : K) ≠ 0), zpow_natCast]

theorem floor_lt (hx : 0 < x) :
    ⌊x / (2 : K) ^ g.qexp x⌋₊ < 2 ^ g.prec := by
  rw [Nat.floor_lt (by positivity)]
  exact_mod_cast g.scaled_lt (x := x)

theorem ceil_le :
    ⌈x / (2 : K) ^ g.qexp x⌉₊ ≤ 2 ^ g.prec := by
  rw [Nat.ceil_le]
  exact_mod_cast (g.scaled_lt (x := x)).le

theorem isDown_floor (hp : 1 ≤ g.prec) (hx : 0 < x) :
    g.IsDown x ((⌊x / (2 : K) ^ g.qexp x⌋₊ : K) * (2 : K) ^ g.qexp x) := by
  have hpos : (0 : K) < (2 : K) ^ g.qexp x := zpow_pos (by norm_num) _
  have hfl : (⌊x / (2 : K) ^ g.qexp x⌋₊ : K) * (2 : K) ^ g.qexp x ≤ x := by
    rw [← le_div_iff₀ hpos]
    exact Nat.floor_le (by positivity)
  refine ⟨⟨_, _, g.floor_lt hx, g.admits_clamp _, rfl⟩, hfl, ?_⟩
  intro c hc hcx
  rcases g.rep_dichotomy (x := x) hc with ⟨k, rfl⟩ | ⟨hlt, hq⟩
  · apply mul_le_mul_of_nonneg_right _ hpos.le
    have hk : (k : K) ≤ x / (2 : K) ^ g.qexp x := by rwa [le_div_iff₀ hpos]
    exact_mod_cast Nat.le_floor hk
  · apply le_of_lt (lt_of_lt_of_le hlt _)
    have hbin : (2 : K) ^ Int.log 2 x = ((2 ^ (g.prec - 1) : ℕ) : K) * (2 : K) ^ g.qexp x := by
      rw [hq]
      push_cast
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
      congr 1
      omega
    rw [hbin]
    apply mul_le_mul_of_nonneg_right _ hpos.le
    have h2 : (((2 ^ (g.prec - 1) : ℕ) : K)) ≤ x / (2 : K) ^ g.qexp x := by
      rw [le_div_iff₀ hpos, ← hbin]
      exact two_zpow_log_le hx
    exact_mod_cast Nat.le_floor h2

theorem isUp_ceil (hp : 1 ≤ g.prec) (hx : 0 < x) :
    g.IsUp x ((⌈x / (2 : K) ^ g.qexp x⌉₊ : K) * (2 : K) ^ g.qexp x) := by
  have hpos : (0 : K) < (2 : K) ^ g.qexp x := zpow_pos (by norm_num) _
  refine ⟨g.rep_mul hp (g.ceil_le (x := x)) (g.admits_clamp _), ?_, ?_⟩
  · rw [← div_le_iff₀ hpos]
    exact Nat.le_ceil _
  · intro c hc hxc
    rcases g.rep_dichotomy (x := x) hc with ⟨k, rfl⟩ | ⟨hlt, -⟩
    · apply mul_le_mul_of_nonneg_right _ hpos.le
      have hk : x / (2 : K) ^ g.qexp x ≤ (k : K) := by rwa [div_le_iff₀ hpos]
      exact_mod_cast Nat.ceil_le.mpr hk
    · exact absurd (lt_of_lt_of_le hlt (two_zpow_log_le hx)) (not_lt.mpr hxc)

end Positive

theorem isDown_zero (g : Grid) : g.IsDown (0 : K) 0 :=
  ⟨g.rep_zero, le_rfl, fun _ _ h => h⟩

theorem isUp_zero (g : Grid) : g.IsUp (0 : K) 0 :=
  ⟨g.rep_zero, le_rfl, fun _ hc _ => rep_nonneg hc⟩

/-- The floor/ceiling formula meets the rounding specification, over any
ordered field with a floor. -/
theorem roundMag_floor_ceil (g : Grid) (hp : 1 ≤ g.prec) (mode : RoundingMode) (neg : Bool)
    {x : K} (hx : 0 ≤ x) :
    g.RoundMag mode neg x
      (pick mode neg (⌊x / (2 : K) ^ g.qexp x⌋₊ % 2 = 0) x
        ((⌊x / (2 : K) ^ g.qexp x⌋₊ : K) * (2 : K) ^ g.qexp x)
        ((⌈x / (2 : K) ^ g.qexp x⌉₊ : K) * (2 : K) ^ g.qexp x)) := by
  rcases hx.lt_or_eq with hx | rfl
  · exact ⟨_, _, g.isDown_floor hp hx, g.isUp_ceil hp hx, rfl⟩
  · refine ⟨0, 0, g.isDown_zero, g.isUp_zero, ?_⟩
    simp [pick_self]

theorem IsDown.unique {g : Grid} {x d d' : K} (h : g.IsDown x d) (h' : g.IsDown x d') :
    d = d' :=
  le_antisymm (h'.2.2 d h.1 h.2.1) (h.2.2 d' h'.1 h'.2.1)

theorem IsUp.unique {g : Grid} {x u u' : K} (h : g.IsUp x u) (h' : g.IsUp x u') :
    u = u' :=
  le_antisymm (h.2.2 u' h'.1 h'.2.1) (h'.2.2 u h.1 h.2.1)

/-- The rounding specification is functional: at most one result. -/
theorem RoundMag.unique {g : Grid} {mode : RoundingMode} {neg : Bool} {x r r' : K}
    (h : g.RoundMag mode neg x r) (h' : g.RoundMag mode neg x r') : r = r' := by
  obtain ⟨d, u, hd, hu, rfl⟩ := h
  obtain ⟨d', u', hd', hu', rfl⟩ := h'
  rw [hd.unique hd', hu.unique hu']

/-- Rounded results lie between the two neighbours. -/
theorem RoundMag.bounds {g : Grid} {mode : RoundingMode} {neg : Bool} {x r : K}
    (h : g.RoundMag mode neg x r) : ∃ d u, g.IsDown x d ∧ g.IsUp x u ∧ (r = d ∨ r = u) := by
  obtain ⟨d, u, hd, hu, rfl⟩ := h
  exact ⟨d, u, hd, hu, pickBy_cases _ _ _ _ _ _ _⟩

/-- Rounded results are representable. -/
theorem RoundMag.rep {g : Grid} {mode : RoundingMode} {neg : Bool} {x r : K}
    (h : g.RoundMag mode neg x r) : g.Rep r := by
  obtain ⟨d, u, hd, hu, rfl | rfl⟩ := h.bounds
  · exact hd.1
  · exact hu.1

/-! ## Executable rounding on rationals -/

/-- `⌊log₂ x⌋` for a positive rational, from the binary lengths of its numerator
and denominator. -/
def floorLog2 (x : ℚ) : ℤ :=
  let k : ℤ := (x.num.natAbs.log2 : ℤ) - (x.den.log2 : ℤ)
  if x < (2 : ℚ) ^ k then k - 1 else k

theorem floorLog2_eq {x : ℚ} (hx : 0 < x) : floorLog2 x = Int.log 2 x := by
  set n := x.num.natAbs
  set d := x.den
  set a := n.log2
  set b := d.log2
  have hn0 : n ≠ 0 := by
    have := Rat.num_pos.mpr hx
    omega
  have hd0 : d ≠ 0 := x.den_nz
  have hxnd : x = (n : ℚ) / d := by
    have hnum : ((n : ℤ) : ℚ) = (x.num : ℚ) := by
      congr 1
      exact Int.natAbs_of_nonneg (Rat.num_pos.mpr hx).le
    rw [← Rat.num_div_den x]
    simp only [d]
    rw [← hnum]
    push_cast
    rfl
  have hna : (2 : ℚ) ^ a ≤ n := by exact_mod_cast Nat.log2_self_le hn0
  have hnb : (n : ℚ) < 2 ^ (a + 1) := by exact_mod_cast Nat.lt_log2_self
  have hda : (2 : ℚ) ^ b ≤ d := by exact_mod_cast Nat.log2_self_le hd0
  have hdb : (d : ℚ) < 2 ^ (b + 1) := by exact_mod_cast Nat.lt_log2_self
  have hdpos : (0 : ℚ) < d := by positivity
  have hlow : (2 : ℚ) ^ ((a : ℤ) - b - 1) ≤ x := by
    rw [hxnd, le_div_iff₀ hdpos]
    calc (2 : ℚ) ^ ((a : ℤ) - b - 1) * d ≤ 2 ^ ((a : ℤ) - b - 1) * 2 ^ ((b : ℤ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast hdb.le
      _ = 2 ^ a := by
          rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), ← zpow_natCast]
          congr 1
          omega
      _ ≤ n := hna
  have hhigh : x < (2 : ℚ) ^ ((a : ℤ) - b + 1) := by
    rw [hxnd, div_lt_iff₀ hdpos]
    calc (n : ℚ) < 2 ^ (a + 1) := hnb
      _ = 2 ^ ((a : ℤ) - b + 1) * 2 ^ (b : ℤ) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), ← zpow_natCast]
          congr 1
          omega
      _ ≤ 2 ^ ((a : ℤ) - b + 1) * d := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast hda
  unfold floorLog2
  simp only
  split_ifs with h
  · exact (log_eq_of_bounds hx (by simpa [sub_sub] using hlow)
      (by simpa using h)).symm
  · exact (log_eq_of_bounds hx (not_lt.mp h) hhigh).symm

/-- Executable quantum exponent. -/
def qexpQ (g : Grid) (x : ℚ) : ℤ := g.clamp (floorLog2 x - ((g.prec : ℤ) - 1))

theorem qexpQ_eq (g : Grid) {x : ℚ} (hx : 0 < x) : g.qexpQ x = g.qexp x := by
  simp [qexpQ, qexp, floorLog2_eq hx]

/-- Executable rounding of a nonnegative rational magnitude. -/
def roundMagQ (g : Grid) (mode : RoundingMode) (neg : Bool) (x : ℚ) : ℚ :=
  let q := g.qexpQ x
  let s := x / (2 : ℚ) ^ q
  pick mode neg (⌊s⌋₊ % 2 = 0) x ((⌊s⌋₊ : ℚ) * (2 : ℚ) ^ q) ((⌈s⌉₊ : ℚ) * (2 : ℚ) ^ q)

/-- The executable rounder is correct: it returns the specified rounding. -/
theorem roundMagQ_spec (g : Grid) (hp : 1 ≤ g.prec) (mode : RoundingMode) (neg : Bool)
    {x : ℚ} (hx : 0 ≤ x) : g.RoundMag mode neg x (g.roundMagQ mode neg x) := by
  rcases hx.lt_or_eq with hx' | rfl
  · unfold roundMagQ
    simp only [g.qexpQ_eq hx']
    exact g.roundMag_floor_ceil hp mode neg hx
  · refine ⟨0, 0, g.isDown_zero, g.isUp_zero, ?_⟩
    simp [roundMagQ, pick_self]

theorem roundMagQ_eq_iff (g : Grid) (hp : 1 ≤ g.prec) (mode : RoundingMode) (neg : Bool)
    {x r : ℚ} (hx : 0 ≤ x) : g.roundMagQ mode neg x = r ↔ g.RoundMag mode neg x r :=
  ⟨fun h => h ▸ g.roundMagQ_spec hp mode neg hx,
    fun h => (g.roundMagQ_spec hp mode neg hx).unique h⟩

end Grid

end Silmaril.Numeric.Ieee754.Std
