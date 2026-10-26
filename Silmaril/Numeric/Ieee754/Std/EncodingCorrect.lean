module

public import Silmaril.Numeric.Ieee754.Std.Isa

/-!
# Correctness of the encodings

* `Interchange.decode_encode_fin`: the canonical encoding of every finite
  representable magnitude up to `maxFinite` decodes to the same datum, for every
  interchange format (normal and subnormal cases, gradual underflow).
* `Interchange.decode_deliver`: every non-NaN datum delivered by `RoundSpec`
  (including overflow results) is encoded faithfully, so the bit-level result of
  `OpSpec` decodes to the specified value.
* `X87.decode_hardware_eq_softfloat`: the hardware and SoftFloat readings of x87
  encodings agree outside the unnormal, pseudo-infinity and pseudo-NaN classes,
  and `X87.ReadingChaos` (the union of the two readings) contains both. The chaotic
  reading, any datum for those three classes, is `X87.ReadingAny` in `Std.Chaos`.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

namespace Interchange

variable (F : Interchange)

theorem qmin_eq : F.fmt.qmin = 1 - ((2 ^ (F.w - 1) - 1 : ℕ) : ℤ) - (F.t : ℤ) := by
  simp [BinFormat.qmin, BinFormat.emin, fmt]

theorem expMax_ge : 3 ≤ F.expMax := by
  have := F.hw
  unfold expMax
  have : 4 ≤ 2 ^ F.w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) this)
  omega

theorem two_pow_w : 2 ^ F.w = 2 * 2 ^ (F.w - 1) := by
  have := F.hw
  rw [← pow_succ']
  congr 1
  omega

/-- A representable magnitude is the integer multiple `⌊r / 2^q⌋₊ * 2^q` of its quantum. -/
theorem rep_eq_floor_mul {g : Grid} {r : ℚ} (hr : g.Rep r) (hpos : 0 < r) :
    r = (⌊r / 2 ^ g.qexp r⌋₊ : ℚ) * 2 ^ g.qexp r := by
  have hd := g.rep_dichotomy (x := r) hr
  generalize g.qexp r = q at hd ⊢
  rcases hd with ⟨k, hk⟩ | ⟨hlt, -⟩
  · have hq : (0 : ℚ) < 2 ^ q := zpow_pos (by norm_num) _
    have : r / 2 ^ q = k := by rw [div_eq_iff hq.ne']; exact hk
    rw [this, Nat.floor_natCast]
    exact hk
  · exact absurd (Grid.two_zpow_log_le hpos) (not_le.mpr hlt)

theorem decode_encode_fin (s : Bool) {r : ℚ} (hr : F.fmt.grid.Rep r) (hmax : r ≤ F.fmt.maxFinite) :
    F.decode (F.encode (.fin s r)) = .fin s r := by
  have hr0 : 0 ≤ r := Grid.rep_nonneg hr
  rcases hr0.lt_or_eq with hpos | rfl
  · have hne : r ≠ 0 := hpos.ne'
    set g := F.fmt.grid
    set q := g.qexp r with hqdef
    set n := ⌊r / 2 ^ q⌋₊ with hn
    have hrn : r = (n : ℚ) * 2 ^ q := rep_eq_floor_mul hr hpos
    have hqQ : g.qexpQ r = q := g.qexpQ_eq hpos
    have hp : F.fmt.prec = F.t + 1 := rfl
    have hgprec : g.prec = F.t + 1 := rfl
    have hglo : g.lo = some F.fmt.qmin := rfl
    have hqge : F.fmt.qmin ≤ q := by
      have := g.admits_clamp (Int.log 2 r - ((g.prec : ℤ) - 1))
      exact this F.fmt.qmin (by simp [hglo])
    have hnlt : n < 2 ^ (F.t + 1) := by
      have := g.floor_lt (x := r) hpos; rwa [hgprec] at this
    have hL : (2 : ℚ) ^ Int.log 2 r ≤ r := Grid.two_zpow_log_le hpos
    -- the quantum is the clamp of `log₂ r - t`
    have hq : q = max (Int.log 2 r - F.t) F.fmt.qmin := by
      simp only [hqdef, Grid.qexp, Grid.clamp, hglo, hgprec]; push_cast; ring_nf
    have hencode : F.encode (.fin s r) =
        (if n < 2 ^ F.t then ⟨s, 0, n⟩ else ⟨s, (q - F.fmt.qmin + 1).toNat, n - 2 ^ F.t⟩) := by
      simp only [encode, hne, ite_false]
      rw [show F.fmt.grid.qexpQ r = q from hqQ]
    rw [hencode]
    have hexp0 : (0 : ℕ) ≠ F.expMax := by have := F.expMax_ge; omega
    split_ifs with hsub
    · -- subnormal: the quantum is the least one
      have hqmin : q = F.fmt.qmin := by
        by_contra hneq
        have hq' : q = Int.log 2 r - F.t := by rw [hq] at hneq ⊢; omega
        have : (2 : ℚ) ^ F.t ≤ n := by
          have h1 : (2 : ℚ) ^ Int.log 2 r = (2 : ℚ) ^ (F.t : ℤ) * 2 ^ q := by
            rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; congr 1; omega
          have h2 : (2 : ℚ) ^ (F.t : ℤ) * 2 ^ q ≤ (n : ℚ) * 2 ^ q := by rw [← h1, ← hrn]; exact hL
          have := le_of_mul_le_mul_right h2 (zpow_pos (by norm_num) _)
          simpa using this
        have : 2 ^ F.t ≤ n := by exact_mod_cast this
        omega
      simp only [decode, hexp0, ↓reduceIte]
      rw [hrn, hqmin]
    · -- normal
      have hnge : 2 ^ F.t ≤ n := not_lt.mp hsub
      have hexpPos : 1 ≤ q - F.fmt.qmin + 1 := by omega
      -- the exponent field is below the all-ones value
      have hqmax : q + F.t ≤ (F.fmt.emax : ℤ) := by
        have hnr : (2 : ℚ) ^ ((F.t : ℤ) + q) ≤ r := by
          rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), hrn, zpow_natCast]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnge) (by positivity)
        have hmf : F.fmt.maxFinite < (2 : ℚ) ^ ((F.fmt.emax : ℤ) + 1) := by
          unfold BinFormat.maxFinite
          rw [hp]
          have : (2 : ℚ) ^ ((F.fmt.emax : ℤ) + 1) =
              2 ^ (F.t + 1) * (2 : ℚ) ^ ((F.fmt.emax : ℤ) - (((F.t + 1 : ℕ) : ℤ) - 1)) := by
            rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; congr 1; push_cast; ring
          rw [this]
          apply mul_lt_mul_of_pos_right _ (zpow_pos (by norm_num) _)
          linarith
        have := lt_of_le_of_lt (le_trans hnr hmax) hmf
        have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp this
        omega
      have hemax : (F.fmt.emax : ℤ) = 2 ^ (F.w - 1) - 1 := by
        have := F.two_le_pow
        simp only [fmt]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 ^ (F.w - 1))]; ring
      have hexpNe : (q - F.fmt.qmin + 1).toNat ≠ F.expMax := by
        have hqm := F.qmin_eq
        have h2 := F.two_pow_w
        have h3 := F.two_le_pow
        unfold expMax
        have hc : ((2 ^ (F.w - 1) - 1 : ℕ) : ℤ) = 2 ^ (F.w - 1) - 1 := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ 2 ^ (F.w - 1))]; ring
        rw [hc] at hqm
        have : ((2 ^ F.w : ℕ) : ℤ) = 2 * 2 ^ (F.w - 1) := by exact_mod_cast h2
        intro h
        have h' : ((q - F.fmt.qmin + 1).toNat : ℤ) = ((2 ^ F.w - 1 : ℕ) : ℤ) := by rw [h]
        rw [Int.toNat_of_nonneg (by omega)] at h'
        push_cast [Nat.cast_sub (Nat.one_le_two_pow)] at h'
        omega
      have hexpNe0 : (q - F.fmt.qmin + 1).toNat ≠ 0 := by omega
      simp only [decode, hexpNe, hexpNe0, ite_false]
      congr 1
      rw [hrn]
      have hsum : 2 ^ F.t + (n - 2 ^ F.t) = n := by omega
      rw [hsum]
      congr 2
      rw [Int.toNat_of_nonneg (by omega)]
      ring
  · simp [encode, decode, show (0 : ℕ) ≠ F.expMax by have := F.expMax_ge; omega]

theorem decode_encode_inf (s : Bool) : F.decode (F.encode (.inf s)) = .inf s := by
  simp [encode, decode]

end Interchange

theorem Grid.rep_of_cast {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {g : Grid} {r : ℚ} (h : g.Rep (r : K)) : g.Rep r := by
  obtain ⟨n, e, hn, he, heq⟩ := h
  refine ⟨n, e, hn, he, ?_⟩
  have : ((r : ℚ) : K) = (((n : ℚ) * 2 ^ e : ℚ) : K) := by rw [heq]; push_cast; rfl
  exact_mod_cast this

theorem BinFormat.rep_maxFinite (f : BinFormat) : f.grid.Rep f.maxFinite := by
  refine ⟨2 ^ f.prec - 1, (f.emax : ℤ) - ((f.prec : ℤ) - 1), ?_, ?_, ?_⟩
  · show 2 ^ f.prec - 1 < 2 ^ f.prec
    have := Nat.one_le_two_pow (n := f.prec); omega
  · intro l hl
    simp only [BinFormat.grid, Option.mem_def, Option.some.injEq] at hl
    subst hl
    simp only [BinFormat.qmin, BinFormat.emin]
    have := f.one_le_emax
    omega
  · simp [BinFormat.maxFinite, Nat.cast_sub (Nat.one_le_two_pow)]

namespace Interchange

variable (F : Interchange)

/-- Every non-NaN datum delivered by rounding is encoded faithfully. -/
theorem decode_roundSpec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorRing K] {tin : TininessDetection} {mode : RoundingMode} {neg : Bool} {x : K}
    {res : Datum} {fl : Flags} (h : RoundSpec F.fmt tin mode neg x res fl) :
    F.decode (F.encode res) = res := by
  obtain ⟨r, ru, hr, -, rfl, -⟩ := h
  split_ifs with hov
  · unfold overflowResult
    cases mode <;> (try split_ifs) <;>
      first
      | exact F.decode_encode_inf _
      | exact F.decode_encode_fin _ F.fmt.rep_maxFinite le_rfl
  · exact F.decode_encode_fin _ (Grid.rep_of_cast hr.rep) (not_lt.mp hov)

/-- The bit-level result of an operation decodes to the specified datum whenever
that datum is not a NaN. -/
theorem OpSpec.decode_out {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorRing K] {P : NaNSpec} {tin : TininessDetection} {mode : RoundingMode}
    {ins : List Fields} {e : Exact K} {out : Fields} {fl : Flags}
    (h : OpSpec F.encoding P tin mode ins e out fl) :
    ∃ res, Deliver F.fmt tin mode e res fl ∧ (res.isNaN = false → F.decode out = res) := by
  obtain ⟨res, hd, -, he⟩ := h
  refine ⟨res, hd, fun hn => ?_⟩
  rw [he hn]
  change F.decode (F.encode res) = res
  cases e with
  | nan inv => obtain ⟨rfl, -⟩ := hd; simp [Datum.isNaN] at hn
  | inf neg dz => obtain ⟨rfl, -⟩ := hd; exact F.decode_encode_inf neg
  | num neg x => exact F.decode_roundSpec hd

end Interchange

/-! ## x87 readings -/

namespace X87

/-- Outside the unnormal, pseudo-infinity and pseudo-NaN classes the hardware and
SoftFloat readings agree. -/
theorem decode_hardware_eq_softfloat (b : Fields) (h1 : classify b ≠ .unnormal)
    (h2 : classify b ≠ .pseudoInfinity) (h3 : classify b ≠ .pseudoNaN) :
    decode .hardware b = decode .softfloat b := by
  unfold decode
  cases hc : classify b <;> simp_all

/-- The union of the two readings: the 387+ hardware reading or the SoftFloat one.
It is not chaos (it excludes, e.g., 8087/287 readings of unnormals); the chaotic
reading is `X87.ReadingAny` (`Std.Chaos`), which contains it
(`X87.readingChaos_le_readingAny`). -/
def ReadingChaos (b : Fields) (d : Datum) : Prop := ∃ r : X87Reading, d = decode r b

theorem readingChaos_hardware (b : Fields) : ReadingChaos b (decode .hardware b) := ⟨_, rfl⟩
theorem readingChaos_softfloat (b : Fields) : ReadingChaos b (decode .softfloat b) := ⟨_, rfl⟩

end X87

end Silmaril.Numeric.Ieee754.Std
