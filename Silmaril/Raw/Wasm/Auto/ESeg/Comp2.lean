module

public import Silmaril.Proofs.Wasm.Auto.ESeg.Comp2

/-! # The second family of computed rewrites: divisibility and signed division

* `sremEqz?_eval`: `eqz (x %s 2^k)` is `eqz (x & (2^k - 1))` (through `toNat` and
  divisibility, both signs of `x`);
* `sdiv_pow2`, `sdivPow2?_eval`: signed division by `2^k`, `0 < k < w - 1`, is the bias form
  `(x + ((x >>s (w-1)) >>u (w-k))) >>s k` (through `toNat`, by the sign of `x` and whether the
  bias wraps);
* `comp2?_eval`: the whole second family keeps the value;
* `intBinOp_ok_of_safe`: an operator that `safeBinOp` admits (a division or remainder by a
  constant that is not `0`, nor `-1` for `div_s`) does not trap.

Unrefined proofs (case splits on signs and wrap-around, closed by `omega`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.EGraph

/-! ## Divisibility by a power of two -/

theorem pow2_lt_half {w k : Nat} (hk : k < w - 1) : 2 ^ k < 2 ^ (w - 1) :=
  Nat.pow_lt_pow_right (by decide) hk

/-- `x %s 2^k = 0` iff `x % 2^k = 0`, through `toNat`. -/
theorem srem_pow2_eq_zero {w k : Nat} (hk : k < w - 1) (x : BitVec w) :
    (x.srem (BitVec.ofNat w (2 ^ k)) = 0) ↔ (x % BitVec.ofNat w (2 ^ k) = 0) := by
  have hkw : k < w := by omega
  have hpk : (BitVec.ofNat w (2 ^ k)).toNat = 2 ^ k := toNat_ofNat_pow hkw
  have hhalf : 2 ^ k < 2 ^ (w - 1) := pow2_lt_half hk
  have hmsb : (BitVec.ofNat w (2 ^ k)).msb = false := by
    rw [BitVec.msb_eq_decide, hpk]; simp; omega
  have hdvd : 2 ^ k ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [BitVec.srem_eq, hmsb]
  cases hx : x.msb
  · rfl
  · show -((-x) % BitVec.ofNat w (2 ^ k)) = 0 ↔ x % BitVec.ofNat w (2 ^ k) = 0
    have hneg0 : ∀ y : BitVec w, -y = 0 ↔ y = 0 := fun y => by
      constructor
      · intro h; have := congrArg (fun z => -z) h; simpa using this
      · intro h; simp [h]
    rw [hneg0, eq_zero_iff_toNat, eq_zero_iff_toNat, BitVec.toNat_umod,
      BitVec.toNat_umod, hpk, BitVec.toNat_neg]
    have hX : x.toNat < 2 ^ w := x.isLt
    have hX0 : 0 < x.toNat := by
      rw [BitVec.msb_eq_decide] at hx
      have : 2 ^ (w - 1) ≤ x.toNat := by simpa using hx
      have : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
      omega
    have hsub : (2 ^ w - x.toNat) % 2 ^ w = 2 ^ w - x.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hsub, ← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
    constructor
    · intro h
      have h' : 2 ^ k ∣ 2 ^ w - (2 ^ w - x.toNat) := Nat.dvd_sub hdvd h
      rwa [Nat.sub_sub_self (by omega)] at h'
    · intro h
      exact Nat.dvd_sub hdvd h

theorem srem_eqz_and {t : IntType} {k : Nat} (hk : k < t.width - 1) (x : BitVec t.width) :
    intBinOp t (.rem .signed) x (BitVec.ofNat _ (2 ^ k)) =
        .ok (x.srem (BitVec.ofNat _ (2 ^ k))) ∧
      intTestOp t .eqz (x.srem (BitVec.ofNat _ (2 ^ k))) =
        intTestOp t .eqz (x &&& BitVec.ofNat _ (2 ^ k - 1)) := by
  have hkw : k < t.width := by omega
  refine ⟨by simp only [intBinOp, pow2_ne_zero hkw, ↓reduceIte], ?_⟩
  have hiff := srem_pow2_eq_zero hk x
  rw [umod_pow2 hkw] at hiff
  have hb : (x.srem (BitVec.ofNat _ (2 ^ k)) == 0) = (x &&& BitVec.ofNat _ (2 ^ k - 1) == 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact hiff
  simp only [intTestOp, hb]

theorem sremEqz?_eval {f : Frame} {a b : Term} (h : sremEqz? a = some b) :
    a.eval f = b.eval f := by
  unfold sremEqz? at h
  split at h
  · rename_i t t' x t'' n
    split at h
    · rename_i ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨k, hk, hb⟩ : ∃ k, pow2Exp? (t.width - 1) n = some k ∧
          Term.test t (.bin t .and x (.const t (n - 1))) = b := Option.map_eq_some_iff.mp h
      obtain ⟨hlt, hn⟩ : k < t.width - 1 ∧ 2 ^ k = n := pow2Exp?_spec hk
      subst hb hn
      have hrem : ∀ z, intBinOp t (.rem .signed) z (BitVec.ofNat _ (2 ^ k)) =
          .ok (z.srem (BitVec.ofNat _ (2 ^ k))) := fun z => (srem_eqz_and hlt z).1
      have hand : ∀ z, intBinOp t .and z (BitVec.ofNat _ (2 ^ k - 1)) =
          .ok (z &&& BitVec.ofNat _ (2 ^ k - 1)) := fun _ => rfl
      simp only [Term.eval, binV_const_ok hrem, binV_const_ok hand, testV_eq_map]
      cases x.eval f with
      | none => rfl
      | some v =>
        cases hv : asInt t v with
        | none => simp [hv]
        | some z =>
          have hz := (srem_eqz_and hlt z).2
          simp only [hv, Option.map_some, Option.bind_some, asInt_intVal]
          exact congrArg (fun c => some (Val.i32 c)) hz
    · cases h
  · cases h

/-! ## Signed division by a power of two -/

/-- `(2^w - 1) / 2^(w-k) = 2^k - 1`. -/
theorem ones_div_pow {w k : Nat} (hk : k ≤ w) : (2 ^ w - 1) / 2 ^ (w - k) = 2 ^ k - 1 := by
  have hw : 2 ^ w = 2 ^ k * 2 ^ (w - k) := by rw [← Nat.pow_add]; congr 1; omega
  have hP : 0 < 2 ^ (w - k) := Nat.two_pow_pos _
  have hQ : 0 < 2 ^ k := Nat.two_pow_pos _
  rw [hw]
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_one_mul]
    have : 2 ^ k * 2 ^ (w - k) ≥ 2 ^ (w - k) := Nat.le_mul_of_pos_left _ hQ
    omega
  · rw [Nat.sub_add_cancel hQ]
    have : 0 < 2 ^ k * 2 ^ (w - k) := Nat.mul_pos hQ hP
    omega

/-- The bias form of signed division by `2^k`, through `toNat`. -/
theorem sdiv_pow2 {w k : Nat} (hk0 : 0 < k) (hk : k < w - 1) (x : BitVec w) :
    x.sdiv (BitVec.ofNat w (2 ^ k)) =
      (x + ((x.sshiftRight (w - 1)) >>> (w - k))).sshiftRight k := by
  have hkw : k < w := by omega
  have hpk : (BitVec.ofNat w (2 ^ k)).toNat = 2 ^ k := toNat_ofNat_pow hkw
  have hhalf : 2 ^ k < 2 ^ (w - 1) := pow2_lt_half hk
  have hcm : (BitVec.ofNat w (2 ^ k)).msb = false := by
    rw [BitVec.msb_eq_decide, hpk]; simp; omega
  have hw2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hX : x.toNat < 2 ^ w := x.isLt
  have hQ : 0 < 2 ^ k := Nat.two_pow_pos k
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.sdiv_eq, hcm]
  cases hx : x.msb
  · -- `x ≥ 0`: no bias
    have hxl : x.toNat < 2 ^ (w - 1) := by
      rw [BitVec.msb_eq_decide] at hx; simpa using hx
    have hs1 : x.sshiftRight (w - 1) = 0 := by
      rw [BitVec.sshiftRight_eq_of_msb_false hx]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hxl]; rfl
    show (x.udiv (BitVec.ofNat w (2 ^ k))).toNat = _
    have hz : (0 : BitVec w) >>> (w - k) = 0 := by
      apply BitVec.eq_of_toNat_eq; simp
    have ha : x + (0 : BitVec w) = x := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [hs1, hz, ha, BitVec.toNat_sshiftRight_of_msb_false hx, BitVec.udiv_eq,
      BitVec.toNat_udiv, hpk, Nat.shiftRight_eq_div_pow]
  · -- `x < 0`: bias `2^k - 1`
    have hxl : 2 ^ (w - 1) ≤ x.toNat := by
      rw [BitVec.msb_eq_decide] at hx; simpa using hx
    have hs1 : (x.sshiftRight (w - 1)).toNat = 2 ^ w - 1 := by
      rw [BitVec.toNat_sshiftRight_of_msb_true hx, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (by omega)]
      omega
    have hs2 : ((x.sshiftRight (w - 1)) >>> (w - k)).toNat = 2 ^ k - 1 := by
      rw [BitVec.toNat_ushiftRight, hs1, Nat.shiftRight_eq_div_pow, ones_div_pow (by omega)]
    have hA : (-x).toNat = 2 ^ w - x.toNat := by
      rw [BitVec.toNat_neg]; exact Nat.mod_eq_of_lt (by omega)
    show (-((-x).udiv (BitVec.ofNat w (2 ^ k)))).toNat = _
    rw [BitVec.toNat_neg, BitVec.udiv_eq, BitVec.toNat_udiv, hA, hpk]
    by_cases hov : 2 ^ w ≤ x.toNat + (2 ^ k - 1)
    · -- the biased value wraps to a small non-negative number
      have hsum : (x + ((x.sshiftRight (w - 1)) >>> (w - k))).toNat =
          x.toNat + (2 ^ k - 1) - 2 ^ w := by
        rw [BitVec.toNat_add, hs2]
        have : x.toNat + (2 ^ k - 1) < 2 * 2 ^ w := by omega
        rw [Nat.mod_eq_sub_mod hov, Nat.mod_eq_of_lt (by omega)]
      have hm : (x + ((x.sshiftRight (w - 1)) >>> (w - k))).msb = false := by
        rw [BitVec.msb_eq_decide, hsum]; simp; omega
      have hq : (2 ^ w - x.toNat) / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
      rw [BitVec.toNat_sshiftRight_of_msb_false hm, hsum, Nat.shiftRight_eq_div_pow, hq,
        Nat.div_eq_of_lt (by omega)]
      simp
    · -- no wrap: the biased value is still negative
      have hsum : (x + ((x.sshiftRight (w - 1)) >>> (w - k))).toNat = x.toNat + (2 ^ k - 1) := by
        rw [BitVec.toNat_add, hs2, Nat.mod_eq_of_lt (by omega)]
      have hm : (x + ((x.sshiftRight (w - 1)) >>> (w - k))).msb = true := by
        rw [BitVec.msb_eq_decide, hsum]; simp; omega
      have hAk : 2 ^ k ≤ 2 ^ w - x.toNat := by omega
      have hdiv : (2 ^ w - x.toNat - 2 ^ k) / 2 ^ k = (2 ^ w - x.toNat) / 2 ^ k - 1 := by
        have := Nat.sub_mul_div (2 ^ w - x.toNat) (2 ^ k) 1
        rwa [Nat.mul_one] at this
      have hge : 1 ≤ (2 ^ w - x.toNat) / 2 ^ k := (Nat.le_div_iff_mul_le hQ).mpr (by omega)
      have hle : (2 ^ w - x.toNat) / 2 ^ k ≤ 2 ^ w - x.toNat := Nat.div_le_self _ _
      rw [BitVec.toNat_sshiftRight_of_msb_true hm, hsum, Nat.shiftRight_eq_div_pow]
      have hinner : 2 ^ w - 1 - (x.toNat + (2 ^ k - 1)) = 2 ^ w - x.toNat - 2 ^ k := by omega
      rw [hinner, hdiv, Nat.mod_eq_of_lt (by omega)]
      omega

/-- `sdivForm` agrees with `div_s` by `2^k` (which does not trap). -/
theorem intBinOp_sdiv_pow2 {t : IntType} {k : Nat} (hk0 : 0 < k) (hk : k < t.width - 1)
    (x : BitVec t.width) :
    intBinOp t (.div .signed) x (BitVec.ofNat _ (2 ^ k)) =
      .ok ((x + ((x.sshiftRight (t.width - 1)) >>> (t.width - k))).sshiftRight k) := by
  have hkw : k < t.width := by omega
  have hne : ¬ (x = BitVec.intMin t.width ∧ BitVec.ofNat t.width (2 ^ k) = -1) := by
    rintro ⟨-, h⟩
    have h1 := congrArg BitVec.toNat h
    rw [toNat_ofNat_pow hkw, BitVec.toNat_neg] at h1
    have hlt : 2 ^ k < 2 ^ (t.width - 1) := pow2_lt_half hk
    have hw2 : 2 ^ t.width = 2 * 2 ^ (t.width - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have h1' : (1 : BitVec t.width).toNat = 1 := by cases t <;> rfl
    rw [h1', Nat.mod_eq_of_lt (by omega)] at h1
    omega
  simp only [intBinOp, pow2_ne_zero hkw, ↓reduceIte, hne, sdiv_pow2 hk0 hk]

theorem sdivPow2?_eval {f : Frame} {a b : Term} (h : sdivPow2? a = some b) :
    a.eval f = b.eval f := by
  unfold sdivPow2? at h
  split at h
  · rename_i t x t' n
    split at h
    · rename_i ht
      subst ht
      obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hk0
        cases h
        obtain ⟨hlt, hn⟩ : k < t.width - 1 ∧ 2 ^ k = n := pow2Exp?_spec hk
        subst hn
        have hkw : k < t.width := by omega
        have c₁ : ∀ z, intBinOp t (.shr .signed) z (BitVec.ofNat _ (t.width - 1)) =
            .ok (z.sshiftRight (t.width - 1)) := fun z => by
          simp only [intBinOp, toNat_ofNat_small (show t.width - 1 < t.width by omega),
            Nat.mod_eq_of_lt (show t.width - 1 < t.width by omega)]
        have c₂ : ∀ z, intBinOp t (.shr .unsigned) z (BitVec.ofNat _ (t.width - k)) =
            .ok (z >>> (t.width - k)) := fun z => by
          simp only [intBinOp, toNat_ofNat_small (show t.width - k < t.width by omega),
            Nat.mod_eq_of_lt (show t.width - k < t.width by omega)]
        have c₃ : ∀ z, intBinOp t (.shr .signed) z (BitVec.ofNat _ k) =
            .ok (z.sshiftRight k) := fun z => by
          simp only [intBinOp, toNat_ofNat_small hkw, Nat.mod_eq_of_lt hkw]
        simp only [sdivForm, Term.eval, binV_const_ok (intBinOp_sdiv_pow2 hk0 hlt),
          binV_const_ok c₁, binV_const_ok c₂, binV_const_ok c₃]
        cases x.eval f with
        | none => rfl
        | some v =>
          cases hv : asInt t v with
          | none => simp [hv, binV]
          | some z => simp [hv, binV, intBinOp]
      · cases h
    · cases h
  · cases h

/-! ## Odd masks of booleans -/

theorem bool32_and_odd (p : Bool) {c : Nat} (hc : c % 2 = 1) :
    BitVec.ofNat 32 c &&& bool32 p = bool32 p := by
  apply BitVec.eq_of_toNat_eq
  have hc' : (BitVec.ofNat 32 c).toNat % 2 = 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 32)]; exact hc
  cases p
  · simp [bool32]
  · simp only [bool32, ite_true, BitVec.toNat_and]
    show (BitVec.ofNat 32 c).toNat &&& 1 = 1
    rw [Nat.and_one_is_mod, hc']

/-- A test or a comparison is `none` or a boolean `i32`. -/
theorem isBool_eval {f : Frame} {b : Term} (hb : isBool b = true) :
    b.eval f = none ∨ ∃ p, b.eval f = some (intVal .i32 (bool32 p)) := by
  cases b with
  | test t a =>
    simp only [Term.eval, testV]
    cases (a.eval f).bind (asInt t) with
    | none => exact .inl rfl
    | some x => exact .inr ⟨x == 0, rfl⟩
  | rel t op a b =>
    simp only [Term.eval]
    rw [relV]
    cases a.eval f with
    | none => exact .inl rfl
    | some va =>
      cases b.eval f with
      | none => exact .inl rfl
      | some vb =>
        simp only [Option.bind_some]
        cases asInt t va with
        | none => exact .inl rfl
        | some x =>
          cases asInt t vb with
          | none => exact .inl rfl
          | some y =>
            simp only [Option.bind_some, Option.map_some]
            unfold intRelOp
            exact .inr ⟨_, rfl⟩
  | _ => simp [isBool] at hb

theorem and_bool_eval {f : Frame} {b : Term} {c : Nat} (hc : c % 2 = 1) (hb : isBool b = true) :
    (Term.bin .i32 .and (.const .i32 c) b).eval f = b.eval f ∧
      (Term.bin .i32 .and b (.const .i32 c)).eval f = b.eval f := by
  rcases isBool_eval (f := f) hb with h | ⟨p, h⟩
  · simp [Term.eval, h, binV]
  · have hk := bool32_and_odd p hc
    have hk' : bool32 p &&& BitVec.ofNat 32 c = bool32 p := by rw [BitVec.and_comm]; exact hk
    constructor
    · simp only [Term.eval, h, binV, Option.bind_some, asInt_intVal, intBinOp]
      exact congrArg (fun z => some (intVal .i32 z)) hk
    · simp only [Term.eval, h, binV, Option.bind_some, asInt_intVal, intBinOp]
      exact congrArg (fun z => some (intVal .i32 z)) hk'

theorem boolMask?_eval {f : Frame} {a b : Term} (h : boolMask? a = some b) :
    a.eval f = b.eval f := by
  unfold boolMask? at h
  split at h
  · split at h
    · rename_i hc; cases h; exact (and_bool_eval hc.1 hc.2).1
    · cases h
  · split at h
    · rename_i hc; cases h; exact (and_bool_eval hc.1 hc.2).2
    · cases h
  · cases h

/-! ## The second family -/

/-- **The second family of computed rewrites keeps the value.** -/
theorem comp2?_eval {f : Frame} {a b : Term} (h : comp2? a = some b) : a.eval f = b.eval f := by
  unfold comp2? at h
  split at h
  · rename_i b' h₁; cases h; exact boolMask?_eval h₁
  · split at h
    · rename_i b' h₁; cases h; exact shiftShift?_eval h₁
    · split at h
      · rename_i b' h₁; cases h; exact cmpZero?_eval h₁
      · split at h
        · rename_i b' h₁; cases h; exact signTest?_eval h₁
        · split at h
          · rename_i b' h₁; cases h; exact sremEqz?_eval h₁
          · exact sdivPow2?_eval h

/-! ## Divisions that cannot trap (for covers) -/

section Safe

variable {f : Frame}

theorem const_val {t t' : IntType} {n : Nat} {y : BitVec t.width}
    (h : (Term.const t' n).eval f = some (intVal t y)) (htt : t' = t) :
    y = BitVec.ofNat t.width n := by
  subst htt
  simp only [Term.eval, Option.some.injEq, intVal, Val.num.injEq] at h
  injection h with _ hb
  exact hb.symm

theorem ofNat_ne_of_mod {w n : Nat} {c : BitVec w} (hc : c.toNat ≠ n % 2 ^ w) :
    BitVec.ofNat w n ≠ c := by
  intro h; apply hc; rw [← h]; simp

/-- A binary operator that `safeBinOp` admits does not trap. -/
theorem intBinOp_ok_of_safe {t : IntType} {op : IntBinOp} {b : Term} {x y : BitVec t.width}
    (hs : safeBinOp t op b = true) (hb : b.eval f = some (intVal t y)) :
    ∃ z, intBinOp t op x y = .ok z := by
  cases op with
  | div sx =>
    cases b with
    | const t' n =>
      have htt : t' = t := by
        cases sx <;> simp only [safeBinOp, Bool.and_eq_true, beq_iff_eq] at hs <;>
          first | exact hs.1.symm | exact hs.1.1.symm
      have hy : y = BitVec.ofNat t.width n := const_val hb htt
      have hw : 0 < 2 ^ t.width := Nat.two_pow_pos _
      cases sx
      · simp only [safeBinOp, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs
        have hy0 : y ≠ 0 := by
          rw [hy]; exact ofNat_ne_of_mod (by simp; exact fun h => hs.1.2 h.symm)
        have hy1 : y ≠ -1 := by
          rw [hy]; refine ofNat_ne_of_mod ?_
          have h1' : (1 : BitVec t.width).toNat = 1 := by cases t <;> rfl
          rw [BitVec.toNat_neg, h1']
          have h1 : 1 < 2 ^ t.width := by cases t <;> decide
          rw [Nat.mod_eq_of_lt (by omega)]
          exact fun h => hs.2 h.symm
        have hy0' : ¬ y = 0#t.width := hy0
        have hy1' : ¬ y = -1#t.width := hy1
        exact ⟨x.sdiv y, by simp [intBinOp, hy0', hy1']⟩
      · simp only [safeBinOp, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs
        have hy0 : y ≠ 0 := by
          rw [hy]; exact ofNat_ne_of_mod (by simp; exact fun h => hs.2 h.symm)
        have hy0' : ¬ y = 0#t.width := hy0
        exact ⟨x / y, by simp [intBinOp, hy0']⟩
    | _ => cases sx <;> simp [safeBinOp] at hs
  | rem sx =>
    cases b with
    | const t' n =>
      have htt : t' = t := by
        cases sx <;> simp only [safeBinOp, Bool.and_eq_true, beq_iff_eq] at hs <;> exact hs.1.symm
      have hy : y = BitVec.ofNat t.width n := const_val hb htt
      have hn0 : n % 2 ^ t.width ≠ 0 := by
        cases sx <;> simp only [safeBinOp, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs <;>
          exact hs.2
      have hy0' : ¬ y = 0#t.width := by
        rw [hy]; exact ofNat_ne_of_mod (by simp; exact fun h => hn0 h.symm)
      cases sx
      · exact ⟨x.srem y, by simp [intBinOp, hy0']⟩
      · exact ⟨x % y, by simp [intBinOp, hy0']⟩
    | _ => cases sx <;> simp [safeBinOp] at hs
  | shr sx => cases sx <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

end Safe

end Silmaril.Proofs.Wasm.Auto.ESeg