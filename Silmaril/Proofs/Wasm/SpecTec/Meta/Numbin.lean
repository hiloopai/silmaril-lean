module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Prims
public import Mathlib.Data.Rat.Lemmas

/-!
# `$numbin` of the fixed script is `Num.bin` on `nat` and `int`

`numbin_spec`: for every operator and every pair of `nat`/`int` numerals, the clauses of
`$numbin` (after erratum M2) give `Num.bin`'s result, encoded, and fail definitely where `Num.bin`
is undefined. The unguarded cases are closed computations; the five guarded clauses (`SUB` and
`DIV`/`MOD` on `nat`, `DIV`/`MOD` on `int`) are walked: the earlier clauses miss, the guard is
decided, and the body evaluated.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-! ## `SUB` on `nat` -/

theorem numbinF_at4 :
    Rules.F.numbinF = Rules.F.numbinF.take 4 ++ Rules.F.nbSubNat :: Rules.F.numbinF.drop 5 := rfl

theorem nb_sub_nat_hit {a b : Nat} (h : b ≤ a) :
    TryClauses envF Rules.F.numbinF (nbArgs .subOp (.natN a) (.natN b))
      (encNum (.natN (a - b))) := by
  rw [numbinF_at4]
  refine tryClauses_append_miss (by miss_all) ?_
  refine tryClauses_hit (ρ₀ := nbScope "n_1" (.natN a) "n_2" (.natN b))
    ⟨10, by with_unfolding_all rfl⟩ (premsHold_ifPr ?_) ?_
  · exact evalExp_cmpNum (evalExp_var rfl) (evalExp_var rfl) (by simp [Num.cmp, h])
  · have h0 : (0 : Int) ≤ (a : Int) - (b : Int) := by omega
    have hc : Num.cvt .natT (.intN ((a : Int) - (b : Int))) = some (.natN (a - b)) := by
      simp only [Num.cvt, h0, ↓reduceIte, Option.some.injEq, Num.natN.injEq]; omega
    exact Equiv.evalExp_case_tup_one (evalExp_cvtNum (evalExp_binNum (evalExp_cvtNum
      (evalExp_var rfl) rfl) (evalExp_cvtNum (evalExp_var rfl) rfl) rfl) hc)

theorem nb_sub_nat_miss {a b : Nat} (h : ¬ b ≤ a) :
    TryUndef envF Rules.F.numbinF (nbArgs .subOp (.natN a) (.natN b)) := by
  rw [numbinF_at4]
  refine tryUndef_append_miss (by miss_all) ?_
  refine tryUndef_skip_prem (ρ₀ := nbScope "n_1" (.natN a) "n_2" (.natN b))
    ⟨10, by with_unfolding_all rfl⟩ (premsUndef_ifPr ?_) ⟨30, by with_unfolding_all rfl⟩
  exact evalExp_cmpNum (evalExp_var rfl) (evalExp_var rfl) (by simp [Num.cmp]; omega)

theorem nb_sub_nat (a b : Nat) : NB .subOp (.natN a) (.natN b) := by
  by_cases h : b ≤ a
  · have e : Num.bin .subOp (.natN a) (.natN b) = some (.natN (a - b)) := by simp [Num.bin, h]
    unfold NB; rw [e]; exact nb_sub_nat_hit h
  · have e : Num.bin .subOp (.natN a) (.natN b) = none := by simp [Num.bin, h]
    unfold NB; rw [e]; exact nb_sub_nat_miss h

/-! ## `DIV` -/

/-- Exact division of naturals, through `rat`. -/
theorem cvt_div_nat {a b : Nat} (h : a % b = 0) :
    Num.cvt .natT (.ratN ((a : ℚ) / (b : ℚ))) = some (.natN (a / b)) := by
  have hq : (a : ℚ) / (b : ℚ) = ((a / b : ℕ) : ℚ) :=
    (Rat.natCast_div a b (Nat.dvd_of_mod_eq_zero h)).symm
  rw [hq]
  simp only [Num.cvt, Rat.den_natCast, Rat.num_natCast, Int.natCast_nonneg, and_self,
    ↓reduceIte, Int.toNat_natCast]

/-- Exact division of integers, through `rat`. -/
theorem cvt_div_int {a b : Int} (h : a.tmod b = 0) :
    Num.cvt .intT (.ratN ((a : ℚ) / (b : ℚ))) = some (.intN (a.tdiv b)) := by
  have hd : b ∣ a := Int.dvd_of_tmod_eq_zero h
  have hq : (a : ℚ) / (b : ℚ) = ((a / b : ℤ) : ℚ) := (Rat.intCast_div a b hd).symm
  rw [hq, Int.tdiv_eq_ediv_of_dvd hd]
  simp [Num.cvt]

theorem bin_div_rat {p q : ℚ} (hq : q ≠ 0) : Num.bin .divOp (.ratN p) (.ratN q) = some (.ratN (p / q)) := by
  simp [Num.bin, hq]

theorem numbinF_at12 :
    Rules.F.numbinF = Rules.F.numbinF.take 12 ++ Rules.F.nbDivNat :: Rules.F.numbinF.drop 13 := rfl

theorem numbinF_at13 :
    Rules.F.numbinF = Rules.F.numbinF.take 13 ++ Rules.F.nbDivInt :: Rules.F.numbinF.drop 14 := rfl

/-- The guard of `DIV` on `nat`: `n_2 =/= 0 /\ n_1 \ n_2 = 0`. -/
theorem guard_div_nat {a b : Nat} (hb : b ≠ 0) :
    EvalExp envF (nbScope "n_1" (.natN a) "n_2" (.natN b))
      (.binE .andOp .boolT (.cmpE .neOp .boolT (.varE "n_2") (.numE (.natN 0)))
        (.cmpE .eqOp .boolT (.binE .modOp (.numT .natT) (.varE "n_1") (.varE "n_2"))
          (.numE (.natN 0)))) (.bool (decide (a % b = 0))) := by
  have h₁ := evalExp_ne_num (ρ := nbScope "n_1" (.natN a) "n_2" (.natN b)) (x := "n_2")
    (m := .natN b) (z := .natN 0) rfl evalExp_num (by simpa using hb)
  have hm : Num.bin .modOp (.natN a) (.natN b) = some (.natN (a % b)) := by simp [Num.bin, hb]
  have h₂ : EvalExp envF (nbScope "n_1" (.natN a) "n_2" (.natN b))
      (.cmpE .eqOp .boolT (.binE .modOp (.numT .natT) (.varE "n_1") (.varE "n_2"))
        (.numE (.natN 0))) (.bool (Value.num (.natN (a % b)) == Value.num (.natN 0))) :=
    evalExp_eq (evalExp_binNum (evalExp_var rfl) (evalExp_var rfl) hm) evalExp_num
  have hd : (Value.num (.natN (a % b)) == Value.num (.natN 0)) = decide (a % b = 0) := by
    by_cases h : a % b = 0 <;> simp [h]
  simpa only [hd, Bool.true_and] using evalExp_and (t := .boolT) h₁ h₂

theorem nb_div_nat_hit {a b : Nat} (hb : b ≠ 0) (h : a % b = 0) :
    TryClauses envF Rules.F.numbinF (nbArgs .divOp (.natN a) (.natN b))
      (encNum (.natN (a / b))) := by
  rw [numbinF_at12]
  refine tryClauses_append_miss (by miss_all) ?_
  refine tryClauses_hit (ρ₀ := nbScope "n_1" (.natN a) "n_2" (.natN b))
    ⟨10, by with_unfolding_all rfl⟩ (premsHold_ifPr ?_) ?_
  · simpa [h] using guard_div_nat (a := a) hb
  · have hq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    exact Equiv.evalExp_case_tup_one (evalExp_cvtNum (evalExp_binNum (evalExp_cvtNum
      (evalExp_var rfl) rfl) (evalExp_cvtNum (evalExp_var rfl) rfl) (bin_div_rat hq))
      (cvt_div_nat h))

theorem nb_div_nat_miss {a b : Nat} (hb : b ≠ 0) (h : a % b ≠ 0) :
    TryUndef envF Rules.F.numbinF (nbArgs .divOp (.natN a) (.natN b)) := by
  rw [numbinF_at12]
  refine tryUndef_append_miss (by miss_all) ?_
  refine tryUndef_skip_prem (ρ₀ := nbScope "n_1" (.natN a) "n_2" (.natN b))
    ⟨10, by with_unfolding_all rfl⟩ (premsUndef_ifPr ?_) ⟨30, by with_unfolding_all rfl⟩
  simpa [h] using guard_div_nat (a := a) hb

theorem nb_div_nat (a b : Nat) : NB .divOp (.natN a) (.natN b) := by
  unfold NB
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact ⟨30, by with_unfolding_all rfl⟩
  · have hb' : b ≠ 0 := Nat.pos_iff_ne_zero.1 hb
    by_cases h : a % b = 0
    · have e : Num.bin .divOp (.natN a) (.natN b) = some (.natN (a / b)) := by
        simp [Num.bin, hb', h]
      rw [e]; exact nb_div_nat_hit hb' h
    · have e : Num.bin .divOp (.natN a) (.natN b) = none := by simp [Num.bin, hb', h]
      rw [e]; exact nb_div_nat_miss hb' h

theorem evalExp_zeroInt {ρ : VarEnv} :
    EvalExp envF ρ (.cvtE (.numE (.natN 0)) .natT .intT) (.num (.intN 0)) :=
  evalExp_cvtNum evalExp_num rfl

/-- The guard of `DIV` on `int` (after M2): `i_2 =/= 0 /\ i_1 \ i_2 = 0`. -/
theorem guard_div_int {a b : Int} (hb : b ≠ 0) :
    EvalExp envF (nbScope "i_1" (.intN a) "i_2" (.intN b))
      (.binE .andOp .boolT (.cmpE .neOp .boolT (.varE "i_2") (.cvtE (.numE (.natN 0)) .natT .intT))
        (.cmpE .eqOp .boolT (.binE .modOp (.numT .intT) (.varE "i_1") (.varE "i_2"))
          (.cvtE (.numE (.natN 0)) .natT .intT))) (.bool (decide (a.tmod b = 0))) := by
  have h₁ := evalExp_ne_num (ρ := nbScope "i_1" (.intN a) "i_2" (.intN b)) (x := "i_2")
    (m := .intN b) (z := .intN 0) rfl evalExp_zeroInt (by simpa using hb)
  have hm : Num.bin .modOp (.intN a) (.intN b) = some (.intN (a.tmod b)) := by simp [Num.bin, hb]
  have h₂ : EvalExp envF (nbScope "i_1" (.intN a) "i_2" (.intN b))
      (.cmpE .eqOp .boolT (.binE .modOp (.numT .intT) (.varE "i_1") (.varE "i_2"))
        (.cvtE (.numE (.natN 0)) .natT .intT))
      (.bool (Value.num (.intN (a.tmod b)) == Value.num (.intN 0))) :=
    evalExp_eq (evalExp_binNum (evalExp_var rfl) (evalExp_var rfl) hm) evalExp_zeroInt
  have hd : (Value.num (.intN (a.tmod b)) == Value.num (.intN 0)) = decide (a.tmod b = 0) := by
    by_cases h : a.tmod b = 0 <;> simp [h]
  simpa only [hd, Bool.true_and] using evalExp_and (t := .boolT) h₁ h₂

theorem nb_div_int_hit {a b : Int} (hb : b ≠ 0) (h : a.tmod b = 0) :
    TryClauses envF Rules.F.numbinF (nbArgs .divOp (.intN a) (.intN b))
      (encNum (.intN (a.tdiv b))) := by
  rw [numbinF_at13]
  refine tryClauses_append_miss (by miss_all) ?_
  refine tryClauses_hit (ρ₀ := nbScope "i_1" (.intN a) "i_2" (.intN b))
    ⟨10, by with_unfolding_all rfl⟩ (premsHold_ifPr ?_) ?_
  · simpa [h] using guard_div_int (a := a) hb
  · have hq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    exact Equiv.evalExp_case_tup_one (evalExp_cvtNum (evalExp_binNum (evalExp_cvtNum
      (evalExp_var rfl) rfl) (evalExp_cvtNum (evalExp_var rfl) rfl) (bin_div_rat hq))
      (cvt_div_int h))

theorem nb_div_int_miss {a b : Int} (hb : b ≠ 0) (h : a.tmod b ≠ 0) :
    TryUndef envF Rules.F.numbinF (nbArgs .divOp (.intN a) (.intN b)) := by
  rw [numbinF_at13]
  refine tryUndef_append_miss (by miss_all) ?_
  refine tryUndef_skip_prem (ρ₀ := nbScope "i_1" (.intN a) "i_2" (.intN b))
    ⟨10, by with_unfolding_all rfl⟩ (premsUndef_ifPr ?_) ⟨30, by with_unfolding_all rfl⟩
  simpa [h] using guard_div_int (a := a) hb

theorem nb_div_int (a b : Int) : NB .divOp (.intN a) (.intN b) := by
  unfold NB
  by_cases hb : b = 0
  · subst hb; exact ⟨30, by with_unfolding_all rfl⟩
  · by_cases h : a.tmod b = 0
    · have e : Num.bin .divOp (.intN a) (.intN b) = some (.intN (a.tdiv b)) := by
        simp [Num.bin, hb, h]
      rw [e]; exact nb_div_int_hit hb h
    · have e : Num.bin .divOp (.intN a) (.intN b) = none := by simp [Num.bin, hb, h]
      rw [e]; exact nb_div_int_miss hb h

/-! ## `MOD` -/

theorem numbinF_at16 :
    Rules.F.numbinF = Rules.F.numbinF.take 16 ++ Rules.F.nbModNat :: Rules.F.numbinF.drop 17 := rfl

theorem numbinF_at17 :
    Rules.F.numbinF = Rules.F.numbinF.take 17 ++ Rules.F.nbModInt :: Rules.F.numbinF.drop 18 := rfl

theorem nb_mod_nat_hit {a b : Nat} (hb : b ≠ 0) :
    TryClauses envF Rules.F.numbinF (nbArgs .modOp (.natN a) (.natN b))
      (encNum (.natN (a % b))) := by
  rw [numbinF_at16]
  refine tryClauses_append_miss (by miss_all) ?_
  have hm : Num.bin .modOp (.natN a) (.natN b) = some (.natN (a % b)) := by simp [Num.bin, hb]
  have hg := evalExp_ne_num (ρ := nbScope "n_1" (.natN a) "n_2" (.natN b)) (x := "n_2")
    (m := .natN b) (z := .natN 0) rfl evalExp_num (by simpa using hb)
  exact tryClauses_hit (ρ₀ := nbScope "n_1" (.natN a) "n_2" (.natN b))
    ⟨10, by with_unfolding_all rfl⟩ (premsHold_ifPr hg)
    (Equiv.evalExp_case_tup_one (evalExp_binNum (evalExp_var rfl) (evalExp_var rfl) hm))

theorem nb_mod_nat (a b : Nat) : NB .modOp (.natN a) (.natN b) := by
  unfold NB
  by_cases hb : b = 0
  · subst hb; exact ⟨30, by with_unfolding_all rfl⟩
  · have e : Num.bin .modOp (.natN a) (.natN b) = some (.natN (a % b)) := by simp [Num.bin, hb]
    rw [e]; exact nb_mod_nat_hit hb

theorem nb_mod_int_hit {a b : Int} (hb : b ≠ 0) :
    TryClauses envF Rules.F.numbinF (nbArgs .modOp (.intN a) (.intN b))
      (encNum (.intN (a.tmod b))) := by
  rw [numbinF_at17]
  refine tryClauses_append_miss (by miss_all) ?_
  have hm : Num.bin .modOp (.intN a) (.intN b) = some (.intN (a.tmod b)) := by simp [Num.bin, hb]
  have hg := evalExp_ne_num (ρ := nbScope "i_1" (.intN a) "i_2" (.intN b)) (x := "i_2")
    (m := .intN b) (z := .intN 0) rfl evalExp_zeroInt (by simpa using hb)
  exact tryClauses_hit (ρ₀ := nbScope "i_1" (.intN a) "i_2" (.intN b))
    ⟨10, by with_unfolding_all rfl⟩ (premsHold_ifPr hg)
    (Equiv.evalExp_case_tup_one (evalExp_binNum (evalExp_var rfl) (evalExp_var rfl) hm))

theorem nb_mod_int (a b : Int) : NB .modOp (.intN a) (.intN b) := by
  unfold NB
  by_cases hb : b = 0
  · subst hb; exact ⟨30, by with_unfolding_all rfl⟩
  · have e : Num.bin .modOp (.intN a) (.intN b) = some (.intN (a.tmod b)) := by simp [Num.bin, hb]
    rw [e]; exact nb_mod_int_hit hb

/-! ## All operators -/

theorem numbin_nat_nat (op : BinOp) (a b : Nat) : NB op (.natN a) (.natN b) := by
  cases op
  case subOp => exact nb_sub_nat a b
  case divOp => exact nb_div_nat a b
  case modOp => exact nb_mod_nat a b
  all_goals exact ⟨30, by with_unfolding_all rfl⟩

theorem numbin_int_int (op : BinOp) (hop : op ≠ .powOp) (a b : Int) :
    NB op (.intN a) (.intN b) := by
  cases op
  case divOp => exact nb_div_int a b
  case modOp => exact nb_mod_int a b
  case powOp => exact absurd rfl hop
  all_goals exact ⟨30, by with_unfolding_all rfl⟩

/-- `POW` on `int` never evaluates: its body raises a `rat` to an `int` power, which
`Num.bin` (like `Xl.Num.bin`) does not compute. -/
theorem numbin_pow_int (a b : Int) :
    TryUndef envF Rules.F.numbinF (nbArgs .powOp (.intN a) (.intN b)) := by
  cases b <;> exact ⟨30, by with_unfolding_all rfl⟩

theorem numbin_nat_int (op : BinOp) (a : Nat) (b : Int) : NB op (.natN a) (.intN b) := by
  cases op <;> exact ⟨30, by with_unfolding_all rfl⟩

theorem numbin_int_nat (op : BinOp) (a : Int) (b : Nat) : NB op (.intN a) (.natN b) := by
  cases op <;> exact ⟨30, by with_unfolding_all rfl⟩

/-- `pow` on two `int`s: the one place where SpecTec's typing and evaluation of `pow` differ. -/
def IntPow (op : BinOp) (a b : Num) : Prop :=
  op = .powOp ∧ (∃ i, a = .intN i) ∧ ∃ j, b = .intN j

/-- **`$numbin` is `Num.bin`** on `nat` and `int` numerals, in the fixed script, except `pow`
on two `int`s. -/
theorem numbin_spec (op : BinOp) {a b : Num} (ha : NatInt a) (hb : NatInt b)
    (hp : ¬ IntPow op a b) : NB op a b := by
  cases a <;> cases b <;> simp only [NatInt] at ha hb
  · exact numbin_nat_nat op _ _
  · exact numbin_nat_int op _ _
  · exact numbin_int_nat op _ _
  · exact numbin_int_int op (fun h => hp ⟨h, ⟨_, rfl⟩, ⟨_, rfl⟩⟩) _ _

/-- Whatever `$numbin` computes on `nat`/`int` numerals is what `Num.bin` computes. -/
theorem numbin_le (op : BinOp) {a b : Num} (ha : NatInt a) (hb : NatInt b) {w : Value}
    (h : TryClauses envF Rules.F.numbinF (nbArgs op a b) w) :
    (Num.bin op a b).map encNum = some w := by
  by_cases hp : IntPow op a b
  · obtain ⟨rfl, ⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hp
    exact absurd h (TryUndef.not (numbin_pow_int i j))
  · exact (numbin_spec op ha hb hp).iff.1 h

/-! ## The other primitives -/

/-- The definition of `f` in `fixed` (a dummy if there is none). -/
noncomputable def fdef (f : IL.Id) : DefDef := (envF.findDef? f).getD ([], .boolT, [])

theorem findDef_fdef {f : IL.Id} (h : (envF.findDef? f).isSome = true) :
    envF.findDef? f = some (fdef f) := by
  unfold fdef
  cases e : envF.findDef? f with
  | none => rw [e] at h; cases h
  | some d => rfl

theorem findDef_numbin : envF.findDef? "numbin" = some ((fdef "numbin").1,
    (fdef "numbin").2.1, Rules.F.numbinF) := by
  rw [findDef_fdef rfl]; rfl

theorem builtins_envF (f : IL.Id) (ws : List ArgV) : envF.builtins.call f ws = none := rfl

theorem boolun_spec (op : UnOp) (b : Bool) :
    Spec envF (fdef "boolun").2.2 (args2 (encUnOp op) (.bool b)) (FExp.resVal (unValue op (.bool b))) := by
  cases op <;> cases b <;> exact ⟨20, by with_unfolding_all rfl⟩

theorem boolbin_spec (op : BinOp) (b₁ b₂ : Bool) :
    Spec envF (fdef "boolbin").2.2 (args3 (encBinOp op) (.bool b₁) (.bool b₂))
      (FExp.resVal (binValues op (.bool b₁) (.bool b₂))) := by
  cases op <;> cases b₁ <;> cases b₂ <;> exact ⟨20, by with_unfolding_all rfl⟩

theorem numun_spec (op : UnOp) {m : Num} (hm : NatInt m) :
    Spec envF (fdef "numun").2.2 (args2 (encUnOp op) (encNum m)) ((Num.un op m).map encNum) := by
  cases m <;> simp only [NatInt] at hm <;> cases op <;> exact ⟨20, by with_unfolding_all rfl⟩

theorem numcmp_spec (op : CmpOp) {a b : Num} (ha : NatInt a) (hb : NatInt b) :
    Spec envF (fdef "numcmp").2.2 (args3 (encCmpOp op) (encNum a) (encNum b))
      ((Num.cmp op a b).map .bool) := by
  cases a <;> cases b <;> simp only [NatInt] at ha hb <;> cases op <;>
    exact ⟨30, by with_unfolding_all rfl⟩

end Silmaril.Wasm.SpecTec.Meta
