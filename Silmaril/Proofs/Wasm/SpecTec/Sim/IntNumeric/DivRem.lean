module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Calls

/-!
# Integer numerics: `$idiv_` and `$irem_` at a non-zero divisor

The pinned `$idiv_`/`$irem_` are written with `$truncz`, which `B` supplies (`truncQ`, rounding
towards zero). The unsigned clauses and the signed `$idiv_` clauses then evaluate as written. The
signed non-zero clause of `$irem_` binds `j_1`, `j_2` only in an `if` premise, so it definitely
fails and every clause of `$irem_` fails there: `callDef` takes `B`'s answer, `IntegerN.irem_`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV intV bvV optUNV NumEnv)
open Silmaril.Wasm.Numerics

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

/-! ## Truncation of a quotient -/

/-- A quotient of naturals truncates to the natural quotient. -/
theorem truncQ_natDiv (a b : ℕ) : truncQ ((a : ℚ) / (b : ℚ)) = ((a / b : ℕ) : ℤ) := by
  have h0 : (0 : ℚ) ≤ (a : ℚ) / (b : ℚ) := by positivity
  simp only [truncQ, h0, ite_true]
  exact Rat.floor_natCast_div_natCast a b

/-- A quotient of integers by a positive natural truncates to `Int.tdiv`. -/
theorem truncQ_intDiv_pos (a : ℤ) (d : ℕ) (hd : 0 < d) :
    truncQ ((a : ℚ) / (d : ℚ)) = a.tdiv d := by
  rcases le_or_gt 0 a with ha | ha
  · have h0 : (0 : ℚ) ≤ (a : ℚ) / (d : ℚ) := by positivity
    simp only [truncQ, h0, ite_true, Rat.floor_intCast_div_natCast]
    exact (Int.tdiv_eq_ediv_of_nonneg ha).symm
  · have h0 : ¬ (0 : ℚ) ≤ (a : ℚ) / (d : ℚ) := by
      rw [not_le]; apply div_neg_of_neg_of_pos <;> [exact_mod_cast ha; exact_mod_cast hd]
    simp only [truncQ, h0, ite_false]
    have hc : ⌈(a : ℚ) / d⌉ = -⌊((-a : ℤ) : ℚ) / d⌋ := by
      rw [show ((-a : ℤ) : ℚ) / d = -((a : ℚ) / d) by push_cast; ring, Int.floor_neg, neg_neg]
    rw [hc, Rat.floor_intCast_div_natCast]
    have hna : 0 ≤ -a := by omega
    rw [← Int.tdiv_eq_ediv_of_nonneg hna, Int.neg_tdiv, neg_neg]

/-- A quotient of integers truncates to `Int.tdiv`. -/
theorem truncQ_intDiv (a b : ℤ) (hb : b ≠ 0) : truncQ ((a : ℚ) / (b : ℚ)) = a.tdiv b := by
  rcases lt_or_gt_of_ne hb with hb | hb
  · have hn : (((-b).toNat : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
    have e : (a : ℚ) / (b : ℚ) = ((-a : ℤ) : ℚ) / (((-b).toNat : ℕ) : ℚ) := by
      rw [show (((-b).toNat : ℕ) : ℚ) = ((-b : ℤ) : ℚ) by exact_mod_cast hn]
      push_cast; rw [neg_div_neg_eq]
    rw [e, truncQ_intDiv_pos _ _ (by omega), hn, Int.tdiv_neg, Int.neg_tdiv, neg_neg]
  · have hn : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (by omega)
    have e : (a : ℚ) / (b : ℚ) = (a : ℚ) / ((b.toNat : ℕ) : ℚ) := by
      rw [show ((b.toNat : ℕ) : ℚ) = ((b : ℤ) : ℚ) by exact_mod_cast hn]
    rw [e, truncQ_intDiv_pos _ _ (by omega), hn]

variable {B : Builtins}

/-- The `$idiv_` overflow test, on rationals as the script states it, is `IntegerN`'s test on
the truncated quotient: both hold exactly at `-2^(N-1) / -1`. -/
theorem overflow_iff (M : ℕ) (a b : ℤ) (ha₁ : -(M : ℤ) ≤ a) (ha₂ : a < M) (hb : b ≠ 0) :
    ((a : ℚ) / (b : ℚ) = ((M : ℕ) : ℚ)) ↔ a.tdiv b = M := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · show a.tdiv b = M
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have h' : (a : ℚ) = (M : ℚ) * b := (div_eq_iff hbq).1 h
    have h'' : a = (M : ℤ) * b := by exact_mod_cast h'
    rw [h'', Int.mul_tdiv_cancel _ hb]
  · show (a : ℚ) / (b : ℚ) = ((M : ℕ) : ℚ)
    have h1 : M = a.natAbs / b.natAbs := by
      have h0 := Int.natAbs_tdiv a b
      rw [h, Int.natAbs_natCast] at h0
      exact h0
    have hab : a.natAbs ≤ M := by omega
    have hb1 : b.natAbs = 1 := by
      by_contra hne
      have h2 : 2 ≤ b.natAbs := by have := Int.natAbs_pos.2 hb; omega
      have : a.natAbs / b.natAbs ≤ a.natAbs / 2 := Nat.div_le_div_left h2 (by norm_num)
      omega
    rcases Int.natAbs_eq_iff.1 hb1 with hb' | hb' <;> subst hb'
    · have ha : a = M := by simpa using h
      simp [ha]
    · have ha : a = -(M : ℤ) := by
        have h3 : -a = M := by simpa using h
        omega
      rw [ha]; push_cast; ring

/-- Equality of rationals, as the evaluator decides it on values. -/
theorem ratV_beq (a b : ℚ) : (Value.num (.ratN a) == Value.num (.ratN b)) = decide (a = b) := by
  by_cases hab : a = b
  · subst hab; simp
  · simp only [hab, decide_false]
    exact beq_eq_false_iff_ne.2 (by simp [hab])

/-! ## The unsigned clauses -/

/-- The scope an `$idiv_`/`$irem_` clause binds (`N`, `i_1`, `i_2`). -/
def scopeDiv (N : Nat) (c₁ c₂ : Value) : VarEnv :=
  ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" c₁).bindVal "i_2" c₂

/-- `$truncz(i_1 / i_2)` on the payloads of two bit patterns, with `i_2 ≠ 0`. -/
theorem evalExp_truncNat (hB : IntB B) {N : Nat} (x y : BitVec N) (hy : y ≠ 0) :
    EvalExp (simEnv B) (scopeDiv N (bvV x) (bvV y))
      (.cvtE (.callE "truncz" [.expA (.binE .divOp (.numT .ratT)
        (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
        (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))]) .intT .natT)
      (natV (x.toNat / y.toNat)) := by
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hx : EvalExp (simEnv B) (scopeDiv N (bvV x) (bvV y))
      (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT) (.num (.ratN (x.toNat : ℚ))) :=
    evalExp_cvtNum (Equiv.evalExp_uNV_payload (by simp [scopeDiv])) rfl
  have hyq : EvalExp (simEnv B) (scopeDiv N (bvV x) (bvV y))
      (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT) (.num (.ratN (y.toNat : ℚ))) :=
    evalExp_cvtNum (Equiv.evalExp_uNV_payload (by simp [scopeDiv])) rfl
  have hq : EvalExp (simEnv B) (scopeDiv N (bvV x) (bvV y))
      (.binE .divOp (.numT .ratT) (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
        (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))
      (.num (.ratN ((x.toNat : ℚ) / (y.toNat : ℚ)))) :=
    evalExp_binNum hx hyq (by simp [Num.bin, hy'])
  have ht : CallDef (simEnv B) (scopeDiv N (bvV x) (bvV y)) "truncz"
      [.expA (.binE .divOp (.numT .ratT) (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
        (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))]
      (.num (.intN ((x.toNat / y.toNat : ℕ) : ℤ))) := by
    refine callDef_prim hB (noClauses_truncz B) rfl (Equiv.evalArgs_cons hq Equiv.evalArgs_nil) ?_
    simp [intCall, truncQ_natDiv]
  exact evalExp_cvtNum (evalExp_callE_iff.2 ht)
    (by simp only [Num.cvt, Int.natCast_nonneg, ite_true, Int.toNat_natCast])


/-- A bit pattern built from a small natural is that natural's `%`-injection. -/
theorem bvV_ofNat {N k : Nat} (h : k < 2 ^ N) :
    bvV (BitVec.ofNat N k) = .case "%" (.tuple [natV k]) := by
  simp [bvV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A divisor pattern `%(0)` definitely fails on a non-zero bit pattern. -/
theorem matchExp_zero_undef {env : Env} {ρ : VarEnv} {N : Nat} {y : BitVec N} (hy : y ≠ 0) :
    MatchExpUndef env ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (bvV y) := by
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  exact matchExp_caseE_undef' (matchExp_tupE_one_undef (matchExp_numE_undef
    (by simpa [natV] using hy')))

/-- The `sx` pattern of a clause for the other signedness definitely fails. -/
theorem matchArgs_sxSkip {env : Env} {N : Nat} {op op' : MixopS} {pats : List Arg}
    {w : Value} {ws : List ArgV} (hop : op ≠ op') :
    MatchArgsUndef env VarEnv.empty (.expA (.varE "N") :: .expA (.caseE op' (.tupE [])) :: pats)
      (.val (natV N) :: .val (.case op w) :: ws) :=
  matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hop)))

/-- The zero-divisor clause of the same signedness is skipped at a non-zero divisor. -/
theorem matchArgs_zeroSkip {env : Env} {N : Nat} {op : MixopS} {x y : BitVec N} (hy : y ≠ 0) :
    MatchArgsUndef env VarEnv.empty
      [.expA (.varE "N"), .expA (.caseE op (.tupE [])), .expA (.varE "i_1"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]
      [.val (natV N), .val (.case op (.tuple [])), .val (bvV x), .val (bvV y)] :=
  matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons_undef_tail (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      (matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons_undef (matchArg_expA_undef (matchExp_zero_undef hy)))))

/-- The general clause of a signedness matches. -/
theorem matchArgs_divGen {env : Env} {N : Nat} {op : MixopS} {c₁ c₂ : Value} :
    MatchArgs env VarEnv.empty
      [.expA (.varE "N"), .expA (.caseE op (.tupE [])), .expA (.varE "i_1"), .expA (.varE "i_2")]
      [.val (natV N), .val (.case op (.tuple [])), .val c₁, .val c₂] (scopeDiv N c₁ c₂) :=
  matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))

/-- **`$idiv_(N, U, i_1, i_2)`** at `i_2 ≠ 0`: `IntegerN.idiv_`, through `$truncz`. -/
theorem callDef_idiv_u (hB : IntB B) {ρ : VarEnv} {args : List Arg} {N : Nat}
    (x y : BitVec N) (hy : y ≠ 0) (hρ : ρ.findDef? "idiv_" = none)
    (ha : EvalArgs (simEnv B) ρ args
      [.val (natV N), .val (Equiv.sxV .unsigned), .val (bvV x), .val (bvV y)]) :
    CallDef (simEnv B) ρ "idiv_" args (optUNV (idiv_ N .unsigned x y)) := by
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hlt : x.toNat / y.toNat < 2 ^ N := lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
  have hv : optUNV (idiv_ N .unsigned x y) =
      .opt (some (.case "%" (.tuple [natV (x.toNat / y.toNat)]))) := by
    simp [optUNV, idiv_, hy', bvV_ofNat hlt]
  rw [hv]
  refine callDef_of_tryClauses hρ (numEnv_simEnv B).idivD ha ?_
  refine tryClauses_skip_match (matchArgs_zeroSkip hy) ?_
  exact tryClauses_hit matchArgs_divGen premsHold_nil (evalExp_optE_some_iff.2
    ⟨_, Equiv.evalExp_case_tup_one (evalExp_truncNat hB x y hy), rfl⟩)

/-- **`$irem_(N, U, i_1, i_2)`** at `i_2 ≠ 0`: `IntegerN.irem_`, through `$truncz`. -/
theorem callDef_irem_u (hB : IntB B) {ρ : VarEnv} {args : List Arg} {N : Nat}
    (x y : BitVec N) (hy : y ≠ 0) (hρ : ρ.findDef? "irem_" = none)
    (ha : EvalArgs (simEnv B) ρ args
      [.val (natV N), .val (Equiv.sxV .unsigned), .val (bvV x), .val (bvV y)]) :
    CallDef (simEnv B) ρ "irem_" args (optUNV (irem_ N .unsigned x y)) := by
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hle : y.toNat * (x.toNat / y.toNat) ≤ x.toNat := Nat.mul_div_le _ _
  have hlt : x.toNat - y.toNat * (x.toNat / y.toNat) < 2 ^ N :=
    lt_of_le_of_lt (Nat.sub_le _ _) x.isLt
  have hv : optUNV (irem_ N .unsigned x y) =
      .opt (some (.case "%" (.tuple [natV (x.toNat - y.toNat * (x.toNat / y.toNat))]))) := by
    simp [optUNV, irem_, hy', bvV_ofNat hlt]
  rw [hv]
  refine callDef_of_tryClauses hρ (numEnv_simEnv B).iremD ha ?_
  refine tryClauses_skip_match (matchArgs_zeroSkip hy) ?_
  have hmul : EvalExp (simEnv B) (scopeDiv N (bvV x) (bvV y))
      (.binE .mulOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") 0)
        (.cvtE (.callE "truncz" [.expA (.binE .divOp (.numT .ratT)
          (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
          (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))]) .intT .natT))
      (natV (y.toNat * (x.toNat / y.toNat))) :=
    evalExp_binNum (Equiv.evalExp_uNV_payload (by simp [scopeDiv])) (evalExp_truncNat hB x y hy)
      rfl
  have hsub : EvalExp (simEnv B) (scopeDiv N (bvV x) (bvV y))
      (.binE .subOp (.numT .intT) (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .intT)
        (.cvtE (.binE .mulOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") 0)
          (.cvtE (.callE "truncz" [.expA (.binE .divOp (.numT .ratT)
            (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
            (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))]) .intT .natT))
          .natT .intT))
      (intV ((x.toNat : ℤ) - ((y.toNat * (x.toNat / y.toNat) : ℕ) : ℤ))) :=
    evalExp_binNum (Equiv.evalExp_toInt (Equiv.evalExp_uNV_payload (by simp [scopeDiv])))
      (Equiv.evalExp_toInt hmul) rfl
  have hnat := Equiv.evalExp_toNat (by omega) hsub
  rw [show ((x.toNat : ℤ) - ((y.toNat * (x.toNat / y.toNat) : ℕ) : ℤ)).toNat =
    x.toNat - y.toNat * (x.toNat / y.toNat) by omega] at hnat
  exact tryClauses_hit matchArgs_divGen premsHold_nil (evalExp_optE_some_iff.2
    ⟨_, Equiv.evalExp_case_tup_one hnat, rfl⟩)


/-! ## The signed clause of `$irem_`, and the fallback to `B` -/

/-- Every clause of an empty list definitely fails. -/
theorem tryClausesUndef_nil {env : Env} {ws : List ArgV} :
    Equiv.ExecNumeric.TryClausesUndef env [] ws :=
  ⟨1, by simp [tryClauses]⟩

/-- A clause skipped on its patterns does not change definite failure. -/
theorem tryClausesUndef_skip_match {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV}
    (hm : MatchArgsUndef env VarEnv.empty pats ws)
    (hrest : Equiv.ExecNumeric.TryClausesUndef env cs ws) :
    Equiv.ExecNumeric.TryClausesUndef env (.defD q pats e prems :: cs) ws := by
  obtain ⟨n₁, hm⟩ := hm
  obtain ⟨n₂, hrest⟩ := hrest
  refine ⟨max n₁ n₂ + 1, ?_⟩
  have e1 := matchArgs_undef_of_le (m := n₁) (n := max n₁ n₂) (by omega) hm
  have e2 := tryClauses_undef_of_le (m := n₂) (n := max n₁ n₂) (by omega) hrest
  simp only [tryClauses, e1, Bind.bind, Except.bind, Res.elimUndef_undef, e2]

/-- A clause skipped on its premises does not change definite failure. -/
theorem tryClausesUndef_skip_prem {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV} {ρ₀ : VarEnv}
    (hm : MatchArgs env VarEnv.empty pats ws ρ₀) (hp : PremsUndef env ρ₀ prems)
    (hrest : Equiv.ExecNumeric.TryClausesUndef env cs ws) :
    Equiv.ExecNumeric.TryClausesUndef env (.defD q pats e prems :: cs) ws := by
  obtain ⟨n₁, hm⟩ := hm
  obtain ⟨n₂, hp⟩ := hp
  obtain ⟨n₃, hrest⟩ := hrest
  refine ⟨max (max n₁ n₂) n₃ + 1, ?_⟩
  have e1 := matchArgs_ok_of_le (m := n₁) (n := max (max n₁ n₂) n₃) (by omega) hm
  have e2 := premsHold_undef_of_le (m := n₂) (n := max (max n₁ n₂) n₃) (by omega) hp
  have e3 := tryClauses_undef_of_le (m := n₃) (n := max (max n₁ n₂) n₃) (by omega) hrest
  simp only [tryClauses, e1, Bind.bind, Except.bind, e2, Res.elimUndef_undef, e3]

/-- `if j_1 = … ∧ …` with `j_1` unbound: the evaluator cannot run it, a definite failure. -/
theorem premsUndef_unboundAnd {env : Env} {ρ : VarEnv} {x : IL.Id} {e₁ e₂ : Exp} {t₁ t₂ : OpTyp}
    (hx : ρ.findVal? x = none) :
    PremsUndef env ρ [.ifPr (.binE .andOp t₁ (.cmpE .eqOp t₂ (.varE x) e₁) e₂)] :=
  ⟨5, by simp [premsHold, premHolds, evalExp, hx, Res.ofOption, Bind.bind, Except.bind]⟩

/-- **`$irem_(N, S, i_1, i_2)`** at `i_2 ≠ 0`: the script's clause cannot be evaluated, every
clause of `$irem_` definitely fails, and `callDef` takes `B`'s answer, `IntegerN.irem_`. -/
theorem callDef_irem_s (hB : IntB B) {ρ : VarEnv} {args : List Arg} {N : Nat}
    (x y : BitVec N) (hy : y ≠ 0) (hρ : ρ.findDef? "irem_" = none)
    (ha : EvalArgs (simEnv B) ρ args
      [.val (natV N), .val (Equiv.sxV .signed), .val (bvV x), .val (bvV y)]) :
    CallDef (simEnv B) ρ "irem_" args (optUNV (irem_ N .signed x y)) := by
  have hb : (simEnv B).builtins.call "irem_"
      [.val (natV N), .val (Equiv.sxV .signed), .val (bvV x), .val (bvV y)] =
      some (optUNV (irem_ N .signed x y)) :=
    hB _ _ _ (by simp [intCall, remBits, natV, asSx?, Equiv.sxV, optUNV])
  have hu : Equiv.ExecNumeric.TryClausesUndef (simEnv B) Equiv.iremDef.2.2
      [.val (natV N), .val (Equiv.sxV .signed), .val (bvV x), .val (bvV y)] := by
    refine tryClausesUndef_skip_match (matchArgs_sxSkip (by decide)) ?_
    refine tryClausesUndef_skip_match (matchArgs_sxSkip (by decide)) ?_
    refine tryClausesUndef_skip_match (matchArgs_zeroSkip hy) ?_
    exact tryClausesUndef_skip_prem matchArgs_divGen (premsUndef_unboundAnd (by simp [scopeDiv]))
      tryClausesUndef_nil
  exact Equiv.ExecNumeric.callDef_iff.2 ⟨_, _, _, _, ha, by rw [hρ]; exact
    (numEnv_simEnv B).iremD, Or.inr ⟨hu, by rw [hρ]; exact hb⟩⟩


/-! ## The signed clauses of `$idiv_` -/

/-- `$signed_(N, i!%.0)`, read as a rational, for a variable holding a bit pattern. -/
theorem evalExp_signedQ {ρ : VarEnv} {N : Nat} (hN : 0 < N) {x : BitVec N} {i : IL.Id}
    (hNv : ρ.findVal? "N" = some (natV N)) (hi : ρ.findVal? i = some (bvV x))
    (hρ : ρ.findDef? "signed_" = none) :
    EvalExp (simEnv B) ρ (.cvtE (.callE "signed_" [.expA (.varE "N"),
        .expA (.projE (.uncaseE (.varE i) "%") 0)]) .intT .ratT)
      (.num (.ratN ((signed_ N x.toNat : ℤ) : ℚ))) :=
  evalExp_cvtNum (evalExp_callE_iff.2 (Equiv.callDef_signed (numEnv_simEnv B) hρ
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hNv)
      (Equiv.evalArgs_cons (Equiv.evalExp_uNV_payload hi) Equiv.evalArgs_nil)) hN x.isLt)) rfl

/-- **`$idiv_(N, S, i_1, i_2)`** at `i_2 ≠ 0`: `IntegerN.idiv_`. The overflow clause fires
exactly at `-2^(N-1) / -1`; otherwise the general clause computes through `$truncz` and
`$inv_signed_`. -/
theorem callDef_idiv_s (hB : IntB B) {ρ : VarEnv} {args : List Arg} {N : Nat} (hN : 0 < N)
    (x y : BitVec N) (hy : y ≠ 0) (hρ : ρ.findDef? "idiv_" = none)
    (ha : EvalArgs (simEnv B) ρ args
      [.val (natV N), .val (Equiv.sxV .signed), .val (bvV x), .val (bvV y)]) :
    CallDef (simEnv B) ρ "idiv_" args (optUNV (idiv_ N .signed x y)) := by
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hj2 : signed_ N y.toNat ≠ 0 := by
    rw [signed_toNat]
    intro h
    exact hy (BitVec.toInt_inj.1 (by rw [h]; simp))
  obtain ⟨hx₁, hx₂⟩ := Equiv.signed_bounds hN x.isLt
  have hM : ((2 ^ (N - 1) : ℕ) : ℤ) = 2 ^ (N - 1) := by push_cast; rfl
  have hov := overflow_iff (2 ^ (N - 1)) (signed_ N x.toNat) (signed_ N y.toNat)
    (by rw [hM]; exact hx₁) (by rw [hM]; exact hx₂) hj2
  set σ := scopeDiv N (bvV x) (bvV y) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by simp [hσ, scopeDiv]
  have hq : EvalExp (simEnv B) σ
      (.binE .divOp (.numT .ratT)
        (.cvtE (.callE "signed_" [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          .intT .ratT)
        (.cvtE (.callE "signed_" [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          .intT .ratT))
      (.num (.ratN (((signed_ N x.toNat : ℤ) : ℚ) / ((signed_ N y.toNat : ℤ) : ℚ)))) :=
    evalExp_binNum (evalExp_signedQ (x := x) (i := "i_1") hN hNv (by simp [hσ, scopeDiv]) rfl)
      (evalExp_signedQ (x := y) (i := "i_2") hN hNv (by simp [hσ, scopeDiv]) rfl)
      (by simp [Num.bin, hj2])
  have hpow : EvalExp (simEnv B) σ
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE .subOp (.numT .intT)
        (.cvtE (.varE "N") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT))
        .natT .ratT)
      (.num (.ratN (((2 ^ (N - 1) : ℕ) : ℚ)))) :=
    evalExp_cvtNum (Equiv.evalExp_twoPowPred hN hNv) rfl
  have hcmp := evalExp_eq (t := .boolT) hq hpow
  rw [ratV_beq] at hcmp
  refine callDef_of_tryClauses hρ (numEnv_simEnv B).idivD ha ?_
  refine tryClauses_skip_match (matchArgs_sxSkip (by decide)) ?_
  refine tryClauses_skip_match (matchArgs_sxSkip (by decide)) ?_
  refine tryClauses_skip_match (matchArgs_zeroSkip hy) ?_
  by_cases hq₀ : ((signed_ N x.toNat : ℤ) : ℚ) / ((signed_ N y.toNat : ℤ) : ℚ) =
      ((2 ^ (N - 1) : ℕ) : ℚ)
  · show TryClauses (simEnv B) _ _ (optUNV (idiv_ N .signed x y))
    have hnone : idiv_ N .signed x y = none := by
      have ht := hov.1 hq₀
      rw [hM] at ht
      simp [idiv_, hy', ht]
    rw [hnone]
    show TryClauses (simEnv B) _ _ (optUNV none)
    rw [decide_eq_true hq₀] at hcmp
    exact tryClauses_hit matchArgs_divGen
      (Equiv.Validation.premsHold_cons_iff.2 ⟨_, Equiv.Validation.premHolds_if_iff.2 ⟨rfl, hcmp⟩,
        Equiv.Validation.premsHold_nil_iff.2 rfl⟩)
      (evalExp_optE_none_iff.2 rfl)
  · show TryClauses (simEnv B) _ _ (optUNV (idiv_ N .signed x y))
    rw [decide_eq_false hq₀] at hcmp
    have ht : (signed_ N x.toNat).tdiv (signed_ N y.toNat) ≠ 2 ^ (N - 1) := by
      rw [← hM]; exact fun h => hq₀ (hov.2 h)
    have hab : ((signed_ N x.toNat).tdiv (signed_ N y.toNat)).natAbs ≤ 2 ^ (N - 1) := by
      have h1 := Int.natAbs_tdiv (signed_ N x.toNat) (signed_ N y.toNat)
      have h2 : (signed_ N x.toNat).natAbs ≤ 2 ^ (N - 1) := by
        have : ((2 ^ (N - 1) : ℕ) : ℤ) = 2 ^ (N - 1) := hM
        omega
      rw [h1]; exact le_trans (Nat.div_le_self _ _) h2
    have hr₁ : -2 ^ (N - 1) ≤ (signed_ N x.toNat).tdiv (signed_ N y.toNat) := by
      have : ((2 ^ (N - 1) : ℕ) : ℤ) = 2 ^ (N - 1) := hM
      omega
    have hr₂ : (signed_ N x.toNat).tdiv (signed_ N y.toNat) < 2 ^ (N - 1) := by
      have : ((2 ^ (N - 1) : ℕ) : ℤ) = 2 ^ (N - 1) := hM
      omega
    have hsome : optUNV (idiv_ N .signed x y) = .opt (some (.case "%" (.tuple
        [natV (invSigned_ N ((signed_ N x.toNat).tdiv (signed_ N y.toNat)))]))) := by
      simp [optUNV, idiv_, hy', ht, bvV_ofNat (Equiv.invSigned_lt _ _)]
    rw [hsome]
    refine tryClauses_skip_prem matchArgs_divGen (premsUndef_ifPr hcmp) ?_
    have htr : CallDef (simEnv B) σ "truncz" [.expA (.binE .divOp (.numT .ratT)
        (.cvtE (.callE "signed_" [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          .intT .ratT)
        (.cvtE (.callE "signed_" [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          .intT .ratT))]
        (intV ((signed_ N x.toNat).tdiv (signed_ N y.toNat))) := by
      refine callDef_prim hB (noClauses_truncz B) rfl (Equiv.evalArgs_cons hq Equiv.evalArgs_nil) ?_
      simp [intCall, truncQ_intDiv _ _ hj2, intV]
    have hinv := Equiv.callDef_invSigned (numEnv_simEnv B) (ρ := σ) rfl
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 hNv)
        (Equiv.evalArgs_cons (evalExp_callE_iff.2 htr) Equiv.evalArgs_nil)) hN hr₁ hr₂
    exact tryClauses_hit matchArgs_divGen premsHold_nil (evalExp_optE_some_iff.2
      ⟨_, Equiv.evalExp_case_tup_one (evalExp_callE_iff.2 hinv), rfl⟩)

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
