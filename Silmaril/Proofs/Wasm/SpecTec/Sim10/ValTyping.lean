module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SubjRedStep
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeValTyping

/-!
# Every V1 value is a typed `val` of the 1.0 script

`ValTyped10 B` (`SubjRedPure`) holds at every builtins (`valTyped10`). 1.0's
`val = CONST valtype val_(valtype)`, with `val_(Inn) = iN($size(Inn))` and
`val_(Fnn) = fN($size(Fnn))`. Integers are `uN` below `2^N`; floats are 1.0's `fN`/`fNmag`, whose
definitions are 2.0's term for term (1.0's `d21`–`d27` for 2.0's `d29`–`d35`). The float lemmas
are 2.0's `Sim20.Pure` ones (`NumTyping`), ported with the 1.0 lookups (each a kernel `rfl`).

With it, subject reduction (`SubjRedStep.ts10_step`) and the forward half without the successor's
typing hold unconditionally (`typed10_step'`, `wholeStepFwd10_of_restR''`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV intV bvV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTecEnc (floatFraction floatExponent floatSign floatFractionWidth
  floatExponentWidth)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (instCases findCase hasTypCase_of_findCase premsOk_if
  evalExp_and defOf hasTypCase_nullary)
open Silmaril.Wasm.SpecTec.Sim.Typing (magV floatV_eq magScope floatFraction_lt floatExponent_lt
  floatExponentWidth_pos evalExp_minExp evalExp_maxExp hasTypCase_of_findCaseQ)
open Silmaril.Wasm.SpecTec.Sim (ValsOnly TypedV)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

namespace W10
export Silmaril.Wasm.SpecTec.Scripts.Wasm10.Original (d21 d22 d23 d24 d26 d27)
end W10

variable {B : Builtins}

/-! ## The 1.0 definitions -/

set_option maxRecDepth 100000 in
theorem findDef_signif10 : (simEnv10 B).findDef? "signif" = defOf W10.d21 := rfl
set_option maxRecDepth 100000 in
theorem findDef_expon10 : (simEnv10 B).findDef? "expon" = defOf W10.d22 := rfl
set_option maxRecDepth 100000 in
theorem findDef_M10 : (simEnv10 B).findDef? "M" = defOf W10.d23 := rfl
set_option maxRecDepth 100000 in
theorem findDef_E10 : (simEnv10 B).findDef? "E" = defOf W10.d24 := rfl

set_option maxRecDepth 100000 in
theorem findTyp_fN10 : ∃ ps qs, (simEnv10 B).findTyp? "fN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases W10.d27 0))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_fNmag10 : ∃ ps qs, (simEnv10 B).findTyp? "fNmag" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases W10.d26 0))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_exp10 : (simEnv10 B).findTyp? "exp" =
    some ([], [.instD [] [] (.aliasT (.numT .intT))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_m10 : (simEnv10 B).findTyp? "m" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

/-! ## Floats: `fNmag(N)`, `fN(N)`, `num_(Fnn)` (2.0's `Sim20.Pure` lemmas, ported to the 1.0 definitions) -/

/-- A natural-literal clause pattern. -/
theorem matchArgs_numLit10 {n : Nat} :
    MatchArgs (simEnv10 B) VarEnv.empty [.expA (.numE (.natN n))] [.val (natV n)] VarEnv.empty :=
  matchArgs_cons (matchArg_expA matchExp_numE) matchArgs_nil

/-- A natural-literal clause pattern definitely fails on another natural. -/
theorem matchArgs_numLit10_undef {n k : Nat} (h : n ≠ k) :
    MatchArgsUndef (simEnv10 B) VarEnv.empty [.expA (.numE (.natN n))] [.val (natV k)] :=
  matchArgs_cons_undef (matchArg_expA_undef (matchExp_numE_undef (by simp [natV, h.symm])))

set_option maxRecDepth 100000 in
/-- `$signif(N)`, at a float width. -/
theorem callDef_signif10 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "signif" = none) (ha : EvalArgs (simEnv10 B) ρ args [.val (natV t.width)]) :
    CallDef (simEnv10 B) ρ "signif" args (natV (floatFractionWidth t)) := by
  refine callDef_of_tryClauses hρ findDef_signif10 ha ?_
  cases t with
  | f32 => exact tryClauses_hit matchArgs_numLit10 premsHold_nil evalExp_num
  | f64 =>
      exact tryClauses_skip_match (matchArgs_numLit10_undef (by decide))
        (tryClauses_hit matchArgs_numLit10 premsHold_nil evalExp_num)

set_option maxRecDepth 100000 in
/-- `$expon(N)`, at a float width. -/
theorem callDef_expon10 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "expon" = none) (ha : EvalArgs (simEnv10 B) ρ args [.val (natV t.width)]) :
    CallDef (simEnv10 B) ρ "expon" args (natV (floatExponentWidth t)) := by
  refine callDef_of_tryClauses hρ findDef_expon10 ha ?_
  cases t with
  | f32 => exact tryClauses_hit matchArgs_numLit10 premsHold_nil evalExp_num
  | f64 =>
      exact tryClauses_skip_match (matchArgs_numLit10_undef (by decide))
        (tryClauses_hit matchArgs_numLit10 premsHold_nil evalExp_num)

set_option maxRecDepth 100000 in
/-- `$M(N)` in a scope binding `N` to a float width. -/
theorem evalExp_M10 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} (hd : ρ.findDef? "M" = none)
    (hN : ρ.findVal? "N" = some (natV t.width)) :
    EvalExp (simEnv10 B) ρ (.callE "M" [.expA (.varE "N")]) (natV (floatFractionWidth t)) :=
  evalExp_callE_iff.2 (callDef_of_tryClauses hd findDef_M10
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hN) Equiv.evalArgs_nil)
    (tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "N" (natV t.width))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
      (evalExp_callE_iff.2 (callDef_signif10 t rfl
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))))

set_option maxRecDepth 100000 in
/-- `$E(N)` in a scope binding `N` to a float width. -/
theorem evalExp_E10 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} (hd : ρ.findDef? "E" = none)
    (hN : ρ.findVal? "N" = some (natV t.width)) :
    EvalExp (simEnv10 B) ρ (.callE "E" [.expA (.varE "N")]) (natV (floatExponentWidth t)) :=
  evalExp_callE_iff.2 (callDef_of_tryClauses hd findDef_E10
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hN) Equiv.evalArgs_nil)
    (tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "N" (natV t.width))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
      (evalExp_callE_iff.2 (callDef_expon10 t rfl
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))))

/-- `m < 2 ^ $M(N)`. -/
theorem evalExp_ltSignif10 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {m : Nat}
    (hd : ρ.findDef? "M" = none) (hN : ρ.findVal? "N" = some (natV t.width))
    (hm : ρ.findVal? "m" = some (.num (.natN m))) (hlt : m < 2 ^ floatFractionWidth t) :
    EvalExp (simEnv10 B) ρ (.cmpE .ltOp (.numT .natT) (.varE "m")
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.callE "M" [.expA (.varE "N")])))
      (.bool true) :=
  evalExp_cmpNum (evalExp_var hm) (evalExp_binNum evalExp_num (evalExp_M10 t hd hN) rfl)
    (by simp [Num.cmp, hlt])

/-- `m` holds naturals. -/
theorem hasTyp_m10 {ρ : VarEnv} (hρ : ρ.findTyp? "m" = none) (n : Nat) :
    HasTyp (simEnv10 B) ρ (.varT "m" []) (.num (.natN n)) :=
  hasTyp_varT_of_insts (by simp [localTyp?, hρ]) findTyp_m10 Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- `exp` holds integers. -/
theorem hasTyp_exp10 {ρ : VarEnv} (hρ : ρ.findTyp? "exp" = none) (j : Int) :
    HasTyp (simEnv10 B) ρ (.varT "exp" []) (.num (.intN j)) :=
  hasTyp_varT_of_insts (by simp [localTyp?, hρ]) findTyp_exp10 Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- `n` holds naturals. -/
theorem hasTyp_n10 {ρ : VarEnv} (hρ : ρ.findTyp? "n" = none) (k : Nat) :
    HasTyp (simEnv10 B) ρ (.varT "n" []) (.num (.natN k)) :=
  hasTyp_varT_of_insts (by simp [localTyp?, hρ]) findTyp_n10 Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- The one-field payload `(m)` of `NAN`/`SUBNORM`. -/
theorem hasTyp_mTup10 (t : Silmaril.Wasm.FloatType) (m : Nat) :
    HasTyp (simEnv10 B) (magScope t) (.tupT [.mk "m" (.varT "m" [])]) (.tuple [.num (.natN m)]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_m10 rfl m,
    hasTypTup_nil_iff.2 rfl⟩⟩

set_option maxRecDepth 100000 in
/-- `INF` and `NAN m` (`1 ≤ m < 2^M`). -/
theorem hasTypCase_mag_inf_nan10 (t : Silmaril.Wasm.FloatType) (m : Nat)
    (hm : m < 2 ^ floatFractionWidth t) :
    HasTypCase (simEnv10 B) (magScope t) (instCases W10.d26 0) "INF" (.tuple []) ∧
      (0 < m → HasTypCase (simEnv10 B) (magScope t) (instCases W10.d26 0) "NAN"
        (.tuple [.num (.natN m)])) := by
  refine ⟨hasTypCase_nullary rfl, fun hpos => ?_⟩
  refine hasTypCase_of_findCase rfl (hasTyp_mTup10 t m) (premsOk_if (evalExp_and ?_ ?_))
  · exact evalExp_cmpNum (m₂ := .natN m) evalExp_num (evalExp_var (by simp [caseScope, typBinds]))
      (by simp [Num.cmp]; omega)
  · exact evalExp_ltSignif10 t rfl (by simp [caseScope, typBinds])
      (by simp [caseScope, typBinds]) hm

set_option maxRecDepth 100000 in
/-- `SUBNORM m` (`m < 2^M`; the quantifier `exp` is defined as `2 - 2^(E-1)`). -/
theorem hasTypCase_mag_subnorm10 (t : Silmaril.Wasm.FloatType) (m : Nat)
    (hm : m < 2 ^ floatFractionWidth t) :
    HasTypCase (simEnv10 B) (magScope t) (instCases W10.d26 0) "SUBNORM"
      (.tuple [.num (.natN m)]) := by
  have hk : 0 < floatExponentWidth t := floatExponentWidth_pos t
  have hE : EvalExp (simEnv10 B) (caseScope (magScope t) (.tupT [.mk "m" (.varT "m" [])])
      (.tuple [.num (.natN m)])) (.callE "E" [.expA (.varE "N")])
      (natV (floatExponentWidth t)) :=
    evalExp_E10 t rfl (by simp [caseScope, typBinds])
  refine hasTypCase_of_findCaseQ rfl (hasTyp_mTup10 t m)
    (bindQuants_cons (evalExp_minExp hk hE) (hasTyp_exp10 rfl _)
      (bindQuants_nil_iff.2 rfl))
    (premsOk_if (evalExp_and ?_ ?_))
  · exact evalExp_ltSignif10 t rfl (by simp [caseScope, typBinds])
      (by simp [caseScope, typBinds]) hm
  · refine evalExp_cmpE_iff.2 ⟨intV (2 - ((2 ^ (floatExponentWidth t - 1) : Nat) : Int)),
      intV (2 - ((2 ^ (floatExponentWidth t - 1) : Nat) : Int)),
      evalExp_minExp hk (evalExp_E10 t rfl (by simp [caseScope, typBinds])),
      evalExp_var (by simp [caseScope, typBinds]), ?_⟩
    simp [cmpValues]

set_option maxRecDepth 100000 in
/-- `NORM m exp` (`m < 2^M`, `2 - 2^(E-1) ≤ exp ≤ 2^(E-1) - 1`). -/
theorem hasTypCase_mag_norm10 (t : Silmaril.Wasm.FloatType) (m : Nat) (j : Int)
    (hm : m < 2 ^ floatFractionWidth t)
    (hlo : 2 - ((2 ^ (floatExponentWidth t - 1) : Nat) : Int) ≤ j)
    (hhi : j ≤ ((2 ^ (floatExponentWidth t - 1) : Nat) : Int) - 1) :
    HasTypCase (simEnv10 B) (magScope t) (instCases W10.d26 0) "NORM"
      (.tuple [.num (.natN m), .num (.intN j)]) := by
  have htup : HasTyp (simEnv10 B) (magScope t)
      (.tupT [.mk "m" (.varT "m" []), .mk "exp" (.varT "exp" [])])
      (.tuple [.num (.natN m), .num (.intN j)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_m10 rfl m,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_exp10 rfl j, hasTypTup_nil_iff.2 rfl⟩⟩⟩
  have hk : 0 < floatExponentWidth t := floatExponentWidth_pos t
  have hE : EvalExp (simEnv10 B) (caseScope (magScope t)
      (.tupT [.mk "m" (.varT "m" []), .mk "exp" (.varT "exp" [])])
      (.tuple [.num (.natN m), .num (.intN j)])) (.callE "E" [.expA (.varE "N")])
      (natV (floatExponentWidth t)) :=
    evalExp_E10 t rfl (by simp [caseScope, typBinds])
  refine hasTypCase_of_findCase rfl htup (premsOk_if (evalExp_and ?_ (evalExp_and ?_ ?_)))
  · exact evalExp_ltSignif10 t rfl (by simp [caseScope, typBinds])
      (by simp [caseScope, typBinds]) hm
  · exact evalExp_cmpNum (m₂ := .intN j) (evalExp_minExp hk hE)
      (evalExp_var (by simp [caseScope, typBinds]))
      (by simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]; omega)
  · exact evalExp_cmpNum (m₁ := .intN j) (evalExp_var (by simp [caseScope, typBinds]))
      (evalExp_maxExp hk hE)
      (by simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]; omega)

/-- Every magnitude `floatV` produces is a `fNmag` case of the width. -/
theorem hasTypCase_magV10 (t : Silmaril.Wasm.FloatType) (b : BitVec t.width) :
    ∃ op w, magV t b = .case op w ∧
      HasTypCase (simEnv10 B) (magScope t) (instCases W10.d26 0) op w := by
  have hm : floatFraction t b < 2 ^ floatFractionWidth t := floatFraction_lt t b
  have he : floatExponent t b < 2 ^ floatExponentWidth t := floatExponent_lt t b
  unfold magV
  simp only
  split_ifs with h0 hmax hm0
  · exact ⟨_, _, rfl, hasTypCase_mag_subnorm10 t _ hm⟩
  · exact ⟨_, _, rfl, (hasTypCase_mag_inf_nan10 t _ hm).1⟩
  · exact ⟨_, _, rfl, (hasTypCase_mag_inf_nan10 t _ hm).2 (Nat.pos_of_ne_zero hm0)⟩
  · refine ⟨_, _, rfl, hasTypCase_mag_norm10 t _ _ hm ?_ ?_⟩
    · cases t <;> simp only [floatExponentWidth] at * <;> omega
    · cases t <;> simp only [floatExponentWidth] at * <;> omega

/-- `fNmag(N)` holds every magnitude of the width. -/
theorem hasTyp_fNmag10 {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.FloatType) (b : BitVec t.width)
    (he : EvalExp (simEnv10 B) ρ e (natV t.width)) :
    HasTyp (simEnv10 B) ρ (.varT "fNmag" [.expA e]) (magV t b) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_fNmag10 (B := B)
  obtain ⟨op, w, hv, hc⟩ := hasTypCase_magV10 (B := B) t b
  rw [hv]
  exact hasTyp_varT_case (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) hc

set_option maxRecDepth 100000 in
/-- **`fN(N)` holds every float of the width**: both signs, every magnitude. -/
theorem hasTyp_fN10 {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.FloatType) (b : BitVec t.width)
    (he : EvalExp (simEnv10 B) ρ e (natV t.width)) :
    HasTyp (simEnv10 B) ρ (.varT "fN" [.expA e]) (Sim.floatV t b) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_fN10 (B := B)
  have hmag : HasTyp (simEnv10 B) (magScope t) (.varT "fNmag" [.expA (.varE "N")]) (magV t b) :=
    hasTyp_fNmag10 t b (evalExp_var (by simp))
  rw [floatV_eq]
  refine hasTyp_varT_case (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) ?_
  split_ifs
  · exact hasTypCase_of_findCase rfl hmag premsOk_nil
  · exact hasTypCase_of_findCase rfl hmag premsOk_nil

/-! ## `val_(valtype)` and `val` -/

set_option maxRecDepth 100000 in
theorem findTyp_valF10 : ∃ ps qs qs', (simEnv10 B).findTyp? "val_" = some (ps,
    [.instD qs [.expA innPat10] (.aliasT (.varT "iN" [.expA (.callE "size" [.expA innPat10])])),
     .instD qs' [.expA fnnPat10] (.aliasT (.varT "fN" [.expA (.callE "size" [.expA fnnPat10])]))]) :=
  ⟨_, _, _, rfl⟩

/-- `iN($size(Inn))` holds every bit pattern of the width. -/
theorem hasTyp_iN10 (t : Silmaril.Wasm.IntType) (b : BitVec t.width) :
    HasTyp (simEnv10 B) (VarEnv.empty.bindVal "Inn" (valTypeV (.int t)))
      (.varT "iN" [.expA (.callE "size" [.expA innPat10])]) (bvV b) := by
  obtain ⟨ps', qs', htd'⟩ := findTyp_iN10 (B := B)
  have hsz : EvalExp (simEnv10 B) (VarEnv.empty.bindVal "Inn" (valTypeV (.int t)))
      (.callE "size" [.expA innPat10]) (natV t.width) :=
    evalExp_size10 (.int t) rfl (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp)))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd'
    (Equiv.evalArgs_cons hsz Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 (hasTyp_uN10 (evalExp_varE_iff.2 (by simp)) b.isLt)))

/-- **`val_(Inn)` holds every integer of the width.** -/
theorem hasTyp_valInt10 {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.IntType) (b : BitVec t.width)
    (he : EvalExp (simEnv10 B) ρ e (valTypeV (.int t))) :
    HasTyp (simEnv10 B) ρ (.varT "val_" [.expA e]) (bvV b) := by
  obtain ⟨ps, qs, qs', htd⟩ := findTyp_valF10 (B := B)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (Sim20.Pure.matchArg_subVar20 (by simp)
      (argSubOk_inn_int10 t)) matchArgs_nil) (hasTypDef_aliasT_iff.2 (hasTyp_iN10 t b)))

/-- **`val_(Fnn)` holds every float of the width.** -/
theorem hasTyp_valFloat10 {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.FloatType)
    (b : BitVec t.width) (he : EvalExp (simEnv10 B) ρ e (valTypeV (.float t))) :
    HasTyp (simEnv10 B) ρ (.varT "val_" [.expA e]) (Sim.floatV t b) := by
  obtain ⟨ps, qs, qs', htd⟩ := findTyp_valF10 (B := B)
  have hfN : HasTyp (simEnv10 B) (VarEnv.empty.bindVal "Fnn" (valTypeV (.float t)))
      (.varT "fN" [.expA (.callE "size" [.expA fnnPat10])]) (Sim.floatV t b) :=
    hasTyp_fN10 t b (evalExp_size10 (.float t) rfl
      (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp))))
  obtain ⟨n, hn⟩ : MatchArgsUndef (simEnv10 B) VarEnv.empty [.expA innPat10]
      [.val (valTypeV (.float t))] :=
    matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (argSubOk_inn_float10 t))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_tail hn (hasTypInsts_head (matchArgs_cons
      (Sim20.Pure.matchArg_subVar20 (by simp) (argSubOk_fnn_float10 t)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 hfN)))

/-- `val_(t)` holds the image of every V1 number of type `t`. -/
theorem hasTyp_valNum10 {ρ : VarEnv} {e : Exp} (v : Silmaril.Wasm.Execution.Runtime.Value)
    (he : EvalExp (simEnv10 B) ρ e (valTypeV v.type)) :
    HasTyp (simEnv10 B) ρ (.varT "val_" [.expA e]) (numV v) := by
  obtain ⟨t | t, b⟩ := v
  · exact hasTyp_valInt10 t b he
  · exact hasTyp_valFloat10 t b he

/-- **Every V1 value is a typed `val` of the 1.0 script**, at every builtins. -/
theorem valTyped10 : ValTyped10 B := fun v => by
  obtain ⟨cs, htd, hc⟩ := findTyp_val10F (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hc (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2
    ⟨_, _, rfl, typedV_valtype10 _ _ ⟨rfl, rfl, rfl⟩, hasTypTup_cons_iff.2 ⟨_, _, rfl,
      hasTyp_valNum10 v (evalExp_varE_iff.2 (by simp)), hasTypTup_nil_iff.2 rfl⟩⟩⟩)

/-! ## Subject reduction and the forward half, unconditionally -/

open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Config HostSemantics Step)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)

/-- **Subject reduction for every V1 step**, at every builtins: from a configuration whose image
is typed and which satisfies `GSetOk`, every V1 step leads to a configuration whose image is
typed. -/
theorem typed10_step' {H : Type} {hn : H → String} {host : HostSemantics H} {c c' : Config H}
    (h : Step host c c') (hc : Typed10 (simEnv10 B) hn c) (hg : GSetOk c.store c.frame c.code) :
    Typed10 (simEnv10 B) hn c' :=
  typed10_step valTyped10 h hc hg

/-- **The forward 1.0 half, without the successor's typing**: under `NumAgree10` at the spec
profile and `FwdRestR10`, every V1 step from a configuration whose image is typed and which
satisfies `Plain10`, `GSetOk` and `MemsAligned10` is a step of the 1.0 script between the
images. -/
theorem wholeStepFwd10_of_restR'' {H : Type} {hn : H → String} {host : HostSemantics H}
    {nd : Bool} {r : RelaxedChoice} (A : NumAgree10 (simEnv10 B) (Profile.spec nd r))
    (R : FwdRestR10 B hn) {c c' : Config H} (hc : Typed10 (simEnv10 B) hn c)
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store)
    (h : Step host c c') : SStepB (simEnv10 B) (configV hn c) (configV hn c') :=
  wholeStepFwd10_of_restR' valTyped10 A R hc hpl hg hal h

/-- **Pass 2's assembly without the successor's typing**: `wholeStepFwd10_of_restQ` at
`floatIntB`, its typed-successor hypothesis discharged by subject reduction. -/
theorem wholeStepFwd10_of_restQ' {H : Type} {hn : H → String} {host : HostSemantics H}
    {nd : Bool} {r : RelaxedChoice}
    (Q : FwdRestQ10 (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) {c c' : Config H}
    (hc : Typed10 (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r))) hn c)
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (h : Step host c c') :
    SStepB (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r))) (configV hn c) (configV hn c') :=
  wholeStepFwd10_of_restQ Q hc (typed10_step' h hc hg) hpl hg h

end Silmaril.Wasm.SpecTec.Sim10.Whole
