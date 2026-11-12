module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumAgree
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Typing

/-!
# `NumTyped` for the wasm-2.0 script, discharged

The encodings of V2's numbers and scalar operators have their wasm-2.0 IL types:
`numTyped_simEnv20 : NumTyped (simEnv20 B)`, with no hypothesis on `B`.

Every type definition the typing reads is byte-identical between wasm-2.0 and wasm-3.0 except
`unop_` (checked textually against the generated scripts: `uN` 2.0 `d17` = 3.0 `d22`, `iN`
`d19`/`d24`, `fN` `d35`/`d40`, `fNmag` `d34`/`d39`, `exp` `d33`/`d38`, `m` `d3`, `num_`
`d97`/`d210`, `Inn`/`Fnn` `d61`,`d62`/`d99`,`d100`, `binop_`, `testop_`, `relop_`
`d105`–`d107`/`d218`–`d220`, `$signif`, `$expon`, `$M`, `$E` `d29`–`d32`/`d34`–`d37`), and the
size functions, which 2.0 defines over `valtype` (`Sim20.NumLookup`). The lemmas below are the
3.0 typing proofs of `Sim.IntNumeric.Typing` and `Sim.Typing.Float`, **ported** to `simEnv20 B`
with the 2.0 definition numbers (each lookup a kernel `rfl` against the 2.0 script) and the 2.0
size functions. 2.0's `unop_(Inn)` has `EXTEND n` with a bare `n` and no premise
(`Original.d104`), so its typing needs no validity side condition.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV intV bvV)
open Silmaril.Wasm.SpecTec (floatFraction floatExponent floatSign floatFractionWidth
  floatExponentWidth)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d2 Original.d3 Original.d17 Original.d19
  Original.d29 Original.d30 Original.d31 Original.d32 Original.d33 Original.d34 Original.d35
  Original.d97 Original.d102 Original.d104 Original.d105 Original.d106 Original.d107)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (instCases findCase hasTypCase_of_findCase premsOk_if
  evalExp_and defOf hasTypCase_nullary)
open Silmaril.Wasm.SpecTec.Sim.Typing (magV floatV_eq magScope floatFraction_lt floatExponent_lt
  floatExponentWidth_pos evalExp_minExp evalExp_maxExp hasTypCase_of_findCaseQ)
open Silmaril.Wasm.SpecTec.Sim (ValsOnly TypedV)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## The script's definitions (2.0 numbering) -/

set_option maxRecDepth 100000 in
theorem findDef_signif20 : (simEnv20 B).findDef? "signif" = defOf Original.d29 := rfl
set_option maxRecDepth 100000 in
theorem findDef_expon20 : (simEnv20 B).findDef? "expon" = defOf Original.d30 := rfl
set_option maxRecDepth 100000 in
theorem findDef_M20 : (simEnv20 B).findDef? "M" = defOf Original.d31 := rfl
set_option maxRecDepth 100000 in
theorem findDef_E20 : (simEnv20 B).findDef? "E" = defOf Original.d32 := rfl

set_option maxRecDepth 100000 in
theorem findTyp_uN20 : ∃ ps qs, (simEnv20 B).findTyp? "uN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases Original.d17 0))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_iN20 : ∃ ps qs, (simEnv20 B).findTyp? "iN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.aliasT (.varT "uN" [.expA (.varE "N")]))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_num20 : ∃ ps qs qs', (simEnv20 B).findTyp? "num_" = some (ps,
    [.instD qs [.expA innPat20] (.aliasT (.varT "iN" [.expA (.callE "sizenn" [.expA innPat20])])),
     .instD qs' [.expA fnnPat] (.aliasT (.varT "fN" [.expA (.callE "sizenn" [.expA fnnPat])]))]) :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_fN20 : ∃ ps qs, (simEnv20 B).findTyp? "fN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases Original.d35 0))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_fNmag20 : ∃ ps qs, (simEnv20 B).findTyp? "fNmag" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases Original.d34 0))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_exp20 : (simEnv20 B).findTyp? "exp" =
    some ([], [.instD [] [] (.aliasT (.numT .intT))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_m20 : (simEnv20 B).findTyp? "m" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_n20 : (simEnv20 B).findTyp? "n" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

/-! ## Integers: `uN(N)`, `iN(N)`, `num_(Inn)` -/

/-- `uN(N)` holds every natural below `2^N` (ported from `IntNumeric.hasTyp_uN`). -/
theorem hasTyp_uN20 {ρ : VarEnv} {e : Exp} {N n : Nat} (he : EvalExp (simEnv20 B) ρ e (natV N))
    (hn : n < 2 ^ N) :
    HasTyp (simEnv20 B) ρ (.varT "uN" [.expA e]) (.case "%" (.tuple [natV n])) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_uN20 (B := B)
  have htup : HasTyp (simEnv20 B) (VarEnv.empty.bindVal "N" (natV N))
      (.tupT [.mk "i" (.numT .natT)]) (.tuple [natV n]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩
  have hpow : EvalExp (simEnv20 B) ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (natV n))
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) (natV (2 ^ N)) :=
    Equiv.evalExp_twoPow (by simp)
  have hsub : EvalExp (simEnv20 B) ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (natV n))
      (.binE .subOp (.numT .intT) (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2))
        (.varE "N")) .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
      (.num (.intN ((2 ^ N : Nat) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt hpow) Equiv.evalExp_oneInt rfl
  have hk := Equiv.evalExp_toNat (j := ((2 ^ N : Nat) : Int) - 1)
    (by have := Nat.one_le_two_pow (n := N); omega) hsub
  refine hasTyp_varT_case (localTyp?_cons _ _ _) htd
    (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    (hasTypCase_of_findCase rfl htup (premsOk_if (evalExp_and ?_ ?_)))
  · exact evalExp_cmpNum (evalExp_var (v := natV n) rfl) evalExp_num (by simp [Num.cmp])
  · refine evalExp_cmpNum (evalExp_var (v := natV n) rfl) hk ?_
    simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
    omega

/-- `iN($sizenn(Inn))` holds every bit pattern of the width. -/
theorem hasTyp_iN20 (t : Silmaril.Wasm.IntType) (b : BitVec t.width) :
    HasTyp (simEnv20 B) (VarEnv.empty.bindVal "Inn" (numTypeV (.int t)))
      (.varT "iN" [.expA (.callE "sizenn" [.expA innPat20])]) (bvV b) := by
  obtain ⟨ps', qs', htd'⟩ := findTyp_iN20 (B := B)
  have hsz : EvalExp (simEnv20 B) (VarEnv.empty.bindVal "Inn" (numTypeV (.int t)))
      (.callE "sizenn" [.expA innPat20]) (natV t.width) := evalExp_sizenn20 (.int t) rfl (by simp)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd'
    (Equiv.evalArgs_cons hsz Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 (hasTyp_uN20 (evalExp_var (by simp)) b.isLt)))

/-- **`num_(Inn)` holds every bit pattern of the width.** -/
theorem hasTyp_num_int20 {ρ : VarEnv} {e : Exp} {t : Silmaril.Wasm.IntType} (b : BitVec t.width)
    (he : EvalExp (simEnv20 B) ρ e (numTypeV (.int t))) :
    HasTyp (simEnv20 B) ρ (.varT "num_" [.expA e]) (bvV b) := by
  obtain ⟨ps, qs, qs', htd⟩ := findTyp_num20 (B := B)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd
    (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_subVar20 (by simp) (argSubOk_inn_int20 _))
      matchArgs_nil) (hasTypDef_aliasT_iff.2 (hasTyp_iN20 t b)))

/-! ## Floats: `fNmag(N)`, `fN(N)`, `num_(Fnn)` (ported from `Sim.Typing.Float`) -/

/-- A natural-literal clause pattern. -/
theorem matchArgs_numLit20 {n : Nat} :
    MatchArgs (simEnv20 B) VarEnv.empty [.expA (.numE (.natN n))] [.val (natV n)] VarEnv.empty :=
  matchArgs_cons (matchArg_expA matchExp_numE) matchArgs_nil

/-- A natural-literal clause pattern definitely fails on another natural. -/
theorem matchArgs_numLit20_undef {n k : Nat} (h : n ≠ k) :
    MatchArgsUndef (simEnv20 B) VarEnv.empty [.expA (.numE (.natN n))] [.val (natV k)] :=
  matchArgs_cons_undef (matchArg_expA_undef (matchExp_numE_undef (by simp [natV, h.symm])))

set_option maxRecDepth 100000 in
/-- `$signif(N)`, at a float width. -/
theorem callDef_signif20 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "signif" = none) (ha : EvalArgs (simEnv20 B) ρ args [.val (natV t.width)]) :
    CallDef (simEnv20 B) ρ "signif" args (natV (floatFractionWidth t)) := by
  refine callDef_of_tryClauses hρ findDef_signif20 ha ?_
  cases t with
  | f32 => exact tryClauses_hit matchArgs_numLit20 premsHold_nil evalExp_num
  | f64 =>
      exact tryClauses_skip_match (matchArgs_numLit20_undef (by decide))
        (tryClauses_hit matchArgs_numLit20 premsHold_nil evalExp_num)

set_option maxRecDepth 100000 in
/-- `$expon(N)`, at a float width. -/
theorem callDef_expon20 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "expon" = none) (ha : EvalArgs (simEnv20 B) ρ args [.val (natV t.width)]) :
    CallDef (simEnv20 B) ρ "expon" args (natV (floatExponentWidth t)) := by
  refine callDef_of_tryClauses hρ findDef_expon20 ha ?_
  cases t with
  | f32 => exact tryClauses_hit matchArgs_numLit20 premsHold_nil evalExp_num
  | f64 =>
      exact tryClauses_skip_match (matchArgs_numLit20_undef (by decide))
        (tryClauses_hit matchArgs_numLit20 premsHold_nil evalExp_num)

set_option maxRecDepth 100000 in
/-- `$M(N)` in a scope binding `N` to a float width. -/
theorem evalExp_M20 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} (hd : ρ.findDef? "M" = none)
    (hN : ρ.findVal? "N" = some (natV t.width)) :
    EvalExp (simEnv20 B) ρ (.callE "M" [.expA (.varE "N")]) (natV (floatFractionWidth t)) :=
  evalExp_callE_iff.2 (callDef_of_tryClauses hd findDef_M20
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hN) Equiv.evalArgs_nil)
    (tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "N" (natV t.width))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
      (evalExp_callE_iff.2 (callDef_signif20 t rfl
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))))

set_option maxRecDepth 100000 in
/-- `$E(N)` in a scope binding `N` to a float width. -/
theorem evalExp_E20 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} (hd : ρ.findDef? "E" = none)
    (hN : ρ.findVal? "N" = some (natV t.width)) :
    EvalExp (simEnv20 B) ρ (.callE "E" [.expA (.varE "N")]) (natV (floatExponentWidth t)) :=
  evalExp_callE_iff.2 (callDef_of_tryClauses hd findDef_E20
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hN) Equiv.evalArgs_nil)
    (tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "N" (natV t.width))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
      (evalExp_callE_iff.2 (callDef_expon20 t rfl
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))))

/-- `m < 2 ^ $M(N)`. -/
theorem evalExp_ltSignif20 (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {m : Nat}
    (hd : ρ.findDef? "M" = none) (hN : ρ.findVal? "N" = some (natV t.width))
    (hm : ρ.findVal? "m" = some (.num (.natN m))) (hlt : m < 2 ^ floatFractionWidth t) :
    EvalExp (simEnv20 B) ρ (.cmpE .ltOp (.numT .natT) (.varE "m")
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.callE "M" [.expA (.varE "N")])))
      (.bool true) :=
  evalExp_cmpNum (evalExp_var hm) (evalExp_binNum evalExp_num (evalExp_M20 t hd hN) rfl)
    (by simp [Num.cmp, hlt])

/-- `m` holds naturals. -/
theorem hasTyp_m20 {ρ : VarEnv} (hρ : ρ.findTyp? "m" = none) (n : Nat) :
    HasTyp (simEnv20 B) ρ (.varT "m" []) (.num (.natN n)) :=
  hasTyp_varT_of_insts (by simp [localTyp?, hρ]) findTyp_m20 Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- `exp` holds integers. -/
theorem hasTyp_exp20 {ρ : VarEnv} (hρ : ρ.findTyp? "exp" = none) (j : Int) :
    HasTyp (simEnv20 B) ρ (.varT "exp" []) (.num (.intN j)) :=
  hasTyp_varT_of_insts (by simp [localTyp?, hρ]) findTyp_exp20 Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- `n` holds naturals. -/
theorem hasTyp_n20 {ρ : VarEnv} (hρ : ρ.findTyp? "n" = none) (k : Nat) :
    HasTyp (simEnv20 B) ρ (.varT "n" []) (.num (.natN k)) :=
  hasTyp_varT_of_insts (by simp [localTyp?, hρ]) findTyp_n20 Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- The one-field payload `(m)` of `NAN`/`SUBNORM`. -/
theorem hasTyp_mTup20 (t : Silmaril.Wasm.FloatType) (m : Nat) :
    HasTyp (simEnv20 B) (magScope t) (.tupT [.mk "m" (.varT "m" [])]) (.tuple [.num (.natN m)]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_m20 rfl m,
    hasTypTup_nil_iff.2 rfl⟩⟩

set_option maxRecDepth 100000 in
/-- `INF` and `NAN m` (`1 ≤ m < 2^M`). -/
theorem hasTypCase_mag_inf_nan20 (t : Silmaril.Wasm.FloatType) (m : Nat)
    (hm : m < 2 ^ floatFractionWidth t) :
    HasTypCase (simEnv20 B) (magScope t) (instCases Original.d34 0) "INF" (.tuple []) ∧
      (0 < m → HasTypCase (simEnv20 B) (magScope t) (instCases Original.d34 0) "NAN"
        (.tuple [.num (.natN m)])) := by
  refine ⟨hasTypCase_nullary rfl, fun hpos => ?_⟩
  refine hasTypCase_of_findCase rfl (hasTyp_mTup20 t m) (premsOk_if (evalExp_and ?_ ?_))
  · exact evalExp_cmpNum (m₂ := .natN m) evalExp_num (evalExp_var (by simp [caseScope, typBinds]))
      (by simp [Num.cmp]; omega)
  · exact evalExp_ltSignif20 t rfl (by simp [caseScope, typBinds])
      (by simp [caseScope, typBinds]) hm

set_option maxRecDepth 100000 in
/-- `SUBNORM m` (`m < 2^M`; the quantifier `exp` is defined as `2 - 2^(E-1)`). -/
theorem hasTypCase_mag_subnorm20 (t : Silmaril.Wasm.FloatType) (m : Nat)
    (hm : m < 2 ^ floatFractionWidth t) :
    HasTypCase (simEnv20 B) (magScope t) (instCases Original.d34 0) "SUBNORM"
      (.tuple [.num (.natN m)]) := by
  have hk : 0 < floatExponentWidth t := floatExponentWidth_pos t
  have hE : EvalExp (simEnv20 B) (caseScope (magScope t) (.tupT [.mk "m" (.varT "m" [])])
      (.tuple [.num (.natN m)])) (.callE "E" [.expA (.varE "N")])
      (natV (floatExponentWidth t)) :=
    evalExp_E20 t rfl (by simp [caseScope, typBinds])
  refine hasTypCase_of_findCaseQ rfl (hasTyp_mTup20 t m)
    (bindQuants_cons (evalExp_minExp hk hE) (hasTyp_exp20 rfl _)
      (bindQuants_nil_iff.2 rfl))
    (premsOk_if (evalExp_and ?_ ?_))
  · exact evalExp_ltSignif20 t rfl (by simp [caseScope, typBinds])
      (by simp [caseScope, typBinds]) hm
  · refine evalExp_cmpE_iff.2 ⟨intV (2 - ((2 ^ (floatExponentWidth t - 1) : Nat) : Int)),
      intV (2 - ((2 ^ (floatExponentWidth t - 1) : Nat) : Int)),
      evalExp_minExp hk (evalExp_E20 t rfl (by simp [caseScope, typBinds])),
      evalExp_var (by simp [caseScope, typBinds]), ?_⟩
    simp [cmpValues]

set_option maxRecDepth 100000 in
/-- `NORM m exp` (`m < 2^M`, `2 - 2^(E-1) ≤ exp ≤ 2^(E-1) - 1`). -/
theorem hasTypCase_mag_norm20 (t : Silmaril.Wasm.FloatType) (m : Nat) (j : Int)
    (hm : m < 2 ^ floatFractionWidth t)
    (hlo : 2 - ((2 ^ (floatExponentWidth t - 1) : Nat) : Int) ≤ j)
    (hhi : j ≤ ((2 ^ (floatExponentWidth t - 1) : Nat) : Int) - 1) :
    HasTypCase (simEnv20 B) (magScope t) (instCases Original.d34 0) "NORM"
      (.tuple [.num (.natN m), .num (.intN j)]) := by
  have htup : HasTyp (simEnv20 B) (magScope t)
      (.tupT [.mk "m" (.varT "m" []), .mk "exp" (.varT "exp" [])])
      (.tuple [.num (.natN m), .num (.intN j)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_m20 rfl m,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_exp20 rfl j, hasTypTup_nil_iff.2 rfl⟩⟩⟩
  have hk : 0 < floatExponentWidth t := floatExponentWidth_pos t
  have hE : EvalExp (simEnv20 B) (caseScope (magScope t)
      (.tupT [.mk "m" (.varT "m" []), .mk "exp" (.varT "exp" [])])
      (.tuple [.num (.natN m), .num (.intN j)])) (.callE "E" [.expA (.varE "N")])
      (natV (floatExponentWidth t)) :=
    evalExp_E20 t rfl (by simp [caseScope, typBinds])
  refine hasTypCase_of_findCase rfl htup (premsOk_if (evalExp_and ?_ (evalExp_and ?_ ?_)))
  · exact evalExp_ltSignif20 t rfl (by simp [caseScope, typBinds])
      (by simp [caseScope, typBinds]) hm
  · exact evalExp_cmpNum (m₂ := .intN j) (evalExp_minExp hk hE)
      (evalExp_var (by simp [caseScope, typBinds]))
      (by simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]; omega)
  · exact evalExp_cmpNum (m₁ := .intN j) (evalExp_var (by simp [caseScope, typBinds]))
      (evalExp_maxExp hk hE)
      (by simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]; omega)

/-- Every magnitude `floatV` produces is a `fNmag` case of the width. -/
theorem hasTypCase_magV20 (t : Silmaril.Wasm.FloatType) (b : BitVec t.width) :
    ∃ op w, magV t b = .case op w ∧
      HasTypCase (simEnv20 B) (magScope t) (instCases Original.d34 0) op w := by
  have hm : floatFraction t b < 2 ^ floatFractionWidth t := floatFraction_lt t b
  have he : floatExponent t b < 2 ^ floatExponentWidth t := floatExponent_lt t b
  unfold magV
  simp only
  split_ifs with h0 hmax hm0
  · exact ⟨_, _, rfl, hasTypCase_mag_subnorm20 t _ hm⟩
  · exact ⟨_, _, rfl, (hasTypCase_mag_inf_nan20 t _ hm).1⟩
  · exact ⟨_, _, rfl, (hasTypCase_mag_inf_nan20 t _ hm).2 (Nat.pos_of_ne_zero hm0)⟩
  · refine ⟨_, _, rfl, hasTypCase_mag_norm20 t _ _ hm ?_ ?_⟩
    · cases t <;> simp only [floatExponentWidth] at * <;> omega
    · cases t <;> simp only [floatExponentWidth] at * <;> omega

/-- `fNmag(N)` holds every magnitude of the width. -/
theorem hasTyp_fNmag20 {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.FloatType) (b : BitVec t.width)
    (he : EvalExp (simEnv20 B) ρ e (natV t.width)) :
    HasTyp (simEnv20 B) ρ (.varT "fNmag" [.expA e]) (magV t b) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_fNmag20 (B := B)
  obtain ⟨op, w, hv, hc⟩ := hasTypCase_magV20 (B := B) t b
  rw [hv]
  exact hasTyp_varT_case (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) hc

set_option maxRecDepth 100000 in
/-- **`fN(N)` holds every float of the width**: both signs, every magnitude. -/
theorem hasTyp_fN20 {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.FloatType) (b : BitVec t.width)
    (he : EvalExp (simEnv20 B) ρ e (natV t.width)) :
    HasTyp (simEnv20 B) ρ (.varT "fN" [.expA e]) (Sim.floatV t b) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_fN20 (B := B)
  have hmag : HasTyp (simEnv20 B) (magScope t) (.varT "fNmag" [.expA (.varE "N")]) (magV t b) :=
    hasTyp_fNmag20 t b (evalExp_var (by simp))
  rw [floatV_eq]
  refine hasTyp_varT_case (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) ?_
  split_ifs
  · exact hasTypCase_of_findCase rfl hmag premsOk_nil
  · exact hasTypCase_of_findCase rfl hmag premsOk_nil

/-- **`num_(Fnn)` holds every float of the width.** -/
theorem hasTyp_num_float20 {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.FloatType)
    (b : BitVec t.width) (he : EvalExp (simEnv20 B) ρ e (numTypeV (.float t))) :
    HasTyp (simEnv20 B) ρ (.varT "num_" [.expA e]) (Sim.floatV t b) := by
  obtain ⟨ps, qs, qs', htd⟩ := findTyp_num20 (B := B)
  have hfN : HasTyp (simEnv20 B) (VarEnv.empty.bindVal "Fnn" (numTypeV (.float t)))
      (.varT "fN" [.expA (.callE "sizenn" [.expA fnnPat])]) (Sim.floatV t b) :=
    hasTyp_fN20 t b (evalExp_sizenn20 (.float t) rfl (by simp))
  obtain ⟨n, hn⟩ : MatchArgsUndef (simEnv20 B) VarEnv.empty [.expA innPat20]
      [.val (numTypeV (.float t))] :=
    matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (argSubOk_inn_float20 t))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_tail hn (hasTypInsts_head (matchArgs_cons
      (matchArg_subVar20 (by simp) (argSubOk_fnn_float20 t)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 hfN)))

/-! ## The operator families -/

/-- An operator family with an `Inn` instance and an `Fnn` instance. -/
def TwoKinds20 (x : IL.Id) (d : Def) : Prop :=
  ∃ ps qs qs', (simEnv20 B).findTyp? x = some (ps,
    [.instD qs [.expA innPat20] (.variantT (instCases d 0)),
     .instD qs' [.expA fnnPat] (.variantT (instCases d 1))])

/-- An operator family with an `Inn` instance only. -/
def OneKind20 (x : IL.Id) (d : Def) : Prop :=
  ∃ ps qs, (simEnv20 B).findTyp? x = some (ps,
    [.instD qs [.expA innPat20] (.variantT (instCases d 0))])

set_option maxRecDepth 100000 in
theorem twoKinds_unop20 : TwoKinds20 (B := B) "unop_" Original.d104 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem twoKinds_binop20 : TwoKinds20 (B := B) "binop_" Original.d105 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem oneKind_testop20 : OneKind20 (B := B) "testop_" Original.d106 := ⟨_, _, rfl⟩
set_option maxRecDepth 100000 in
theorem twoKinds_relop20 : TwoKinds20 (B := B) "relop_" Original.d107 := ⟨_, _, _, rfl⟩

/-- The `Inn` instance of a family holds its cases, at an integer type. -/
theorem hasTyp_innVariant20 {x : IL.Id} {ρ : VarEnv} {e : Exp} {t : Silmaril.Wasm.IntType}
    {ps qs : List Param} {cs : List TypCase} {rest : List Inst} {op : MixopS} {w : Value}
    (htd : (simEnv20 B).findTyp? x = some (ps, .instD qs [.expA innPat20] (.variantT cs) :: rest))
    (he : EvalExp (simEnv20 B) ρ e (numTypeV (.int t)))
    (hc : HasTypCase (simEnv20 B) (VarEnv.empty.bindVal "Inn" (numTypeV (.int t))) cs op w) :
    HasTyp (simEnv20 B) ρ (.varT x [.expA e]) (.case op w) :=
  hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_subVar20 (by simp) (argSubOk_inn_int20 _))
      matchArgs_nil) (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩))

/-- The `Fnn` instance of a two-kind family holds its cases, at a float type. -/
theorem hasTyp_fnnVariant20 {x : IL.Id} {d : Def} (htd : TwoKinds20 (B := B) x d) {ρ : VarEnv}
    {e : Exp} {t : Silmaril.Wasm.FloatType} (he : EvalExp (simEnv20 B) ρ e (numTypeV (.float t)))
    {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv20 B) (VarEnv.empty.bindVal "Fnn" (numTypeV (.float t)))
      (instCases d 1) op w) :
    HasTyp (simEnv20 B) ρ (.varT x [.expA e]) (.case op w) := by
  obtain ⟨ps, qs, qs', htd⟩ := htd
  obtain ⟨n, hn⟩ : MatchArgsUndef (simEnv20 B) VarEnv.empty [.expA innPat20]
      [.val (numTypeV (.float t))] :=
    matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (argSubOk_inn_float20 t))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_tail hn (hasTypInsts_head (matchArgs_cons
      (matchArg_subVar20 (by simp) (argSubOk_fnn_float20 t)) matchArgs_nil)
      (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩)))

set_option maxRecDepth 100000 in
theorem findTyp_sx20' : (simEnv20 B).findTyp? "sx" =
    some ([], [.instD [] [] (.variantT (instCases Original.d102 0))]) := rfl

/-- A case carrying an `sx`, with no premise. -/
theorem hasTypCase_sx20 {σ : VarEnv} (hσ : ValsOnly σ) {cs : List TypCase} {op : MixopS}
    (hf : findCase cs op = some (.varT "sx" [], [])) (s : Silmaril.Wasm.Signedness) :
    HasTypCase (simEnv20 B) σ cs op (sxV s) :=
  hasTypCase_of_findCase hf (typedV_sx20 B s σ hσ) premsOk_nil
    (Sim.IntNumeric.quantFreeAt_of_findCase_nil hf)

/-- The scope the `Inn` instance binds is value-only. -/
theorem valsOnly_inn20 (t : Silmaril.Wasm.IntType) :
    ValsOnly (VarEnv.empty.bindVal "Inn" (numTypeV (.int t))) := ⟨rfl, rfl, rfl⟩

/-! ## The interface, discharged -/

/-- `unop_(Inn)` holds every integer unary operator (2.0's `EXTEND n` has no premise). -/
theorem typedAt_intUnOp20 (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntUnOp) :
    TypedAt (simEnv20 B) "unop_" "nt" (numTypeV (.int t)) (intUnOpV op) := by
  intro ρ _ hx
  obtain ⟨ps, qs, qs', htd⟩ := twoKinds_unop20 (B := B)
  cases op with
  | extend p =>
      exact hasTyp_innVariant20 htd (evalExp_var hx)
        (hasTypCase_of_findCase (cs := instCases Original.d104 0) (op := "EXTEND") rfl
          (hasTyp_n20 rfl _) premsOk_nil (Sim.IntNumeric.quantFreeAt_of_findCase_nil rfl))
  | _ => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_nullary rfl)

/-- `binop_(Inn)` holds every integer binary operator. -/
theorem typedAt_intBinOp20 (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntBinOp) :
    TypedAt (simEnv20 B) "binop_" "nt" (numTypeV (.int t)) (intBinOpV op) := by
  intro ρ _ hx
  obtain ⟨ps, qs, qs', htd⟩ := twoKinds_binop20 (B := B)
  have hσ : ValsOnly (VarEnv.empty.bindVal "Inn" (numTypeV (.int t))) := valsOnly_inn20 t
  cases op with
  | div s => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_sx20 hσ rfl s)
  | rem s => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_sx20 hσ rfl s)
  | shr s => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_sx20 hσ rfl s)
  | _ => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_nullary rfl)

/-- `relop_(Inn)` holds every integer comparison. -/
theorem typedAt_intRelOp20 (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntRelOp) :
    TypedAt (simEnv20 B) "relop_" "nt" (numTypeV (.int t)) (intRelOpV op) := by
  intro ρ _ hx
  obtain ⟨ps, qs, qs', htd⟩ := twoKinds_relop20 (B := B)
  have hσ : ValsOnly (VarEnv.empty.bindVal "Inn" (numTypeV (.int t))) := valsOnly_inn20 t
  cases op with
  | eq => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_nullary rfl)
  | ne => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_nullary rfl)
  | lt s => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_sx20 hσ rfl s)
  | gt s => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_sx20 hσ rfl s)
  | le s => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_sx20 hσ rfl s)
  | ge s => exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_sx20 hσ rfl s)

/-- `testop_(Inn)` holds `EQZ`. -/
theorem typedAt_intTestOp20 (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntTestOp) :
    TypedAt (simEnv20 B) "testop_" "nt" (numTypeV (.int t)) (intTestOpV op) := by
  intro ρ _ hx
  obtain ⟨ps, qs, htd⟩ := oneKind_testop20 (B := B)
  cases op
  exact hasTyp_innVariant20 htd (evalExp_var hx) (hasTypCase_nullary rfl)

/-- A float operator family holds every nullary operator case at a float type. -/
theorem typedAt_float20 {x : IL.Id} {d : Def} (htd : TwoKinds20 (B := B) x d)
    (t : Silmaril.Wasm.FloatType) {o : MixopS}
    (hf : findCase (instCases d 1) o = some (.tupT [], [])) :
    TypedAt (simEnv20 B) x "nt" (numTypeV (.float t)) (.case o (.tuple [])) := by
  intro ρ _ hx
  exact hasTyp_fnnVariant20 htd (evalExp_var hx) (hasTypCase_nullary hf)

/-- **`NumTyped` holds for the wasm-2.0 script**, for every interpretation of the primitives:
the encodings of V2's number types, numbers and scalar operators have their 2.0 IL types. -/
theorem numTyped_simEnv20 (B : Builtins) : NumTyped (simEnv20 B) where
  numtype := typedV_numtype20 B
  num t x _ := by
    intro ρ _ hx
    rcases t with t | t
    · exact hasTyp_num_int20 x (evalExp_var hx)
    · exact hasTyp_num_float20 t x (evalExp_var hx)
  i32 b := fun _ _ => hasTyp_num_int20 (t := .i32) b
    (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Equiv.Validation.evalExps_nil_iff.2 rfl,
      rfl⟩, rfl⟩)
  intUnOp t op _ := typedAt_intUnOp20 t op
  floatUnOp t op := by cases op <;> exact typedAt_float20 twoKinds_unop20 t rfl
  intBinOp t op := typedAt_intBinOp20 t op
  floatBinOp t op := by cases op <;> exact typedAt_float20 twoKinds_binop20 t rfl
  intTestOp t op := typedAt_intTestOp20 t op
  intRelOp t op := typedAt_intRelOp20 t op
  floatRelOp t op := by cases op <;> exact typedAt_float20 twoKinds_relop20 t rfl

end Silmaril.Wasm.SpecTec.Sim20.Pure
