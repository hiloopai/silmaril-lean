module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Thms

/-!
# Round 5: the shape of `$vcvtop__`'s clauses

`$vcvtop__` (`Original.d539`) has three clauses. Each matches the shapes as `Lnn X M` (the first
with one `M` for both shapes, the others with `M_1`, `M_2`), binds `vcvtop` and `v_1`, and has
two leading `if` premises: a test of `$halfop`/`$zeroop` on the operator, then `c_1* = …`,
which mentions the unbound list variable `c_1*`. So a clause either fails to match or reaches
the second premise and definitely fails there, provided the first premise evaluates to *some*
value (or definitely fails). This module states that reduction (`tryClausesUndef_vcvtop`): what
is left is the evaluation of the three leading conditions (`CondsOk`), which only involves
`$halfop` and `$zeroop` and is discharged operator by operator in the sibling modules.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Convert

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30
open Round4Int (BI)
open Simd (clausesOf unboundPrem premsUndef_unbound findDef_Halfop findDef_Zeroop)
open Prims (EvalExpUndef)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-! ## The clauses, read off the script -/

/-- The shape pattern `Lnn X M`. -/
abbrev shPat (x m : IL.Id) : Exp := .caseE "%X%" (.tupE [.varE x, .varE m])

/-- The argument patterns of a clause of `$vcvtop__`. -/
abbrev cvtPats (m₁ m₂ : IL.Id) : List Arg :=
  [.expA (shPat "Lnn_1" m₁), .expA (shPat "Lnn_2" m₂), .expA (.varE "vcvtop"), .expA (.varE "v_1")]

/-- A call of `$halfop`/`$zeroop` on the clause's shapes and operator. -/
abbrev opCall (f m₁ m₂ : IL.Id) : Exp :=
  .callE f [.expA (shPat "Lnn_1" m₁), .expA (shPat "Lnn_2" m₂), .expA (.varE "vcvtop")]

/-- The first clause's leading condition: `$halfop(…) = ε ∧ $zeroop(…) = ε`. -/
abbrev cond₁ : Exp :=
  .binE .andOp .boolT (.cmpE .eqOp .boolT (opCall "halfop" "M" "M") (.optE none))
    (.cmpE .eqOp .boolT (opCall "zeroop" "M" "M") (.optE none))

/-- The second clause's leading condition: `$halfop(…) = half`. -/
abbrev cond₂ : Exp :=
  .cmpE .eqOp .boolT (opCall "halfop" "M_1" "M_2") (.optE (some (.varE "half")))

/-- The third clause's leading condition: `$zeroop(…) = ZERO`. -/
abbrev cond₃ : Exp :=
  .cmpE .eqOp .boolT (opCall "zeroop" "M_1" "M_2") (.optE (some (.caseE "ZERO" (.tupE []))))

set_option maxRecDepth 100000 in
/-- **The clauses of `$vcvtop__`**, up to what follows their second premise. -/
theorem clauses_vcvtop : ∃ (q₁ q₂ q₃ : List Param) (r₁ r₂ r₃ : Exp) (t₁ t₂ t₃ : List Prem),
    clausesOf Original.d539 =
      [.defD q₁ (cvtPats "M" "M") (.varE "v") (.ifPr cond₁ :: unboundPrem "c_1" "c_1*" r₁ :: t₁),
       .defD q₂ (cvtPats "M_1" "M_2") (.varE "v") (.ifPr cond₂ :: unboundPrem "c_1" "c_1*" r₂ :: t₂),
       .defD q₃ (cvtPats "M_1" "M_2") (.varE "v")
        (.ifPr cond₃ :: unboundPrem "c_1" "c_1*" r₃ :: t₃)] :=
  ⟨_, _, _, _, _, _, _, _, _, rfl⟩

/-! ## Matching -/

/-- The scope the first clause's patterns build when both shapes have the same `M`. -/
abbrev scope₁ (l₁ m l₂ o w : Value) : VarEnv :=
  ((((VarEnv.empty.bindVal "Lnn_1" l₁).bindVal "M" m).bindVal "Lnn_2" l₂).bindVal "vcvtop" o).bindVal
    "v_1" w

/-- The scope the second and third clauses' patterns build. -/
abbrev scope₂ (l₁ m₁ l₂ m₂ o w : Value) : VarEnv :=
  (((((VarEnv.empty.bindVal "Lnn_1" l₁).bindVal "M_1" m₁).bindVal "Lnn_2" l₂).bindVal "M_2"
    m₂).bindVal "vcvtop" o).bindVal "v_1" w

/-- The arguments of a call. -/
abbrev cvtArgs (l₁ m₁ l₂ m₂ o w : Value) : List ArgV :=
  [.val (.case "%X%" (.tuple [l₁, m₁])), .val (.case "%X%" (.tuple [l₂, m₂])), .val o, .val w]

/-- `Lnn X M` matches a shape image with fresh variables. -/
theorem matchExp_shPat {env : Env} {ρ : VarEnv} {x m : IL.Id} {l mv : Value}
    (hx : ρ.findVal? x = none) (hm : (ρ.bindVal x l).findVal? m = none) :
    MatchExp env ρ (shPat x m) (.case "%X%" (.tuple [l, mv])) ((ρ.bindVal x l).bindVal m mv) :=
  ⟨6, by
    simp [matchExp, matchExps, hx, hm, Res.assert, Res.ofOption, Bind.bind, Except.bind,
      Value.asTuple?, Value.asCase?]⟩

/-- `Lnn X M` with `M` already bound to `m` matches only an `M` equal to `m`. -/
theorem matchExp_shPat_bound {env : Env} {ρ : VarEnv} {x m : IL.Id} {l mv mw : Value}
    (hx : ρ.findVal? x = none) (hm : (ρ.bindVal x l).findVal? m = some mw) (he : mw = mv) :
    MatchExp env ρ (shPat x m) (.case "%X%" (.tuple [l, mv])) (ρ.bindVal x l) :=
  ⟨6, by
    simp [matchExp, matchExps, hx, hm, he, Res.assert, Res.ofOption, Bind.bind, Except.bind,
      Value.asTuple?, Value.asCase?]⟩

/-- `Lnn X M` with `M` bound to `mw ≠ mv` definitely fails. -/
theorem matchExp_shPat_undef {env : Env} {ρ : VarEnv} {x m : IL.Id} {l mv mw : Value}
    (hx : ρ.findVal? x = none) (hm : (ρ.bindVal x l).findVal? m = some mw) (he : mw ≠ mv) :
    MatchExpUndef env ρ (shPat x m) (.case "%X%" (.tuple [l, mv])) :=
  ⟨6, by
    simp [matchExp, matchExps, hx, hm, he, Res.assert, Res.ofOption, Bind.bind, Except.bind,
      Value.asTuple?, Value.asCase?]⟩

/-- The first clause's patterns match when the two `M` agree. -/
theorem matchArgs_cvt₁ {env : Env} (l₁ m l₂ o w : Value) :
    MatchArgs env VarEnv.empty (cvtPats "M" "M") (cvtArgs l₁ m l₂ m o w) (scope₁ l₁ m l₂ o w) :=
  matchArgs_cons (matchArg_expA (matchExp_shPat (by simp) (by simp)))
    (matchArgs_cons (matchArg_expA (matchExp_shPat_bound (by simp) (by simp) rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))

/-- The first clause's patterns definitely fail when the two `M` differ. -/
theorem matchArgs_cvt₁_undef {env : Env} {l₁ m₁ l₂ m₂ : Value} (o w : Value) (h : m₁ ≠ m₂) :
    MatchArgsUndef env VarEnv.empty (cvtPats "M" "M") (cvtArgs l₁ m₁ l₂ m₂ o w) :=
  matchArgs_cons_undef_tail (matchArg_expA (matchExp_shPat (by simp) (by simp)))
    (matchArgs_cons_undef (matchArg_expA_undef (matchExp_shPat_undef (by simp) (by simp) h)))

/-- The second and third clauses' patterns match. -/
theorem matchArgs_cvt₂ {env : Env} (l₁ m₁ l₂ m₂ o w : Value) :
    MatchArgs env VarEnv.empty (cvtPats "M_1" "M_2") (cvtArgs l₁ m₁ l₂ m₂ o w)
      (scope₂ l₁ m₁ l₂ m₂ o w) :=
  matchArgs_cons (matchArg_expA (matchExp_shPat (by simp) (by simp)))
    (matchArgs_cons (matchArg_expA (matchExp_shPat (by simp) (by simp)))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))

/-! ## The premises -/

/-- An expression evaluates to something or definitely fails: it does not need unbounded fuel. -/
def EvalsOrUndef (env : Env) (ρ : VarEnv) (e : Exp) : Prop :=
  (∃ v, EvalExp env ρ e v) ∨ EvalExpUndef env ρ e

/-- **A leading `if` that evaluates, then an `if` over an unbound list variable**: the premises
definitely fail, whatever the leading condition's value. -/
theorem premsUndef_cond_unbound {env : Env} {ρ : VarEnv} {e : Exp} {c cs : IL.Id} {rhs : Exp}
    {rest : List Prem} (he : EvalsOrUndef env ρ e) (h : ρ.findVal? cs = none) :
    PremsUndef env ρ (.ifPr e :: unboundPrem c cs rhs :: rest) := by
  rcases he with ⟨v, n, hv⟩ | hu
  · obtain ⟨k, hk⟩ := premsUndef_unbound (env := env) (c := c) (rhs := rhs) (rest := rest) h
    refine ⟨max n k + 2, ?_⟩
    have hk' := premsHold_undef_of_le (m := k) (n := max n k + 2) (by omega) hk
    have hv' : evalExp (max n k) env ρ e = .ok v := evalExp_ok_of_le (Nat.le_max_left n k) hv
    by_cases hb : v = .bool true
    · have e1 : premHolds (max n k + 1) env ρ (.ifPr e) = .ok ρ := by
        simp [premHolds, hv', hb, Bind.bind, Except.bind]
      simp only [premsHold, List.foldlM_cons, e1, Bind.bind, Except.bind] at hk' ⊢
      exact hk'
    · have e1 : premHolds (max n k + 1) env ρ (.ifPr e) = .error .undef := by
        simp only [premHolds, hv', Bind.bind, Except.bind]
        exact Res.assert_neg hb _
      simp only [premsHold, List.foldlM_cons, e1, Bind.bind, Except.bind]
  · exact Prims.premsUndef_if hu

/-- The three leading conditions evaluate (or definitely fail) in the scopes the patterns build. -/
structure CondsOk (env : Env) (l₁ m₁ l₂ m₂ o w : Value) : Prop where
  c₁ : m₁ = m₂ → EvalsOrUndef env (scope₁ l₁ m₁ l₂ o w) cond₁
  c₂ : EvalsOrUndef env (scope₂ l₁ m₁ l₂ m₂ o w) cond₂
  c₃ : EvalsOrUndef env (scope₂ l₁ m₁ l₂ m₂ o w) cond₃

/-- **Every clause of `$vcvtop__` definitely fails** where the leading conditions evaluate. -/
theorem tryClausesUndef_vcvtop {env : Env} {l₁ m₁ l₂ m₂ o w : Value}
    (h : CondsOk env l₁ m₁ l₂ m₂ o w) :
    TryClausesUndef env (clausesOf Original.d539) (cvtArgs l₁ m₁ l₂ m₂ o w) := by
  obtain ⟨q₁, q₂, q₃, r₁, r₂, r₃, t₁, t₂, t₃, hc⟩ := clauses_vcvtop
  rw [hc]
  have h₂ : TryClausesUndef env
      [.defD q₂ (cvtPats "M_1" "M_2") (.varE "v") (.ifPr cond₂ :: unboundPrem "c_1" "c_1*" r₂ :: t₂),
       .defD q₃ (cvtPats "M_1" "M_2") (.varE "v") (.ifPr cond₃ :: unboundPrem "c_1" "c_1*" r₃ :: t₃)]
      (cvtArgs l₁ m₁ l₂ m₂ o w) := IntNumeric.tryClausesUndef_skip_prem (matchArgs_cvt₂ l₁ m₁ l₂ m₂ o w)
    (premsUndef_cond_unbound (cs := "c_1*") h.c₂ (by simp)) (IntNumeric.tryClausesUndef_skip_prem
      (matchArgs_cvt₂ l₁ m₁ l₂ m₂ o w) (premsUndef_cond_unbound (cs := "c_1*") h.c₃ (by simp))
      IntNumeric.tryClausesUndef_nil)
  by_cases hm : m₁ = m₂
  · subst hm
    exact IntNumeric.tryClausesUndef_skip_prem (matchArgs_cvt₁ l₁ m₁ l₂ o w)
      (premsUndef_cond_unbound (cs := "c_1*") (h.c₁ rfl) (by simp)) h₂
  · exact IntNumeric.tryClausesUndef_skip_match (matchArgs_cvt₁_undef o w hm) h₂

/-! ## Evaluating the leading conditions -/

/-- Value comparison is decidable equality. -/
theorem value_beq (a b : Value) : (a == b) = decide (a = b) := rfl

/-- Binding a one-element list is binding its element. -/
theorem bindVals_single (ρ : VarEnv) (x : IL.Id) (v : Value) :
    ρ.bindVals [(x, v)] = ρ.bindVal x v := rfl

/-- Unfold the evaluator on a leading condition, `$halfop` and `$zeroop` included, at a fixed
fuel. -/
macro "cond_simp" : tactic => `(tactic|
  simp [evalExp, evalExps, evalArgs, evalArg, callDef, tryClauses, matchArgs, matchArg, matchExp,
    matchExps, matchIterE, evalIterE, evalDoms, domVar, domSrc, argSubOk, premsHold, cmpValues,
    binValues, boolBin, boolShort, Res.assert, Res.ofOption, Res.elimUndef, Bind.bind, Except.bind,
    pure, Except.pure, Value.asTuple?, Value.asCase?, Value.asOpt?, VarEnv.findVals?,
    bindVals_single, value_beq, IntNumeric.defOf, clausesOf, Original.d510, Original.d511,
    findDef_Halfop, findDef_Zeroop, Vec.vConvertOpV, Vec.halfV, Vec.sxV, caseNilV])

/-- A shape's image is `Lnn X M`. -/
theorem shapeV_split (s : Shape) : ∃ l m, Vec.shapeV s = .case "%X%" (.tuple [l, m]) := by
  rcases s with s | s <;> exact ⟨_, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
