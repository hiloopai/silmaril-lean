module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Store

/-!
# Definite failure of evaluation

`callDef` consults `B` only when every clause of a definition *definitely* fails
(`.error .undef`). The clauses `B` has to stand in for fail because a premise mentions a variable
that only that premise could bind (`$unrolldt`, `$unrollrt`, `$blocktype_` at `_IDX`). This file
propagates a definite failure from an unbound variable through the expression formers those
premises use: `EvalExpUndef env ρ e` says `e` definitely fails in `ρ`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Prims

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (TryClausesUndef)

/-- `e` definitely fails to evaluate in `ρ`. -/
def EvalExpUndef (env : Env) (ρ : VarEnv) (e : Exp) : Prop :=
  ∃ n, evalExp n env ρ e = .error .undef

/-- A definite failure persists with more fuel. -/
theorem evalExp_undef_of_le {m n : Nat} {env : Env} {ρ : VarEnv} {e : Exp} (h : m ≤ n)
    (hv : evalExp m env ρ e = .error .undef) : evalExp n env ρ e = .error .undef :=
  undef_of_le ((monoAt_of_le h).exp env ρ e) hv

/-- An unbound variable. -/
theorem evalExpUndef_var {env : Env} {ρ : VarEnv} {x : IL.Id} (hx : ρ.findVal? x = none) :
    EvalExpUndef env ρ (.varE x) :=
  ⟨1, by simp [evalExp, hx]⟩

/-- An injection of a failing payload. -/
theorem evalExpUndef_case {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp}
    (h : EvalExpUndef env ρ e) : EvalExpUndef env ρ (.caseE op e) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp [evalExp, h]⟩

/-- A tuple whose components before `e` evaluate and `e` fails. -/
theorem evalExpUndef_tup {env : Env} {ρ : VarEnv} {pre post : List Exp} {e : Exp}
    {vs : List Value} (hpre : EvalExps env ρ pre vs) (h : EvalExpUndef env ρ e) :
    EvalExpUndef env ρ (.tupE (pre ++ e :: post)) := by
  obtain ⟨n₁, h₁⟩ := hpre
  obtain ⟨n₂, h₂⟩ := h
  refine ⟨max n₁ (n₂ + 1) + 1, ?_⟩
  have e₁ := evalExps_ok_of_le (Nat.le_max_left n₁ (n₂ + 1)) h₁
  obtain ⟨k, hk⟩ : ∃ k, max n₁ (n₂ + 1) = k + 1 := ⟨max n₁ (n₂ + 1) - 1, by omega⟩
  rw [hk] at e₁ ⊢
  have e₂ : evalExp k env ρ e = .error .undef := evalExp_undef_of_le (by omega) h₂
  simp only [evalExps] at e₁
  simp only [evalExp, evalExps, List.mapM_append, e₁, List.mapM_cons, e₂]
  rfl

/-- A comparison whose left operand fails. -/
theorem evalExpUndef_cmpL {env : Env} {ρ : VarEnv} {op : CmpOp} {t : OpTyp} {e₁ e₂ : Exp}
    (h : EvalExpUndef env ρ e₁) : EvalExpUndef env ρ (.cmpE op t e₁ e₂) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp [evalExp, h, Bind.bind, Except.bind]⟩

/-- A comparison whose left operand evaluates and whose right one fails. -/
theorem evalExpUndef_cmpR {env : Env} {ρ : VarEnv} {op : CmpOp} {t : OpTyp} {e₁ e₂ : Exp}
    {v : Value} (h₁ : EvalExp env ρ e₁ v) (h : EvalExpUndef env ρ e₂) :
    EvalExpUndef env ρ (.cmpE op t e₁ e₂) := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h
  refine ⟨max n₁ n₂ + 1, ?_⟩
  simp [evalExp, evalExp_ok_of_le (Nat.le_max_left n₁ n₂) h₁,
    evalExp_undef_of_le (Nat.le_max_right n₁ n₂) h₂, Bind.bind, Except.bind]

/-- A list iteration over one domain whose source fails. -/
theorem evalExpUndef_iterList {env : Env} {ρ : VarEnv} {b : Exp} {x : IL.Id} {s : Exp}
    (h : EvalExpUndef env ρ s) : EvalExpUndef env ρ (.iterE b (.mk .list [.mk x s])) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 3, by simp [evalExp, evalIterE, evalDoms, domSrc, h,
    Bind.bind, Except.bind]⟩

/-- An option iteration over one domain whose source fails. -/
theorem evalExpUndef_iterOpt {env : Env} {ρ : VarEnv} {b : Exp} {x : IL.Id} {s : Exp}
    (h : EvalExpUndef env ρ s) : EvalExpUndef env ρ (.iterE b (.mk .opt [.mk x s])) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 3, by simp [evalExp, evalIterE, evalDoms, domSrc, h,
    Bind.bind, Except.bind]⟩

/-- A counted iteration over one domain whose source fails. -/
theorem evalExpUndef_iterListN {env : Env} {ρ : VarEnv} {b eₙ : Exp} {ido : Option IL.Id}
    {x : IL.Id} {s : Exp} (h : EvalExpUndef env ρ s) :
    EvalExpUndef env ρ (.iterE b (.mk (.listN eₙ ido) [.mk x s])) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 3, by simp [evalExp, evalIterE, evalDoms, domSrc, h,
    Bind.bind, Except.bind]⟩

/-- An `if` premise on a failing expression definitely fails. -/
theorem premsUndef_if {env : Env} {ρ : VarEnv} {e : Exp} {prs : List Prem}
    (h : EvalExpUndef env ρ e) : PremsUndef env ρ (.ifPr e :: prs) := by
  obtain ⟨n, h⟩ := h
  refine ⟨n + 2, ?_⟩
  have e1 : premHolds (n + 1) env ρ (.ifPr e) = .error .undef := by
    simp only [premHolds, h, Bind.bind, Except.bind]
  simp only [premsHold, List.foldlM_cons, e1, Bind.bind, Except.bind]

/-- A relational premise whose asserted instance fails to evaluate definitely fails. -/
theorem premsUndef_rule {env : Env} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS}
    {e : Exp} {prs : List Prem} {ws : List ArgV} (ha : EvalArgs env ρ args ws)
    (h : EvalExpUndef env ρ e) : PremsUndef env ρ (.rulePr x args op e :: prs) := by
  obtain ⟨n₁, h₁⟩ := ha
  obtain ⟨n₂, h₂⟩ := h
  refine ⟨max n₁ n₂ + 2, ?_⟩
  have e1 : premHolds (max n₁ n₂ + 1) env ρ (.rulePr x args op e) = .error .undef := by
    simp only [premHolds, evalArgs_ok_of_le (Nat.le_max_left n₁ n₂) h₁,
      evalExp_undef_of_le (Nat.le_max_right n₁ n₂) h₂, Bind.bind, Except.bind]
  simp only [premsHold, List.foldlM_cons, e1, Bind.bind, Except.bind]

/-- A call whose clauses definitely fail and which `B` does not answer, definitely fails. -/
theorem evalExpUndef_call {env : Env} {ρ : VarEnv} {x : IL.Id} {args : List Arg}
    {ws : List ArgV} {ps : List Param} {t : Typ} {cs : List Clause}
    (hρ : ρ.findDef? x = none) (ha : EvalArgs env ρ args ws)
    (hd : env.findDef? x = some (ps, t, cs)) (hu : TryClausesUndef env cs ws)
    (hb : env.builtins.call x ws = none) : EvalExpUndef env ρ (.callE x args) := by
  obtain ⟨n₁, h₁⟩ := ha
  obtain ⟨n₂, h₂⟩ := hu
  refine ⟨max n₁ n₂ + 2, ?_⟩
  simp only [evalExp, callDef, evalArgs_ok_of_le (Nat.le_max_left n₁ n₂) h₁, hρ, Option.getD_none,
    hd, tryClauses_undef_of_le (Nat.le_max_right n₁ n₂) h₂, hb, Bind.bind, Except.bind,
    Res.ofOption, Res.elimUndef]

/-- A call whose arguments fail definitely fails. -/
theorem evalExpUndef_callArg {env : Env} {ρ : VarEnv} {x : IL.Id} {e : Exp} {rest : List Arg}
    (h : EvalExpUndef env ρ e) : EvalExpUndef env ρ (.callE x (.expA e :: rest)) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 4, by simp [evalExp, callDef, evalArgs, evalArg, h, Bind.bind, Except.bind]⟩

end Silmaril.Wasm.SpecTec.Sim.Prims

namespace Silmaril.Wasm.SpecTec.Sim.Prims

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## A definite failure excludes a value -/

/-- An expression that definitely fails has no value. -/
theorem not_evalExp_of_undef {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (hu : EvalExpUndef env ρ e) (h : EvalExp env ρ e v) : False := by
  obtain ⟨n₁, h₁⟩ := h
  obtain ⟨n₂, h₂⟩ := hu
  have e₁ := evalExp_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  rw [evalExp_undef_of_le (Nat.le_max_right n₁ n₂) h₂] at e₁
  cases e₁

/-- Argument patterns that definitely fail do not match. -/
theorem not_matchArgs_of_undef {env : Env} {ρ ρ' : VarEnv} {pats : List Arg} {ws : List ArgV}
    (hu : MatchArgsUndef env ρ pats ws) (h : MatchArgs env ρ pats ws ρ') : False := by
  obtain ⟨n₁, h₁⟩ := h
  obtain ⟨n₂, h₂⟩ := hu
  have e₁ := matchArgs_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  rw [matchArgs_undef_of_le (Nat.le_max_right n₁ n₂) h₂] at e₁
  cases e₁

/-- Every component of an evaluated tuple has a value. -/
theorem evalExp_of_tupE_mem {env : Env} {ρ : VarEnv} {es : List Exp} {v : Value} {e : Exp}
    (h : EvalExp env ρ (.tupE es) v) (he : e ∈ es) : ∃ u, EvalExp env ρ e u := by
  obtain ⟨vs, hvs, -⟩ := evalExp_tupE_iff.1 h
  clear h
  induction es generalizing vs with
  | nil => cases he
  | cons a es ih =>
    obtain ⟨w, ws, hw, hws, -⟩ := evalExps_cons_iff.1 hvs
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨w, hw⟩
    · exact ih he ws hws

/-- The payload of an evaluated injection has a value. -/
theorem evalExp_of_caseE {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {v : Value}
    (h : EvalExp env ρ (.caseE op e) v) : ∃ u, EvalExp env ρ e u := by
  obtain ⟨w, hw, -⟩ := evalExp_caseE_iff.1 h
  exact ⟨w, hw⟩

/-- A relational premise that holds has an evaluated instance. -/
theorem evalExp_of_premsHold_rule {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {args : List Arg}
    {op : MixopS} {e : Exp} (h : PremsHold env ρ [.rulePr x args op e] ρ') :
    ∃ v, EvalExp env ρ e v := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | _ | n
  · simp [premsHold] at hn
  · simp [premsHold, premHolds] at hn
  · simp only [premsHold, List.foldlM_cons, List.foldlM_nil, premHolds] at hn
    cases ha : evalArgs n env ρ args <;> cases he : evalExp n env ρ e <;>
      simp_all [Bind.bind, Except.bind]
    exact ⟨_, n, he⟩

end Silmaril.Wasm.SpecTec.Sim.Prims
