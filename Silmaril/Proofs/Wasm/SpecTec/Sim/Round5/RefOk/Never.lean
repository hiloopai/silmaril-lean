module

public import Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.Defs

/-!
# Round 5: `Reftype_ok` is never derivable, so `null` has one `Ref_ok` type

`DDerives` evaluates a rule's conclusion. `Reftype_ok`'s only rule concludes
`(C, REF NULL? heaptype)`, and the IL writes `NULL?` as an option iteration with an empty domain,
`iterE (NULL) (opt [])`, which never evaluates (`not_evalExp_iterOptNil`). So `Reftype_ok` is
empty in every `simEnv B` (`not_reftypeOk`), and `Ref_ok/sub`, whose second premise is
`Reftype_ok`, never fires. The only rule left that types `REF.NULL_ADDR` is `Ref_ok/null`, so
SpecTec types `null` at `REF NULL BOT` only (`eq_bot_of_dderives_null`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.RefOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)

/-- **An option iteration with no domain variables never evaluates**: the evaluator asserts a
non-empty domain (`evalIterE`). -/
theorem not_evalExp_iterOptNil {env : Env} {ρ : VarEnv} {e : Exp} {v : Value} :
    ¬ EvalExp env ρ (.iterE e (.mk .opt [])) v := by
  rintro ⟨n, h⟩
  rcases n with _ | n
  · simp [evalExp] at h
  rcases n with _ | n
  · simp [evalExp, evalIterE] at h
  simp [evalExp, evalIterE, Res.assert] at h

/-- The relation a one-relation `rec` group defines, as `envOfScript` records it. -/
def relOf : Def → List Param × MixopS × Typ × List Rule
  | .recD [.relD _ ps op t rules] => (ps, op, t, rules)
  | _ => ([], "", .boolT, [])

set_option maxRecDepth 100000 in
/-- `Reftype_ok` in `simEnv B`. -/
theorem findRel_reftypeOk (B : Builtins) :
    (simEnv B).findRel? "Reftype_ok" = some Equiv.Validation.reftypeOkRel := rfl

set_option maxRecDepth 100000 in
/-- `Ref_ok` in `simEnv B`: the script's definition 627. -/
theorem findRel_refOk (B : Builtins) :
    (simEnv B).findRel? "Ref_ok" = some (relOf Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d627) :=
  rfl

/-- The second component of a two-component tuple expression's value. -/
theorem evalExp_tup2_snd {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) v) : ∃ w, EvalExp env ρ e₂ w := by
  obtain ⟨vs, hvs, -⟩ := evalExp_tupE_iff.1 h
  obtain ⟨-, ws, -, -, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨w, -, -, hw, -⟩ := Equiv.Validation.evalExps_cons_iff.1 hws
  exact ⟨w, hw⟩

/-- The first component of a two-component tuple expression's value. -/
theorem evalExp_tup2_fst {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) v) : ∃ w, EvalExp env ρ e₁ w := by
  obtain ⟨vs, hvs, -⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w, -, -, hw, -⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  exact ⟨w, hw⟩

/-- `REF NULL? heaptype` never evaluates. -/
theorem not_evalExp_refNullOpt {env : Env} {ρ : VarEnv} {e : Exp} {v : Value} :
    ¬ EvalExp env ρ (.caseE "REF" (.tupE [.iterE (.caseE "NULL" (.tupE [])) (.mk .opt []), e]))
      v := fun h =>
  have hu : ∃ u, EvalExp env ρ (.tupE [.iterE (.caseE "NULL" (.tupE [])) (.mk .opt []), e]) u :=
    (evalExp_caseE_iff.1 h).imp fun _ h => h.1
  have hn : ∃ w, EvalExp env ρ (.iterE (.caseE "NULL" (.tupE [])) (.mk .opt [])) w :=
    evalExp_tup2_fst hu.choose_spec
  not_evalExp_iterOptNil hn.choose_spec

/-- **`Reftype_ok` is never derivable** in any `simEnv B`, under any reading of `otherwise`. -/
theorem not_reftypeOk (B : Builtins) (O : ElseI) (op : MixopS) (args : List ArgV) (v : Value) :
    ¬ DDerives (simEnv B) O "Reftype_ok" op args v := by
  rintro ⟨hrel, hrule, -, -, he, -⟩
  rw [findRel_reftypeOk] at hrel
  simp only [Equiv.Validation.reftypeOkRel, Option.some.injEq, Prod.mk.injEq] at hrel
  obtain ⟨-, -, -, rfl⟩ := hrel
  rename_i i _ _ _ _ _ _
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq, Rule.ruleD.injEq] at hrule
    obtain ⟨-, -, -, rfl, -⟩ := hrule
    obtain ⟨w, hw⟩ := evalExp_tup2_snd he
    exact not_evalExp_refNullOpt hw
  · simp at hrule

/-- The components of a three-component tuple expression's value. -/
theorem evalExp_tup3_inv {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {a b c : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂, e₃]) (.tuple [a, b, c])) :
    EvalExp env ρ e₁ a ∧ EvalExp env ρ e₂ b ∧ EvalExp env ρ e₃ c := by
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w₁, ws₁, rfl, h₁, hs₁⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws₂, rfl, h₂, hs₂⟩ := Equiv.Validation.evalExps_cons_iff.1 hs₁
  obtain ⟨w₃, ws₃, rfl, h₃, hs₃⟩ := Equiv.Validation.evalExps_cons_iff.1 hs₂
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hs₃
  simp only [Value.tuple.injEq, List.cons.injEq] at hv
  obtain ⟨rfl, rfl, rfl, -⟩ := hv
  exact ⟨h₁, h₂, h₃⟩

/-- `Ref_ok/null`'s type, `REF NULL BOT`, evaluates to the image of Core's `ref null bot`. -/
theorem evalExp_refNullBot {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "REF" (.tupE [.optE (some (.caseE "NULL" (.tupE []))),
        .caseE "BOT" (.tupE [])])) (tyV (Ty.ref true .bot)) :=
  evalExp_case (evalExp_tup2 (evalExp_optE_some_iff.2 ⟨_, evalExp_case
    (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩), rfl⟩)
    (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)))

/-- **SpecTec types `null` at `REF NULL BOT` only**: of `Ref_ok`'s nine rules, `null` is the
only one whose conclusion has `REF.NULL_ADDR` in second place, apart from `sub`, which needs
`Reftype_ok`. Any store value, any reading of `otherwise`. -/
theorem eq_bot_of_dderives_null (B : Builtins) (O : ElseI) (sv : Value) (rt : CRefType)
    (h : DDerives (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [sv, refToValue .null, tyV rt])) :
    rt = .ref true .bot := by
  obtain ⟨hrel, hrule, -, -, he, hp⟩ := h
  rw [findRel_refOk] at hrel
  simp only [relOf, Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d627, Option.some.injEq,
    Prod.mk.injEq] at hrel
  obtain ⟨-, -, -, rfl⟩ := hrel
  rename_i i _ _ _ _ _ _
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
    Rule.ruleD.injEq, List.getElem?_nil, reduceCtorEq] at hrule
  · obtain ⟨-, -, -, rfl, -⟩ := hrule
    exact Equiv.Validation.tyV_inj _ _ ((evalExp_tup3_inv he).2.2.unique evalExp_refNullBot)
  all_goals try (obtain ⟨-, -, -, rfl, -⟩ := hrule
                 obtain ⟨w, -, hw⟩ := evalExp_caseE_iff.1 (evalExp_tup3_inv he).2.1
                 simp [refToValue] at hw)
  obtain ⟨-, -, -, -, rfl⟩ := hrule
  have hd := hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  cases hd with
  | rulePr _ _ hd => exact (not_reftypeOk B O _ _ _ hd).elim

end Silmaril.Wasm.SpecTec.Sim.Round5.RefOk
