module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Complete

/-!
# Strict evaluation and our evaluator

`evalExp_of_strict`: a strict value of a fragment expression is its value under `Sem.evalExp`, in
any environment and scope (the fragment is closed). The converse holds whenever the strict value
exists (`strict_of_evalExp`); it can fail to exist only through eval.ml's short-circuit, which
`shortCircuit_evalExp` and `shortCircuit_strict` witness.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- `boolShort` settles a Boolean operator from its left operand only with the value both
operands give. -/
theorem boolShort_agree {op : BinOp} {u w r v : Value} (hs : boolShort op u = some r)
    (h : binValues op u w = .ok v) : r = v := by
  cases op <;> cases u <;> simp_all [boolShort] <;> rename_i b <;> cases b <;>
    simp_all <;> subst hs <;> cases w <;>
    simp_all [binValues, boolBin, Res.ofOption]

theorem evalExp_of_strict {env : Env} {ρ : VarEnv} :
    ∀ {e : FExp} {v : Value}, e.strict = some v → EvalExp env ρ e.toExp v
  | .bool _, _, h => by cases h; exact evalExp_boolE_iff.2 rfl
  | .nat _, _, h => by cases h; exact evalExp_numE_iff.2 rfl
  | .int _, _, h => by cases h; exact evalExp_numE_iff.2 rfl
  | .un _ _ a, _, h => by
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.1 h
    exact evalExp_unE_iff.2 ⟨u, evalExp_of_strict hu, resVal_ok h⟩
  | .bin op _ a b, _, h => by
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
    refine evalExp_binE_iff.2 ⟨u, evalExp_of_strict hu, ?_⟩
    cases hs : boolShort op u with
    | some r => exact .inl (by rw [boolShort_agree hs (resVal_ok h)])
    | none => exact .inr ⟨rfl, w, evalExp_of_strict hw, resVal_ok h⟩
  | .cmp _ _ a b, _, h => by
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
    exact evalExp_cmpE_iff.2 ⟨u, w, evalExp_of_strict hu, evalExp_of_strict hw, resVal_ok h⟩

theorem strict_of_evalExp {env : Env} {ρ : VarEnv} {e : FExp} {v : Value}
    (h : EvalExp env ρ e.toExp v) (hd : e.strict.isSome) : e.strict = some v := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hd
  rw [hu, (evalExp_of_strict (env := env) (ρ := ρ) hu).unique h]

/-- `false /\ (1 / 0 = 1)`. -/
def shortCircuitExp : FExp :=
  .bin .andOp .boolT (.bool false) (.cmp .eqOp .boolT (.bin .divOp (.numT .natT) (.nat 1) (.nat 0))
    (.nat 1))

/-- Our evaluator short-circuits `false /\ (1 / 0 = 1)` to `false`, as `il/eval.ml` does. -/
theorem shortCircuit_evalExp {env : Env} {ρ : VarEnv} :
    EvalExp env ρ shortCircuitExp.toExp (.bool false) :=
  evalExp_binE_iff.2 ⟨.bool false, evalExp_boolE_iff.2 rfl, .inl rfl⟩

/-- Strictly, `1 / 0` has no value, so neither has `false /\ (1 / 0 = 1)`. -/
theorem shortCircuit_strict : shortCircuitExp.strict = none := by
  simp [shortCircuitExp, FExp.strict, binValues, Num.bin, Res.ofOption, FExp.resVal]

end Silmaril.Wasm.SpecTec.Meta
