module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Variable

/-!
# Family M: SpecTec → Core, `Step_pure/local.tee`

`fires_localTee_inv` inverts rule 30 of `Step_pure` under the declarative reading: whatever it
derives is `[val, LOCAL.TEE x] ~> [val, val, LOCAL.SET x]` with `val` a typed `val`.
`bwd_pure_localTee` is the `Backward.pure 30` obligation, given the decoders `StateDecode`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)

/-- A two-element list expression, inverted. -/
theorem evalExp_listE_two_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.listE [e₁, e₂]) v) :
    ∃ w₁ w₂, EvalExp env ρ e₁ w₁ ∧ EvalExp env ρ e₂ w₂ ∧ v = .list [w₁, w₂] := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
  obtain ⟨w₁, ws, h₁, hws, rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws', h₂, hws', rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hws
  obtain rfl := Silmaril.SpecTec.Sem.evalExps_nil_iff.1 hws'
  exact ⟨w₁, w₂, h₁, h₂, rfl⟩

/-- A three-element list expression, inverted. -/
theorem evalExp_listE_three_inv {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v : Value}
    (h : EvalExp env ρ (.listE [e₁, e₂, e₃]) v) :
    ∃ w₁ w₂ w₃, EvalExp env ρ e₁ w₁ ∧ EvalExp env ρ e₂ w₂ ∧ EvalExp env ρ e₃ w₃ ∧
      v = .list [w₁, w₂, w₃] := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
  obtain ⟨w₁, ws, h₁, hws, rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws', h₂, hws', rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hws
  obtain ⟨w₃, ws'', h₃, hws'', rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hws'
  obtain rfl := Silmaril.SpecTec.Sem.evalExps_nil_iff.1 hws''
  exact ⟨w₁, w₂, w₃, h₁, h₂, h₃, rfl⟩

/-- A pair expression, inverted. -/
theorem evalExp_tup2_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) v) :
    ∃ w₁ w₂, EvalExp env ρ e₁ w₁ ∧ EvalExp env ρ e₂ w₂ ∧ v = .tuple [w₁, w₂] := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w₁, ws, h₁, hws, rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws', h₂, hws', rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hws
  obtain rfl := Silmaril.SpecTec.Sem.evalExps_nil_iff.1 hws'
  exact ⟨w₁, w₂, h₁, h₂, rfl⟩

/-- The rule a `Fires` fact is about is the one `HasRuleAt` names. -/
theorem Fires.rule_eq {env : Env} {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem} {v : Value} (h : HasRuleAt env x "%~>%" k (.ruleD nm qs "%~>%" e prems))
    (hf : Fires env x k v) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧ EvalExp env (VarEnv.empty.bindVals σ) e v ∧
      ∀ pr ∈ prems, PremW env (DDerives env (otherwise env)) (otherwise env x [] k v)
        (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := h
  obtain ⟨t', rules', r, hrel', hk', hb⟩ := hf
  have hr : rules' = rules := by
    rw [hrel] at hrel'
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
    exact hrel'.2.2.2.symm
  subst hr
  have hr' : r = .ruleD nm qs "%~>%" e prems := Option.some.inj (hk'.symm.trans hk)
  subst hr'
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := hb
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  exact ⟨σ, hq, he, hp⟩

/-- **Inversion of `Step_pure/local.tee`.** -/
theorem fires_localTee_inv {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 30 Equiv.Execution.localTeeRule) {v : Value}
    (hf : Fires env "Step_pure" 30 v) :
    ∃ V X ρ, ValsOnly ρ ∧ HasTyp env ρ valT V ∧
      v = .tuple [.list [V, .case "LOCAL.TEE" X], .list [V, V, .case "LOCAL.SET" X]] := by
  obtain ⟨σ, hq, he, -⟩ := Fires.rule_eq h hf
  obtain ⟨V, fv, hV⟩ := hq "val" valT (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" idxT (by simp)
  have ev : EvalExp env (VarEnv.empty.bindVals σ)
      (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) V :=
    evalExp_subE_iff.2 (evalExp_var fv)
  have ex : EvalExp env (VarEnv.empty.bindVals σ) (.varE "x") X := evalExp_var fx
  obtain ⟨l₁, l₂, h₁, h₂, rfl⟩ := evalExp_tup2_inv he
  obtain ⟨a, b, ha, hb, rfl⟩ := evalExp_listE_two_inv h₁
  obtain ⟨c, d, e, hc, hd, he', rfl⟩ := evalExp_listE_three_inv h₂
  obtain ⟨xb, hxb, rfl⟩ := evalExp_caseE_iff.1 hb
  obtain ⟨xe, hxe, rfl⟩ := evalExp_caseE_iff.1 he'
  rw [EvalExp.unique ha ev, EvalExp.unique hc ev, EvalExp.unique hd ev, EvalExp.unique hxb ex,
    EvalExp.unique hxe ex]
  exact ⟨V, X, _, ⟨rfl, rfl, rfl⟩, hV, rfl⟩

section Backward

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **`Backward.pure 30` (`local.tee`)**: whatever `Step_pure/local.tee` derives from the image of
a configuration's code is the image of a Core `local.tee` step. -/
theorem bwd_pure_localTee (B : Builtins) {hn : H → String} {P : Numerics.Profile}
    {host : HostSemantics H} (Dc : StateDecode (simEnv B)) (s : Store H) (f : Frame)
    (is : List Admin) (w : Value) (_ : Typed (simEnv B) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv B) "Step_pure" 30 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨V, X, ρ, hρ, hV, heq⟩ := fires_localTee_inv (hasPureRules_simEnv B).localTee hf
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, and_true] at heq
  obtain ⟨his, rfl⟩ := heq
  rw [adminsToV_eq_map] at his
  obtain ⟨a, l, rfl, rfl, hl⟩ := List.map_eq_cons_iff.1 his
  obtain ⟨b, l', rfl, hb, hl'⟩ := List.map_eq_cons_iff.1 hl
  obtain rfl := List.map_eq_nil_iff.1 hl'
  obtain ⟨v, rfl⟩ := Dc.val a ρ hρ hV
  obtain ⟨x, rfl, rfl⟩ := Dc.localTee b X hb
  exact ⟨[v.toAdmin, v.toAdmin, .plain (.localSet x)], rfl, .variable .localTee⟩

end Backward

end Silmaril.Wasm.SpecTec.Sim.State
