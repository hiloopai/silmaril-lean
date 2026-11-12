module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecVector
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `Step`'s lifting and congruence rules

`Step` (36 rules) and `Step_read` (103) range over `config = state; instr*`
with `state = store; frame`, which is why `Equiv/Execution.lean` left them
alone: they need a bridge for the runtime, and
`Equiv/RuntimeBridge/` is building one.

**Five of `Step`'s rules need no bridge at all**, and they are the five that
matter most structurally, because they are how every other rule becomes a step
of the whole machine:

| rule | what it does | does it inspect the state? |
| --- | --- | --- |
| `pure` | lifts `Step_pure` | no — `z` is carried through untouched |
| `read` | lifts `Step_read` | no — `z` is passed to the premise, not examined |
| `ctxt-instrs` | congruence under a value prefix and an instruction suffix | no |
| `ctxt-label` | congruence under `LABEL_` | no |
| `ctxt-handler` | congruence under `HANDLER_` | no |

Only `ctxt-frame` destructures `state` into `store; frame`, and only the
remaining thirty use the store.

This file does `pure` and `read`.  Their characterisations quantify over an
**arbitrary** state value `z`, which is exactly the strength
`Equiv/Execution.lean` used for the components a rule does not inspect, and it
means they compose with every `Step_pure` characterisation already proved —
all 50 of them — without waiting for the bridge.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecStep

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## The two rules, as the pinned stream records them -/

/-- `Step/pure`, rule 0 of the pinned stream. -/
def stepPureRule : Rule :=
  (.ruleD "pure" [(.expP "z" (.varT "state" [])), (.expP "instr*" (.iterT (.varT "instr" [])
   .list)), (.expP "instr'*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE
   "instr*"))]))])), (.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr'") (.mk .list
   [(.mk "instr'" (.varE "instr'*"))]))]))]) [(.rulePr "Step_pure" [] "%~>%" (.tupE [(.iterE
   (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])), (.iterE (.varE "instr'")
   (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))])

/-- `Step/read`, rule 1 of the pinned stream. -/
def stepReadRule : Rule :=
  (.ruleD "read" [(.expP "z" (.varT "state" [])), (.expP "instr*" (.iterT (.varT "instr" [])
   .list)), (.expP "instr'*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE
   "instr*"))]))])), (.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr'") (.mk .list
   [(.mk "instr'" (.varE "instr'*"))]))]))]) [(.rulePr "Step_read" [] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE
   "instr*"))]))])), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE
   "instr'*"))]))]))])

/-- The pinned specification has them at indices 0 and 1 of `Step`. -/
structure HasStepLiftRules (env : Env) : Prop where
  /-- `Step/pure`, rule 0. -/
  pure : HasRuleAt env "Step" "%~>%" 0 stepPureRule
  /-- `Step/read`, rule 1. -/
  read : HasRuleAt env "Step" "%~>%" 1 stepReadRule

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- Discharged by `rfl` against the pinned stream. -/
theorem hasStepLiftRules_wasm30 : HasStepLiftRules (envOfScript Specs.wasm30) :=
  ⟨⟨_, _, _, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, rfl, rfl⟩⟩

set_option maxRecDepth 4000000 in
/-- The provenance transfers to the environment with Silmaril's numerics
installed: an interpretation does not touch `findRel?`. -/
theorem hasStepLiftRulesWithBuiltins :
    HasStepLiftRules ExecBuiltins.wasm30WithWasmNumerics :=
  ⟨⟨_, _, _, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, rfl, rfl⟩⟩

/-- `z; instr*`, the `config` injection. -/
def configV (z : Value) (is : List Value) : Value := .case "%;%" (.tuple [z, .list is])

/-! ## The two characterisations

Each says exactly which pairs of configurations the rule derives, for an
**arbitrary** state `z`.  Neither mentions the runtime bridge, and neither
needs it. -/

/-- The conclusion pattern both rules share: `(z; instr*) ~> (z; instr'*)`,
with the same `z` on both sides. -/
theorem matchExp_liftConcl_iff {env : Env} {ρ' : VarEnv} {v : Value} :
    MatchExp env VarEnv.empty
      (.tupE
        [.caseE "%;%" (.tupE [.varE "z",
           .iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")])]),
         .caseE "%;%" (.tupE [.varE "z",
           .iterE (.varE "instr'") (.mk .list [.mk "instr'" (.varE "instr'*")])])])
      v ρ' ↔
      ∃ z is js, v = .tuple [configV z is, configV z js] ∧
        ρ' = ((VarEnv.empty.bindVal "z" z).bindVal "instr*" (.list is)).bindVal
          "instr'*" (.list js) := by
  constructor
  · rintro h
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 h
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨zv, iv, τ, rfl, hz, hi⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)] at hi
    obtain ⟨is, rfl, his⟩ := hi
    rw [matchExp_freshVar_iff (by simp)] at his
    subst his
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨zv', jv, υ, rfl, hz', hj⟩ := matchExps_two_iff.1 hbvs
    rw [matchExp_boundVar_iff (w := zv) (by simp)] at hz'
    obtain ⟨rfl, rfl⟩ := hz'
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr'") (by simp) (by simp)] at hj
    obtain ⟨js, rfl, hjs⟩ := hj
    rw [matchExp_freshVar_iff (by simp)] at hjs
    subst hjs
    exact ⟨zv', is, js, rfl, rfl⟩
  · rintro ⟨z, is, js, rfl, rfl⟩
    exact matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)).2
              ⟨is, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_boundVar_iff (w := z) (by simp)).2 ⟨rfl, rfl⟩,
            (matchExp_iterE_list_iff (bindsVar_varE "instr'") (by simp) (by simp)).2
              ⟨js, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩

/-- Evaluating one of the two iterations back out: the list it was bound to. -/
theorem evalExp_instrIter {env : Env} {ρ : VarEnv} {x y : IL.Id} {vs : List Value}
    (hx : x ≠ "_") (h : ρ.findVal? y = some (.list vs)) :
    EvalExp env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE y)])) (.list vs) :=
  evalExp_iterBody_var (b := .varE x) (d := 0)
    (fun σ w hw => by simpa [evalExp] using hw) hx h

/-- **`Step/pure`, characterised exactly.**  It derives `(z; is) ~> (z; js)`
for *every* state value `z`, exactly when `Step_pure` derives `is ~> js`.
Composed with `Equiv/Execution.lean`'s and `Equiv/ExecNumeric.lean`'s
characterisations, this turns every one of them into a step of the whole
machine. -/
theorem ruleFires_stepPure_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v stepPureRule ↔
      ∃ z is js, v = .tuple [configV z is, configV z js] ∧
        Derives env "Step_pure" "%~>%" [] (Execution.stepV is js) := by
  unfold stepPureRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, is, js, rfl, rfl⟩ := matchExp_liftConcl_iff.1 hm
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, ws, w, hws, hw, hder⟩ := Validation.premHolds_rule_iff.1 hpr
    obtain rfl := Validation.evalArgs_nil_iff.1 hws
    refine ⟨z, is, js, rfl, ?_⟩
    obtain ⟨wvs, hwvs, rfl⟩ := evalExp_tupE_iff.1 hw
    obtain ⟨p, q, hq, hp1, hq1⟩ := Validation.evalExps_cons_iff.1 hwvs
    obtain ⟨q1, q2, hq', hq2, hq3⟩ := Validation.evalExps_cons_iff.1 hq1
    obtain rfl := Validation.evalExps_nil_iff.1 hq3
    obtain rfl : p = .list is := EvalExp.unique hp1 (evalExp_instrIter (by simp) (by simp))
    obtain rfl : q1 = .list js := EvalExp.unique hq2 (evalExp_instrIter (by simp) (by simp))
    subst hq'; subst hq
    exact hder
  · rintro ⟨z, is, js, rfl, hder⟩
    refine ⟨(((VarEnv.empty.bindVal "z" z).bindVal "instr*" (.list is)).bindVal "instr'*" (.list js)), (((VarEnv.empty.bindVal "z" z).bindVal "instr*" (.list is)).bindVal "instr'*" (.list js)), matchExp_liftConcl_iff.2 ⟨z, is, js, rfl, rfl⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_rule_iff.2
      ⟨rfl, [], Execution.stepV is js, Validation.evalArgs_nil_iff.2 rfl, ?_, hder⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    exact evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
      evalExp_instrIter (by simp) (by simp),
      Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_instrIter (by simp) (by simp),
        Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩

/-- **`Step/read`, characterised exactly.**  Its premise carries the state into
`Step_read` but still never inspects it. -/
theorem ruleFires_stepRead_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v stepReadRule ↔
      ∃ z is js, v = .tuple [configV z is, configV z js] ∧
        Derives env "Step_read" "%~>%" []
          (.tuple [configV z is, .list js]) := by
  unfold stepReadRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, is, js, rfl, rfl⟩ := matchExp_liftConcl_iff.1 hm
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, ws, w, hws, hw, hder⟩ := Validation.premHolds_rule_iff.1 hpr
    obtain rfl := Validation.evalArgs_nil_iff.1 hws
    refine ⟨z, is, js, rfl, ?_⟩
    obtain ⟨wvs, hwvs, rfl⟩ := evalExp_tupE_iff.1 hw
    obtain ⟨p, q, hq, hp1, hq1⟩ := Validation.evalExps_cons_iff.1 hwvs
    obtain ⟨q1, q2, hq', hq2, hq3⟩ := Validation.evalExps_cons_iff.1 hq1
    obtain rfl := Validation.evalExps_nil_iff.1 hq3
    obtain rfl : p = configV z is := by
      refine EvalExp.unique hp1 ?_
      exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
            evalExp_instrIter (by simp) (by simp),
            Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
    obtain rfl : q1 = .list js := EvalExp.unique hq2 (evalExp_instrIter (by simp) (by simp))
    subst hq'; subst hq
    exact hder
  · rintro ⟨z, is, js, rfl, hder⟩
    refine ⟨(((VarEnv.empty.bindVal "z" z).bindVal "instr*" (.list is)).bindVal "instr'*" (.list js)), (((VarEnv.empty.bindVal "z" z).bindVal "instr*" (.list is)).bindVal "instr'*" (.list js)), matchExp_liftConcl_iff.2 ⟨z, is, js, rfl, rfl⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_rule_iff.2
      ⟨rfl, [], .tuple [configV z is, .list js], Validation.evalArgs_nil_iff.2 rfl, ?_,
        hder⟩, Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
      Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_instrIter (by simp) (by simp),
        Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
    exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
      Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_instrIter (by simp) (by simp),
          Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩

/-! ## What this buys

`derives_of_ruleAt` turns a rule that fires into a derivation of the relation,
so the two theorems above compose with every `Step_pure` characterisation
already proved.  The corollary is stated once, generically; the instances are
one line each. -/

/-- **Every `Step_pure` derivation is a `Step` derivation**, at every state. -/
theorem derives_step_of_stepPure {env : Env} (h : HasStepLiftRules env)
    {is js : List Value} (z : Value)
    (hd : Derives env "Step_pure" "%~>%" [] (Execution.stepV is js)) :
    Derives env "Step" "%~>%" [] (.tuple [configV z is, configV z js]) :=
  derives_of_ruleAt h.pure (ruleFires_stepPure_iff.2 ⟨z, is, js, rfl, hd⟩)

/-- **Every `Step_read` derivation is a `Step` derivation**, at the state it
read. -/
theorem derives_step_of_stepRead {env : Env} (h : HasStepLiftRules env)
    {is js : List Value} {z : Value}
    (hd : Derives env "Step_read" "%~>%" [] (.tuple [configV z is, .list js])) :
    Derives env "Step" "%~>%" [] (.tuple [configV z is, configV z js]) :=
  derives_of_ruleAt h.read (ruleFires_stepRead_iff.2 ⟨z, is, js, rfl, hd⟩)

/-- `i32.and` steps the **whole machine**, at every state, with Silmaril's
numerics installed.  `Equiv/ExecBuiltins.lean` proved the `Step_pure`
derivation; this lifts it. -/
theorem derives_step_binopAnd_wasmBuiltins (i₁ i₂ : BitVec 32) (z : Value) :
    Derives ExecBuiltins.wasm30WithWasmNumerics "Step" "%~>%" []
      (.tuple
        [configV z
          [Execution.constV Execution.i32V (bvV i₁),
           Execution.constV Execution.i32V (bvV i₂),
           ExecNumeric.binopV Execution.i32V ExecBuiltins.andV],
         configV z
          [Execution.constV Execution.i32V
            (bvV (Wasm.Numerics.iand_ 32 i₁ i₂))]]) :=
  derives_step_of_stepPure hasStepLiftRulesWithBuiltins z
    (ExecBuiltins.derives_binopAnd_wasmBuiltins i₁ i₂)

end Silmaril.SpecTec.Equiv.ExecStep
