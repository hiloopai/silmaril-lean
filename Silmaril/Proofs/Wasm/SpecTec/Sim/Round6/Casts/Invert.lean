module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.Forward

/-!
# Round 6: inverting `Step`'s rules 1–5 under the new reading

`Bwd.inv_read`, `Bwd.inv_ctxtInstrs`, `Bwd.inv_ctxtLabel`, `Bwd.inv_ctxtHandler` and
`Bwd.inv_ctxtFrame` (`Bwd/Invert.lean`), copied for `FiresB`: the five rules' conclusions have no
empty-domain option, so a firing is a rule body (`Reading.firesB_body`) whose premise is read by
`DDerivesB`, and the read-back premise is an `SReadB` or `SStepB` step. Rule 0 (`pure`) and the
rules from 6 on transfer to the old reading as they are (`Reading.firesB_step_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecStepRules
  (pureRule readRule ctxtInstrsRule ctxtLabelRule ctxtHandlerRule ctxtFrameRule)
open Silmaril.SpecTec.Equiv.Execution (iterPat valsPat evalExp_iterPat evalExp_valsPat)
open Bwd (rulePrem_nil ifPrem_true tuple2_inj)
open Reading (FiresB SStepB SReadB)

variable {env : Env}

/-- `Step/read`, read back under the new reading: both sides share the state, and the configuration takes a
`Step_read` step to the new code. -/
theorem inv_readB (h₀ : HasRuleAt env "Step" "%~>%" 1 readRule) {v₁ v₂ : Value}
    (hf : FiresB env "Step" 1 (.tuple [v₁, v₂])) :
    ∃ z is js, v₁ = cfgV z is ∧ v₂ = cfgV z js ∧ SReadB env (cfgV z is) js := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (Reading.firesB_body h₀ (by rfl) hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (.tail _ (.head _))
  obtain ⟨js, fj, -⟩ :=
    quant_list (x := "instr'*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ej : EvalExp env _ (iterPat "instr'" "instr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  have ez := evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei)
  have hc : Value.tuple [v₁, v₂] = .tuple [cfgV z is, cfgV z js] :=
    EvalExp.unique he (evalExp_tup2 ez (evalExp_case (evalExp_tup2 (evalExp_var fz) ej)))
  have hd : SReadB env (cfgV z is) js := rulePrem_nil (hp _ (.head _)) (evalExp_tup2 ez ej)
  exact ⟨z, is, js, (tuple2_inj hc).1, (tuple2_inj hc).2, hd⟩

/-! ## The four context rules -/

/-- What `Step/ctxt-instrs` says, read back. -/
def CtxtInstrsInvB (env : Env) (v₁ v₂ : Value) : Prop :=
  ∃ z z' vs is is' rest, (∃ ρ, ValsOnly ρ ∧ HasTyp env ρ valsT (.list vs)) ∧
    (vs ≠ [] ∨ rest ≠ []) ∧ v₁ = cfgV z (vs ++ is ++ rest) ∧ v₂ = cfgV z' (vs ++ is' ++ rest) ∧
    SStepB env (cfgV z is) (cfgV z' is')

/-- `Step/ctxt-instrs`, read back, for every split. -/
theorem inv_ctxtInstrsB (h₀ : HasRuleAt env "Step" "%~>%" 2 ctxtInstrsRule) {v₁ v₂ : Value}
    (hf : FiresB env "Step" 2 (.tuple [v₁, v₂])) : CtxtInstrsInvB env v₁ v₂ := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (Reading.firesB_body h₀ (by rfl) hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨vs, fv, tv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq (.tail _ (.head _))
  obtain ⟨is, fi, -⟩ :=
    quant_list (x := "instr*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨rest, fr, -⟩ := quant_list (x := "instr_1*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨z', fz', -⟩ :=
    quant_of (x := "z'") (t := stateT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ev : EvalExp env _ (valsPat "val" "val*") (.list vs) := evalExp_valsPat (by decide) fv
  have ev' : EvalExp env _ (iterPat "val" "val*") (.list vs) := evalExp_iterPat (by decide) fv
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have er : EvalExp env _ (iterPat "instr_1" "instr_1*") (.list rest) :=
    evalExp_iterPat (by decide) fr
  have hc : Value.tuple [v₁, v₂] =
      .tuple [cfgV z (vs ++ (is ++ rest)), cfgV z' (vs ++ (is' ++ rest))] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_cat ev (evalExp_cat ei er))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') (evalExp_cat ev (evalExp_cat ei' er)))))
  have hs : SStepB env (cfgV z is) (cfgV z' is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  have hb : Value.bool (decide (vs ≠ [] ∨ rest ≠ [])) = .bool true :=
    ifPrem_true (hp _ (.tail _ (.head _))) (evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er))
  have hne : vs ≠ [] ∨ rest ≠ [] := of_decide_eq_true (Value.bool.inj hb)
  have h₁ : v₁ = cfgV z (vs ++ is ++ rest) := by rw [List.append_assoc]; exact (tuple2_inj hc).1
  have h₂ : v₂ = cfgV z' (vs ++ is' ++ rest) := by rw [List.append_assoc]; exact (tuple2_inj hc).2
  exact ⟨z, z', vs, is, is', rest, ⟨_, valsOnly_bindVals σ, tv⟩, hne, h₁, h₂, hs⟩

/-- `Step/ctxt-label`, read back. -/
theorem inv_ctxtLabelB (h₀ : HasRuleAt env "Step" "%~>%" 3 ctxtLabelRule) {v₁ v₂ : Value}
    (hf : FiresB env "Step" 3 (.tuple [v₁, v₂])) :
    ∃ z z' n cont is is',
      v₁ = cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])] ∧
      v₂ = cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])] ∧
      SStepB env (cfgV z is) (cfgV z' is') := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (Reading.firesB_body h₀ (by rfl) hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := nT) hq (.tail _ (.head _))
  obtain ⟨cont, fc, -⟩ :=
    quant_list (x := "instr_0*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨z', fz', -⟩ :=
    quant_of (x := "z'") (t := stateT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ec : EvalExp env _ (iterPat "instr_0" "instr_0*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have hc : Value.tuple [v₁, v₂] =
      .tuple [cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])],
        cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz')
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei'))))))
  have hs : SStepB env (cfgV z is) (cfgV z' is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  exact ⟨z, z', n, cont, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

/-- `Step/ctxt-handler`, read back. -/
theorem inv_ctxtHandlerB (h₀ : HasRuleAt env "Step" "%~>%" 4 ctxtHandlerRule) {v₁ v₂ : Value}
    (hf : FiresB env "Step" 4 (.tuple [v₁, v₂])) :
    ∃ z z' n cs is is',
      v₁ = cfgV z [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is])] ∧
      v₂ = cfgV z' [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is'])] ∧
      SStepB env (cfgV z is) (cfgV z' is') := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (Reading.firesB_body h₀ (by rfl) hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := nT) hq (.tail _ (.head _))
  obtain ⟨cs, fc, -⟩ :=
    quant_list (x := "catch*") (t := .varT "catch" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨z', fz', -⟩ :=
    quant_of (x := "z'") (t := stateT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ec : EvalExp env _ (iterPat "catch" "catch*") (.list cs) := evalExp_iterPat (by decide) fc
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have hc : Value.tuple [v₁, v₂] =
      .tuple [cfgV z [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is])],
        cfgV z' [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz')
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei'))))))
  have hs : SStepB env (cfgV z is) (cfgV z' is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  exact ⟨z, z', n, cs, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

/-- What `Step/ctxt-frame` says, read back. -/
def CtxtFrameInvB (env : Env) (v₁ v₂ : Value) : Prop :=
  ∃ s s' f fr fr' n is is',
    v₁ = cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])] ∧
    v₂ = cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])] ∧
    SStepB env (cfgV (stV s fr) is) (cfgV (stV s' fr') is')

/-- `Step/ctxt-frame`, read back. -/
theorem inv_ctxtFrameB (h₀ : HasRuleAt env "Step" "%~>%" 5 ctxtFrameRule) {v₁ v₂ : Value}
    (hf : FiresB env "Step" 5 (.tuple [v₁, v₂])) : CtxtFrameInvB env v₁ v₂ := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (Reading.firesB_body h₀ (by rfl) hf)
  obtain ⟨s, fs, -⟩ := quant_of (x := "s") (t := storeT) hq (.head _)
  obtain ⟨f, ff, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := nT) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨fr, ffr, -⟩ :=
    quant_of (x := "f'") (t := frameT) hq (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  obtain ⟨s', fs', -⟩ := quant_of (x := "s'") (t := storeT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨fr', ffr', -⟩ := quant_of (x := "f''") (t := frameT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  have ei' : EvalExp env _ (iterPat "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have hc : Value.tuple [v₁, v₂] =
      .tuple [cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])],
        cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff)))
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff)))
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr') ei'))))))
  have hs : SStepB env (cfgV (stV s fr) is) (cfgV (stV s' fr') is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr)))
        ei))
      (evalExp_case (evalExp_tup2
        (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr'))) ei')))
  exact ⟨s, s', f, fr, fr', n, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
