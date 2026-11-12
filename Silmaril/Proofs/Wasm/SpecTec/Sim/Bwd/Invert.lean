module

public import Silmaril.Wasm.SpecTec.Sim.Bwd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Assembly

/-!
# Inverting the six structural rules of `Step`

`Step` rules 0–5 (`pure`, `read`, `ctxt-instrs`, `ctxt-label`, `ctxt-handler`, `ctxt-frame`) read
backwards, for arbitrary values. Each `inv_*` takes a firing of the rule (`Fires`) and returns the
shape of both sides and the premises. The method is the same in each: the quantifiers give the
values bound to the rule's variables (`quant_of`, `quant_list`); the conclusion is evaluated
*forwards* at those values (the lifting lemmas' evaluation facts) and compared with the given one
by `EvalExp.unique`; the `Step` premise is read back by `rulePrem_nil`. These are the
SpecTec-side halves of the base's `sstep_*` constructions (`Lift.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecStepRules
  (pureRule readRule ctxtInstrsRule ctxtLabelRule ctxtHandlerRule ctxtFrameRule)
open Silmaril.SpecTec.Equiv.Execution (iterPat valsPat evalExp_iterPat evalExp_valsPat)

variable {env : Env}

/-! ## Premises and quantifiers -/

/-- A `RulePr` premise without arguments, at a known instance, read back. -/
theorem rulePrem_nil {D : Interp} {els : Prop} {ρ : VarEnv} {x : IL.Id} {op : MixopS} {e : Exp}
    {w : Value} (h : PremW env D els ρ (.rulePr x [] op e)) (he : EvalExp env ρ e w) :
    D x op [] w := by
  cases h with
  | rulePr ha he' hd =>
    have e₁ := evalArgs_nil_iff.1 ha
    have e₂ := EvalExp.unique he' he
    subst e₁ e₂
    exact hd

/-- An `if` premise read back. -/
theorem ifPrem_true {D : Interp} {els : Prop} {ρ : VarEnv} {e : Exp} {w : Value}
    (h : PremW env D els ρ (.ifPr e)) (he : EvalExp env ρ e w) : w = .bool true := by
  cases h with
  | ifPr h' => exact EvalExp.unique he h'

/-- A relation with a rule fact has no parameters and is looked up as such. -/
theorem findRel_of_ruleAt {x : IL.Id} {op : MixopS} {k : Nat} {r : Rule}
    (h : HasRuleAt env x op k r) : ∃ t rules, env.findRel? x = some ([], op, t, rules) := by
  obtain ⟨ps, t, rules, hrel, hps, -⟩ := h
  exact ⟨t, rules, hps ▸ hrel⟩

/-- `cfgV` is injective. -/
theorem cfgV_inj {z z' : Value} {is is' : List Value} (h : cfgV z is = cfgV z' is') :
    z = z' ∧ is = is' := by
  simp only [cfgV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    and_true, true_and] at h
  exact h

/-- `stV` is injective. -/
theorem stV_inj {s f s' f' : Value} (h : stV s f = stV s' f') : s = s' ∧ f = f' := by
  simp only [stV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
    true_and] at h
  exact h

/-- The two sides of a pair. -/
theorem tuple2_inj {a b c d : Value} (h : Value.tuple [a, b] = .tuple [c, d]) : a = c ∧ b = d := by
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at h
  exact h

/-! ## `Step/pure` and `Step/read` -/

/-- `Step/pure`, read back: both sides share the state, and the code takes a `Step_pure` step. -/
theorem inv_pure (h₀ : HasRuleAt env "Step" "%~>%" 0 pureRule) {v₁ v₂ : Value}
    (hf : Fires env "Step" 0 (.tuple [v₁, v₂])) :
    ∃ z is js, v₁ = cfgV z is ∧ v₂ = cfgV z js ∧ SPure env is js := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (.tail _ (.head _))
  obtain ⟨js, fj, -⟩ :=
    quant_list (x := "instr'*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  have ei : EvalExp env _ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have ej : EvalExp env _ (iterPat "instr'" "instr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  have hc : Value.tuple [v₁, v₂] = .tuple [cfgV z is, cfgV z js] :=
    EvalExp.unique he (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz) ej)))
  have hd : SPure env is js := rulePrem_nil (hp _ (.head _)) (evalExp_tup2 ei ej)
  exact ⟨z, is, js, (tuple2_inj hc).1, (tuple2_inj hc).2, hd⟩

/-- `Step/read`, read back: both sides share the state, and the configuration takes a
`Step_read` step to the new code. -/
theorem inv_read (h₀ : HasRuleAt env "Step" "%~>%" 1 readRule) {v₁ v₂ : Value}
    (hf : Fires env "Step" 1 (.tuple [v₁, v₂])) :
    ∃ z is js, v₁ = cfgV z is ∧ v₂ = cfgV z js ∧ SRead env (cfgV z is) js := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
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
  have hd : SRead env (cfgV z is) js := rulePrem_nil (hp _ (.head _)) (evalExp_tup2 ez ej)
  exact ⟨z, is, js, (tuple2_inj hc).1, (tuple2_inj hc).2, hd⟩

/-! ## The four context rules -/

/-- What `Step/ctxt-instrs` says, read back. -/
def CtxtInstrsInv (env : Env) (v₁ v₂ : Value) : Prop :=
  ∃ z z' vs is is' rest, (∃ ρ, ValsOnly ρ ∧ HasTyp env ρ valsT (.list vs)) ∧
    (vs ≠ [] ∨ rest ≠ []) ∧ v₁ = cfgV z (vs ++ is ++ rest) ∧ v₂ = cfgV z' (vs ++ is' ++ rest) ∧
    SStep env (cfgV z is) (cfgV z' is')

/-- `Step/ctxt-instrs`, read back, for every split. -/
theorem inv_ctxtInstrs (h₀ : HasRuleAt env "Step" "%~>%" 2 ctxtInstrsRule) {v₁ v₂ : Value}
    (hf : Fires env "Step" 2 (.tuple [v₁, v₂])) : CtxtInstrsInv env v₁ v₂ := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
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
  have hs : SStep env (cfgV z is) (cfgV z' is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  have hb : Value.bool (decide (vs ≠ [] ∨ rest ≠ [])) = .bool true :=
    ifPrem_true (hp _ (.tail _ (.head _))) (evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er))
  have hne : vs ≠ [] ∨ rest ≠ [] := of_decide_eq_true (Value.bool.inj hb)
  have h₁ : v₁ = cfgV z (vs ++ is ++ rest) := by rw [List.append_assoc]; exact (tuple2_inj hc).1
  have h₂ : v₂ = cfgV z' (vs ++ is' ++ rest) := by rw [List.append_assoc]; exact (tuple2_inj hc).2
  exact ⟨z, z', vs, is, is', rest, ⟨_, valsOnly_bindVals σ, tv⟩, hne, h₁, h₂, hs⟩

/-- `Step/ctxt-label`, read back. -/
theorem inv_ctxtLabel (h₀ : HasRuleAt env "Step" "%~>%" 3 ctxtLabelRule) {v₁ v₂ : Value}
    (hf : Fires env "Step" 3 (.tuple [v₁, v₂])) :
    ∃ z z' n cont is is',
      v₁ = cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])] ∧
      v₂ = cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is') := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
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
  have hs : SStep env (cfgV z is) (cfgV z' is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  exact ⟨z, z', n, cont, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

/-- `Step/ctxt-handler`, read back. -/
theorem inv_ctxtHandler (h₀ : HasRuleAt env "Step" "%~>%" 4 ctxtHandlerRule) {v₁ v₂ : Value}
    (hf : Fires env "Step" 4 (.tuple [v₁, v₂])) :
    ∃ z z' n cs is is',
      v₁ = cfgV z [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is])] ∧
      v₂ = cfgV z' [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is') := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
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
  have hs : SStep env (cfgV z is) (cfgV z' is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  exact ⟨z, z', n, cs, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

/-- What `Step/ctxt-frame` says, read back. -/
def CtxtFrameInv (env : Env) (v₁ v₂ : Value) : Prop :=
  ∃ s s' f fr fr' n is is',
    v₁ = cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])] ∧
    v₂ = cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])] ∧
    SStep env (cfgV (stV s fr) is) (cfgV (stV s' fr') is')

/-- `Step/ctxt-frame`, read back. -/
theorem inv_ctxtFrame (h₀ : HasRuleAt env "Step" "%~>%" 5 ctxtFrameRule) {v₁ v₂ : Value}
    (hf : Fires env "Step" 5 (.tuple [v₁, v₂])) : CtxtFrameInv env v₁ v₂ := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
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
  have hs : SStep env (cfgV (stV s fr) is) (cfgV (stV s' fr') is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr)))
        ei))
      (evalExp_case (evalExp_tup2
        (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr'))) ei')))
  exact ⟨s, s', f, fr, fr', n, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

end Silmaril.Wasm.SpecTec.Sim.Bwd
