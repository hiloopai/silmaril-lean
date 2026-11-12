module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.CastsFwd

/-!
# Round 6: context lifting under `DDerivesB`

`Sim/Lift.lean`'s `Step/pure`, `Step/ctxt-instrs`, `ctxt-label`, `ctxt-handler` and `ctxt-frame`
(with `Step/read` in `CastsFwd.lean`), copied for the new reading: each builds an `SStepB` step
from an `SStepB` (or `SPureB`) premise. The rules' conclusions have no empty-domain option
iteration, so each is its own only alternative; the proofs are otherwise unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Reading

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecStepRules
  (pureRule readRule ctxtInstrsRule ctxtLabelRule ctxtHandlerRule ctxtFrameRule)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat evalExp_valsPat)

/-- Two premises, under the new reading. -/
theorem premsB_two {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr₁ pr₂ : Prem}
    (h₁ : DPremB env O els ρ pr₁) (h₂ : DPremB env O els ρ pr₂) :
    ∀ p ∈ [pr₁, pr₂], DPremB env O els ρ p := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h₁
  · rw [List.mem_singleton.1 hp]
    exact h₂

/-- `Step/pure`: a `Step_pure` step is a `Step` step under the new reading at any state. -/
theorem sstepB_pure {env : Env} (h : HasRuleAt env "Step" "%~>%" 0 pureRule) {z : Value}
    {is js : List Value} (hz : TypedV env stateT z) (his : TypedV env instrsT (.list is))
    (hjs : TypedV env instrsT (.list js)) (hp : SPureB env is js) :
    SStepB env (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("instr*", .list is), ("instr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fj : ρ.findVal? "instr'*" = some (.list js) := rfl
  have hq : QuantsOk env ρ [.expP "z" stateT, .expP "instr*" instrsT, .expP "instr'*" instrsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list is) := evalExp_iterPat (by decide) fi
  have ej : EvalExp env ρ (.iterE (.varE "instr'") (.mk .list [.mk "instr'" (.varE "instr'*")]))
      (.list js) := evalExp_iterPat (by decide) fj
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) _ hq
    (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ej)))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 ei ej) hp))

/-- `Step/ctxt-instrs`: a step under a value prefix `vs` and an instruction suffix `rest`, not
both empty, for **every** split. -/
theorem sstepB_ctxtInstrs {env : Env} (h : HasRuleAt env "Step" "%~>%" 2 ctxtInstrsRule)
    {z z' : Value} {vs is is' rest : List Value} (hz : TypedV env stateT z)
    (hz' : TypedV env stateT z') (hvs : TypedV env valsT (.list vs))
    (his : TypedV env instrsT (.list is)) (his' : TypedV env instrsT (.list is'))
    (hrest : TypedV env instrsT (.list rest)) (hne : vs ≠ [] ∨ rest ≠ [])
    (hs : SStepB env (cfgV z is) (cfgV z' is')) :
    SStepB env (cfgV z (vs ++ is ++ rest)) (cfgV z' (vs ++ is' ++ rest)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("val*", .list vs), ("instr*", .list is),
    ("instr_1*", .list rest), ("z'", z'), ("instr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fv : ρ.findVal? "val*" = some (.list vs) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fr : ρ.findVal? "instr_1*" = some (.list rest) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "instr'*" = some (.list is') := rfl
  have hq : QuantsOk env ρ [.expP "z" stateT, .expP "val*" valsT, .expP "instr*" instrsT,
      .expP "instr_1*" instrsT, .expP "z'" stateT, .expP "instr'*" instrsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons fr (hrest ρ hρ)
      (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ev : EvalExp env ρ (Equiv.Execution.valsPat "val" "val*") (.list vs) :=
    evalExp_valsPat (by decide) fv
  have ev' : EvalExp env ρ (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")]))
      (.list vs) := evalExp_iterPat (by decide) fv
  have ei : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env ρ (.iterE (.varE "instr'") (.mk .list [.mk "instr'" (.varE "instr'*")]))
      (.list is') := evalExp_iterPat (by decide) fi'
  have er : EvalExp env ρ
      (.iterE (.varE "instr_1") (.mk .list [.mk "instr_1" (.varE "instr_1*")])) (.list rest) :=
    evalExp_iterPat (by decide) fr
  have hor : EvalExp env ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")])) (.listE []))
      (.cmpE .neOp .boolT
        (.iterE (.varE "instr_1") (.mk .list [.mk "instr_1" (.varE "instr_1*")])) (.listE [])))
      (.bool (decide (vs ≠ [] ∨ rest ≠ []))) :=
    evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er)
  have hd : decide (vs ≠ [] ∨ rest ≠ []) = true := decide_eq_true hne
  have hg : SStepB env (cfgV z (vs ++ (is ++ rest))) (cfgV z' (vs ++ (is' ++ rest))) :=
    dderivesB_of_ruleAt h (self_mem_conclAlts _) _ hq
      (evalExp_tup2
        (evalExp_case (op := "%;%")
          (evalExp_tup2 (evalExp_var fz) (evalExp_cat ev (evalExp_cat ei er))))
        (evalExp_case (op := "%;%")
          (evalExp_tup2 (evalExp_var fz') (evalExp_cat ev (evalExp_cat ei' er)))))
      (premsB_two
        (.rulePr (evalArgs_nil _ _)
          (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
            (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs)
        (.ifPr (hd ▸ hor)))
  simpa only [List.append_assoc] using hg

/-- `Step/ctxt-label`: a step under `LABEL_n{cont}`. -/
theorem sstepB_ctxtLabel {env : Env} (h : HasRuleAt env "Step" "%~>%" 3 ctxtLabelRule)
    {z z' n : Value} {cont is is' : List Value} (hz : TypedV env stateT z)
    (hz' : TypedV env stateT z') (hn : TypedV env nT n) (hc : TypedV env instrsT (.list cont))
    (his : TypedV env instrsT (.list is)) (his' : TypedV env instrsT (.list is'))
    (hs : SStepB env (cfgV z is) (cfgV z' is')) :
    SStepB env (cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])])
      (cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", n), ("instr_0*", .list cont),
    ("instr*", .list is), ("z'", z'), ("instr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "instr_0*" = some (.list cont) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "instr'*" = some (.list is') := rfl
  have hq : QuantsOk env ρ [.expP "z" stateT, .expP "n" nT, .expP "instr_0*" instrsT,
      .expP "instr*" instrsT, .expP "z'" stateT, .expP "instr'*" instrsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ec : EvalExp env ρ
      (.iterE (.varE "instr_0") (.mk .list [.mk "instr_0" (.varE "instr_0*")])) (.list cont) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env ρ (.iterE (.varE "instr'") (.mk .list [.mk "instr'" (.varE "instr'*")]))
      (.list is') := evalExp_iterPat (by decide) fi'
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei'))))))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs))

/-- `Step/ctxt-handler`: a step under `HANDLER_n{catch*}`. -/
theorem sstepB_ctxtHandler {env : Env} (h : HasRuleAt env "Step" "%~>%" 4 ctxtHandlerRule)
    {z z' n : Value} {cs is is' : List Value} (hz : TypedV env stateT z)
    (hz' : TypedV env stateT z') (hn : TypedV env nT n) (hc : TypedV env catchesT (.list cs))
    (his : TypedV env instrsT (.list is)) (his' : TypedV env instrsT (.list is'))
    (hs : SStepB env (cfgV z is) (cfgV z' is')) :
    SStepB env (cfgV z [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is])])
      (cfgV z' [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is'])]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", n), ("catch*", .list cs),
    ("instr*", .list is), ("z'", z'), ("instr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "catch*" = some (.list cs) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "instr'*" = some (.list is') := rfl
  have hq : QuantsOk env ρ [.expP "z" stateT, .expP "n" nT, .expP "catch*" catchesT,
      .expP "instr*" instrsT, .expP "z'" stateT, .expP "instr'*" instrsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ec : EvalExp env ρ
      (.iterE (.varE "catch") (.mk .list [.mk "catch" (.varE "catch*")])) (.list cs) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env ρ (.iterE (.varE "instr'") (.mk .list [.mk "instr'" (.varE "instr'*")]))
      (.list is') := evalExp_iterPat (by decide) fi'
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) (evalExp_list1
        (evalExp_case (op := "HANDLER_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') (evalExp_list1
        (evalExp_case (op := "HANDLER_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei'))))))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs))

/-- `Step/ctxt-frame`: a step under `FRAME_n{f}`, run in the frame `f` and leaving the outer
frame alone. -/
theorem sstepB_ctxtFrame {env : Env} (h : HasRuleAt env "Step" "%~>%" 5 ctxtFrameRule)
    {s s' f fr fr' n : Value} {is is' : List Value} (hs₁ : TypedV env storeT s)
    (hs₂ : TypedV env storeT s') (hf : TypedV env frameT f) (hfr : TypedV env frameT fr)
    (hfr' : TypedV env frameT fr') (hn : TypedV env nT n)
    (his : TypedV env instrsT (.list is)) (his' : TypedV env instrsT (.list is'))
    (hst : SStepB env (cfgV (stV s fr) is) (cfgV (stV s' fr') is')) :
    SStepB env (cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])])
      (cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])]) := by
  let ρ := VarEnv.empty.bindVals [("s", s), ("f", f), ("n", n), ("f'", fr), ("instr*", .list is),
    ("s'", s'), ("f''", fr'), ("instr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fs : ρ.findVal? "s" = some s := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fn : ρ.findVal? "n" = some n := rfl
  have ffr : ρ.findVal? "f'" = some fr := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fs' : ρ.findVal? "s'" = some s' := rfl
  have ffr' : ρ.findVal? "f''" = some fr' := rfl
  have fi' : ρ.findVal? "instr'*" = some (.list is') := rfl
  have hq : QuantsOk env ρ [.expP "s" storeT, .expP "f" frameT, .expP "n" nT, .expP "f'" frameT,
      .expP "instr*" instrsT, .expP "s'" storeT, .expP "f''" frameT, .expP "instr'*" instrsT] :=
    QuantsOk.cons fs (hs₁ ρ hρ)
      (QuantsOk.cons ff (hf ρ hρ)
      (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons ffr (hfr ρ hρ)
      (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons fs' (hs₂ ρ hρ)
      (QuantsOk.cons ffr' (hfr' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))))
  have ei : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list is) := evalExp_iterPat (by decide) fi
  have ei' : EvalExp env ρ (.iterE (.varE "instr'") (.mk .list [.mk "instr'" (.varE "instr'*")]))
      (.list is') := evalExp_iterPat (by decide) fi'
  have est : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "s", .varE "f"])) (stV s f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff))
  have est' : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "s'", .varE "f"])) (stV s' f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff))
  have ein : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "s", .varE "f'"])) (stV s fr) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr))
  have ein' : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "s'", .varE "f''"])) (stV s' fr') :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr'))
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 est (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%") (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 est' (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%")
          (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr') ei'))))))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 ein ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 ein' ei'))) hst))

end Silmaril.Wasm.SpecTec.Sim.Round6.Reading
