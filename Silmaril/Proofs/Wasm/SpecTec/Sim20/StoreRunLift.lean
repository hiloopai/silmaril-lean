module

public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Thms

/-!
# The corrected `Step` in `simEnv20T`: `read`, `ctxt-label` and `ctxt-frame`

An earlier step lifted steps of `simEnv20T` through `ctxt-instrs` only (`StoreFix.sstepT_ctxtInstrs`). The
`STORE` errata leave `Step` unchanged, so its rules 0, 1, 3 and 4 are `StepFix.pureFix`, `readFix`,
`ctxtLabelFix` and `ctxtFrameFix` in `simEnv20T` too (`hasRuleAt_*FixT`, by `rfl`), and the
proofs of `StepFix.sstepS_read`, `sstepS_ctxtLabel` and `sstepS_ctxtFrame` go through at
`simEnv20T` with every quantified value typed there:

* `sstepT_read`: a `Step_read` step from `z; instr*` is a `Step` step that keeps `z`;
* **`sstepT_ctxtLabel`**: a step of `z; instr*` lifts under `LABEL_ n {instr_0*}`;
* **`sstepT_ctxtFrame`**: a step of `s; f'; instr*` to `s'; f''; instr'*` lifts under
  `FRAME_ n {f'}` at any outer frame `f`;
* `sstepT_pure`: a `Step_pure` step is a `Step` step at any state.

With `ElseAgree.elseAgree20T` these give the `Step_read` and `Step_pure` analogues of
`StoreAgree.sstepB20T_of_fires20`: every firing of a `Step_read` (`Step_pure`) rule of the 2.0
script, at a state and codes typed in `simEnv20T`, is a step of `simEnv20T`
(`sstepB20T_of_firesRead20`, `sstepB20T_of_firesPure20`).

Unlike in `simEnv20S`, the continuation `instr_0*` and the bodies may contain scalar stores.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreRun

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk SStep SRead cfgV stV TypedV ValsOnly stateT storeT frameT nT
  instrsT dderives_of_ruleAt evalExp_tup2 evalExp_tup3 evalExp_case evalExp_list1
  prems_one)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (readFix ctxtLabelFix ctxtFrameFix adminsTy iterV cfgE stE)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

set_option maxRecDepth 100000

variable (B : Builtins)

theorem hasRuleAt_pureFixT : HasRuleAt (simEnv20T B) "Step" "%~>%" 0 StepFix.pureFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_readFixT : HasRuleAt (simEnv20T B) "Step" "%~>%" 1 readFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_ctxtLabelFixT : HasRuleAt (simEnv20T B) "Step" "%~>%" 3 ctxtLabelFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_ctxtFrameFixT : HasRuleAt (simEnv20T B) "Step" "%~>%" 4 ctxtFrameFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable {B}

/-- **`Step/pure`** in `simEnv20T`: a `Step_pure` step between `admininstr*` sequences is a `Step`
step at any state. (The proof of `StepFix.sstepS_pure`, at `simEnv20T`.) -/
theorem sstepT_pure {z : Value} {is js : List Value} (hz : TypedV (simEnv20T B) stateT z)
    (his : TypedV (simEnv20T B) adminsTy (.list is)) (hjs : TypedV (simEnv20T B) adminsTy (.list js))
    (hp : Sim.SPure (simEnv20T B) is js) : SStep (simEnv20T B) (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("instr*", .list is), ("instr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fj : ρ.findVal? "instr'*" = some (.list js) := rfl
  have hq : QuantsOk (simEnv20T B) ρ
      [.expP "z" stateT, .expP "instr*" adminsTy, .expP "instr'*" adminsTy] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp (simEnv20T B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp (simEnv20T B) ρ (iterV "instr'" "instr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  exact dderives_of_ruleAt (hasRuleAt_pureFixT B) _ hq
    (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ej)))
    (prems_one (.rulePr Equiv.evalArgs_nil (evalExp_tup2 ei ej) hp))

/-- **`Step/read`** of the corrected script: a `Step_read` step from `z; instr*` is a `Step` step
that keeps the state. (The proof of `StepFix.sstepS_read`, at `simEnv20T`.) -/
theorem sstepT_read {z : Value} {is js : List Value} (hz : TypedV (simEnv20T B) stateT z)
    (his : TypedV (simEnv20T B) adminsTy (.list is)) (hjs : TypedV (simEnv20T B) adminsTy (.list js))
    (hp : SRead (simEnv20T B) (cfgV z is) js) : SStep (simEnv20T B) (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("instr*", .list is), ("instr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fj : ρ.findVal? "instr'*" = some (.list js) := rfl
  have hq : QuantsOk (simEnv20T B) ρ
      [.expP "z" stateT, .expP "instr*" adminsTy, .expP "instr'*" adminsTy] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp (simEnv20T B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp (simEnv20T B) ρ (iterV "instr'" "instr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  have ec : EvalExp (simEnv20T B) ρ (cfgE (.varE "z") (iterV "instr" "instr*")) (cfgV z is) :=
    evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei)
  exact dderives_of_ruleAt (hasRuleAt_readFixT B) _ hq
    (evalExp_tup2 ec (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ej)))
    (prems_one (.rulePr Equiv.evalArgs_nil (evalExp_tup2 ec ej) hp))

/-- **`Step/ctxt-label`** of the corrected script: a step of `z; instr*` lifts under
`LABEL_ n {instr_0*}`. (The proof of `StepFix.sstepS_ctxtLabel`, at `simEnv20T`.) -/
theorem sstepT_ctxtLabel {z z' n : Value} {cont is is' : List Value}
    (hz : TypedV (simEnv20T B) stateT z) (hz' : TypedV (simEnv20T B) stateT z')
    (hn : TypedV (simEnv20T B) nT n) (hc : TypedV (simEnv20T B) instrsT (.list cont))
    (his : TypedV (simEnv20T B) adminsTy (.list is))
    (his' : TypedV (simEnv20T B) adminsTy (.list is'))
    (hs : SStep (simEnv20T B) (cfgV z is) (cfgV z' is')) :
    SStep (simEnv20T B) (cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])])
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
  have hq : QuantsOk (simEnv20T B) ρ [.expP "z" stateT, .expP "n" nT, .expP "instr_0*" instrsT,
      .expP "instr*" adminsTy, .expP "z'" stateT, .expP "instr'*" adminsTy] :=
    QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ec : EvalExp (simEnv20T B) ρ (iterV "instr_0" "instr_0*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp (simEnv20T B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv20T B) ρ (iterV "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  exact dderives_of_ruleAt (hasRuleAt_ctxtLabelFixT B) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei'))))))
    (prems_one (.rulePr Equiv.evalArgs_nil
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs))

/-- **`Step/ctxt-frame`** of the corrected script: a step of `s; f'; instr*` to
`s'; f''; instr'*` lifts under `FRAME_ n {f'}` at any outer frame `f`. (The proof of
`StepFix.sstepS_ctxtFrame`, at `simEnv20T`.) -/
theorem sstepT_ctxtFrame {s s' f fr fr' n : Value} {is is' : List Value}
    (hs₁ : TypedV (simEnv20T B) storeT s) (hs₂ : TypedV (simEnv20T B) storeT s')
    (hf : TypedV (simEnv20T B) frameT f) (hfr : TypedV (simEnv20T B) frameT fr)
    (hfr' : TypedV (simEnv20T B) frameT fr') (hn : TypedV (simEnv20T B) nT n)
    (his : TypedV (simEnv20T B) adminsTy (.list is))
    (his' : TypedV (simEnv20T B) adminsTy (.list is'))
    (hst : SStep (simEnv20T B) (cfgV (stV s fr) is) (cfgV (stV s' fr') is')) :
    SStep (simEnv20T B) (cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])])
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
  have hq : QuantsOk (simEnv20T B) ρ [.expP "s" storeT, .expP "f" frameT, .expP "n" nT,
      .expP "f'" frameT, .expP "instr*" adminsTy, .expP "s'" storeT, .expP "f''" frameT,
      .expP "instr'*" adminsTy] :=
    QuantsOk.cons fs (hs₁ ρ hρ) (QuantsOk.cons ff (hf ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons ffr (hfr ρ hρ) (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fs' (hs₂ ρ hρ)
      (QuantsOk.cons ffr' (hfr' ρ hρ) (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))))
  have ei : EvalExp (simEnv20T B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv20T B) ρ (iterV "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have est : EvalExp (simEnv20T B) ρ (stE (.varE "s") (.varE "f")) (stV s f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff))
  have est' : EvalExp (simEnv20T B) ρ (stE (.varE "s'") (.varE "f")) (stV s' f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff))
  have ein : EvalExp (simEnv20T B) ρ (stE (.varE "s") (.varE "f'")) (stV s fr) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr))
  have ein' : EvalExp (simEnv20T B) ρ (stE (.varE "s'") (.varE "f''")) (stV s' fr') :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr'))
  exact dderives_of_ruleAt (hasRuleAt_ctxtFrameFixT B) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 est (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%") (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 est' (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%")
          (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr') ei'))))))
    (prems_one (.rulePr Equiv.evalArgs_nil
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 ein ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 ein' ei'))) hst))

/-! ## `Step_pure` and `Step_read` firings of the 2.0 script, at `simEnv20T` -/

/-- **A `Step_read` firing of the 2.0 script is a step of `simEnv20T`**, from a state and codes
typed there. The route is `simEnv20 → simEnv20S` (`RelFree.sread20S_iff`), then
`simEnv20S → simEnv20T` (`StoreAgree.dderives_of` with `ElseAgree.elseAgree20T`), then
`Step/read` (`sstepT_read`). -/
theorem sstepB20T_of_firesRead20 {k : Nat} {z : Value} {is js : List Value}
    (hz : TypedV (simEnv20T B) stateT z) (his : TypedV (simEnv20T B) adminsTy (.list is))
    (hjs : TypedV (simEnv20T B) adminsTy (.list js))
    (h : Sim.Fires (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) "Step_read" k (.tuple [cfgV z is, .list js])) :
    SStepB (simEnv20T B) (cfgV z is) (cfgV z js) := by
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B).findRel? "Step_read" = some ([], "%~>%", t, rules) :=
    ⟨_, _, rfl⟩
  have h₀ : SRead (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) (cfgV z is) js :=
    (Sim.dderives_iff_fires hrel).2 ⟨k, h⟩
  have h₁ : SRead (StepFix.simEnv20S B) (cfgV z is) js := (RelFree.sread20S_iff B _ _).2 h₀
  have h₂ : SRead (simEnv20T B) (cfgV z is) js :=
    StoreAgree.dderives_of (StoreAgree.envSame20T B) (StoreAgree.typRepair20T B)
      (ElseAgree.elseAgree20T B) h₁
  exact (StoreFix.sstepB20T_iff B).2 (sstepT_read hz his hjs h₂)

/-- **A `Step_pure` firing of the 2.0 script is a step of `simEnv20T`** at any state typed there. -/
theorem sstepB20T_of_firesPure20 {k : Nat} {z : Value} {is js : List Value}
    (hz : TypedV (simEnv20T B) stateT z) (his : TypedV (simEnv20T B) adminsTy (.list is))
    (hjs : TypedV (simEnv20T B) adminsTy (.list js))
    (h : Sim.Fires (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) "Step_pure" k (.tuple [.list is, .list js])) :
    SStepB (simEnv20T B) (cfgV z is) (cfgV z js) := by
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B).findRel? "Step_pure" = some ([], "%~>%", t, rules) :=
    ⟨_, _, rfl⟩
  have h₀ : Sim.SPure (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) is js :=
    (Sim.dderives_iff_fires hrel).2 ⟨k, h⟩
  have h₁ : Sim.SPure (StepFix.simEnv20S B) is js := (RelFree.spure20S_iff B _ _).2 h₀
  have h₂ : Sim.SPure (simEnv20T B) is js :=
    StoreAgree.dderives_of (StoreAgree.envSame20T B) (StoreAgree.typRepair20T B)
      (ElseAgree.elseAgree20T B) h₁
  exact (StoreFix.sstepB20T_iff B).2 (sstepT_pure hz his hjs h₂)

end Silmaril.Wasm.SpecTec.Sim20.StoreRun
