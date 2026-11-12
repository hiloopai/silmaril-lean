module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.WholeBwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StepFixRun

/-!
# The 1.0 script forward: the five structural rules lift steps

The wasm-1.0 script needs no erratum for the forward half. Its `Step` already has the five
structural rules that pass 7's `stepErratum20` gives 2.0 (`Sim20.StepFix`): `pure` and `read` at
`admininstr*`, `ctxt-label`, `ctxt-frame` with a successor inner frame, and `ctxt-instrs`. This
module builds derivations with them in `simEnv10 B`, mirroring `Sim20.StepFix.sstepS_*`:

* `sstep10_pure`, `sstep10_read`: a `Step_pure` (`Step_read`) step between `admininstr*` sequences
  is a `Step` step that keeps the state;
* `sstep10_ctxtInstrs`: a step lifts under a `val*` prefix and an `admininstr*` suffix, not both
  empty;
* `sstep10_ctxtLabel`: a step lifts under `LABEL_ n {instr_0*}`;
* `sstep10_ctxtFrame`: a step of `s; f'; instr*` to `s'; f''; instr'*` lifts under `FRAME_ n {f'}`
  at any outer frame `f`.

Each needs every quantified value IL-typed in `simEnv10 B`; the typing is a hypothesis here.
`FwdNest` reads it off the typing of the configurations.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat iterPat)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk SStep SRead SPure cfgV stV TypedV ValsOnly stateT storeT
  frameT nT instrsT dderives_of_ruleAt evalExp_tup2 evalExp_tup3 evalExp_case evalExp_list1
  evalExp_cat evalExp_ne_nil evalExp_or prems_one prems_two)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat)

set_option maxRecDepth 100000

variable {B : Builtins}

/-- `val*`, the type of the value prefix of `ctxt-instrs`. -/
abbrev valsTy10 : Typ := .iterT (.varT "val" []) .list

/-- **`Step/pure`** of the 1.0 script: a `Step_pure` step between `admininstr*` sequences is a
`Step` step at any state. -/
theorem sstep10_pure {z : Value} {is js : List Value} (hz : TypedV (simEnv10 B) stateT z)
    (his : TypedV (simEnv10 B) adminsT (.list is)) (hjs : TypedV (simEnv10 B) adminsT (.list js))
    (hp : SPure (simEnv10 B) is js) : SStep (simEnv10 B) (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("admininstr*", .list is), ("admininstr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fj : ρ.findVal? "admininstr'*" = some (.list js) := rfl
  have hq : QuantsOk (simEnv10 B) ρ
      [.expP "z" stateT, .expP "admininstr*" adminsT, .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp (simEnv10 B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp (simEnv10 B) ρ (iterPat "admininstr'" "admininstr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  exact dderives_of_ruleAt (hasRuleAt_pure10 B) _ hq
    (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ej)))
    (prems_one (.rulePr Equiv.evalArgs_nil (evalExp_tup2 ei ej) hp))

/-- **`Step/read`** of the 1.0 script: a `Step_read` step from `z; admininstr*` is a `Step` step
that keeps the state. -/
theorem sstep10_read {z : Value} {is js : List Value} (hz : TypedV (simEnv10 B) stateT z)
    (his : TypedV (simEnv10 B) adminsT (.list is)) (hjs : TypedV (simEnv10 B) adminsT (.list js))
    (hp : SRead (simEnv10 B) (cfgV z is) js) : SStep (simEnv10 B) (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("admininstr*", .list is), ("admininstr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fj : ρ.findVal? "admininstr'*" = some (.list js) := rfl
  have hq : QuantsOk (simEnv10 B) ρ
      [.expP "z" stateT, .expP "admininstr*" adminsT, .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp (simEnv10 B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp (simEnv10 B) ρ (iterPat "admininstr'" "admininstr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  have ec : EvalExp (simEnv10 B) ρ (cfgE (.varE "z") (iterPat "admininstr" "admininstr*"))
      (cfgV z is) :=
    evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei)
  exact dderives_of_ruleAt (hasRuleAt_read10 B) _ hq
    (evalExp_tup2 ec (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ej)))
    (prems_one (.rulePr Equiv.evalArgs_nil (evalExp_tup2 ec ej) hp))

/-- **`Step/ctxt-instrs`** of the 1.0 script: a step under a value prefix `vs` and a suffix
`rest`, not both empty. -/
theorem sstep10_ctxtInstrs {z z' : Value} {vs is is' rest : List Value}
    (hz : TypedV (simEnv10 B) stateT z) (hz' : TypedV (simEnv10 B) stateT z')
    (hvs : TypedV (simEnv10 B) valsTy10 (.list vs)) (his : TypedV (simEnv10 B) adminsT (.list is))
    (his' : TypedV (simEnv10 B) adminsT (.list is'))
    (hrest : TypedV (simEnv10 B) adminsT (.list rest)) (hne : vs ≠ [] ∨ rest ≠ [])
    (hs : SStep (simEnv10 B) (cfgV z is) (cfgV z' is')) :
    SStep (simEnv10 B) (cfgV z (vs ++ is ++ rest)) (cfgV z' (vs ++ is' ++ rest)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("val*", .list vs), ("admininstr*", .list is),
    ("admininstr_1*", .list rest), ("z'", z'), ("admininstr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fv : ρ.findVal? "val*" = some (.list vs) := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fr : ρ.findVal? "admininstr_1*" = some (.list rest) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "admininstr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv10 B) ρ [.expP "z" stateT, .expP "val*" valsTy10,
      .expP "admininstr*" adminsT, .expP "admininstr_1*" adminsT, .expP "z'" stateT,
      .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons fr (hrest ρ hρ)
      (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ev : EvalExp (simEnv10 B) ρ valsE10 (.list vs) := evalExp_subIterPat (by decide) fv
  have ev' : EvalExp (simEnv10 B) ρ (iterPat "val" "val*") (.list vs) :=
    evalExp_iterPat (by decide) fv
  have ei : EvalExp (simEnv10 B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv10 B) ρ (iterPat "admininstr'" "admininstr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have er : EvalExp (simEnv10 B) ρ (iterPat "admininstr_1" "admininstr_1*") (.list rest) :=
    evalExp_iterPat (by decide) fr
  have hor : EvalExp (simEnv10 B) ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterPat "admininstr_1" "admininstr_1*") (.listE [])))
      (.bool (decide (vs ≠ [] ∨ rest ≠ []))) :=
    evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er)
  have hd : decide (vs ≠ [] ∨ rest ≠ []) = true := decide_eq_true hne
  have hg : SStep (simEnv10 B) (cfgV z (vs ++ (is ++ rest))) (cfgV z' (vs ++ (is' ++ rest))) :=
    dderives_of_ruleAt (hasRuleAt_ctxtInstrs10 B) _ hq
      (evalExp_tup2
        (evalExp_case (op := "%;%")
          (evalExp_tup2 (evalExp_var fz) (evalExp_cat ev (evalExp_cat ei er))))
        (evalExp_case (op := "%;%")
          (evalExp_tup2 (evalExp_var fz') (evalExp_cat ev (evalExp_cat ei' er)))))
      (prems_two
        (.rulePr Equiv.evalArgs_nil
          (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
            (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs)
        (.ifPr (hd ▸ hor)))
  simpa only [List.append_assoc] using hg

/-- **`Step/ctxt-label`** of the 1.0 script: a step of `z; admininstr*` lifts under
`LABEL_ n {instr_0*}`. -/
theorem sstep10_ctxtLabel {z z' n : Value} {cont is is' : List Value}
    (hz : TypedV (simEnv10 B) stateT z) (hz' : TypedV (simEnv10 B) stateT z')
    (hn : TypedV (simEnv10 B) nT n) (hc : TypedV (simEnv10 B) instrsT (.list cont))
    (his : TypedV (simEnv10 B) adminsT (.list is))
    (his' : TypedV (simEnv10 B) adminsT (.list is'))
    (hs : SStep (simEnv10 B) (cfgV z is) (cfgV z' is')) :
    SStep (simEnv10 B) (cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])])
      (cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", n), ("instr_0*", .list cont),
    ("admininstr*", .list is), ("z'", z'), ("admininstr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "instr_0*" = some (.list cont) := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "admininstr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv10 B) ρ [.expP "z" stateT, .expP "n" nT, .expP "instr_0*" instrsT,
      .expP "admininstr*" adminsT, .expP "z'" stateT, .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ec : EvalExp (simEnv10 B) ρ (iterPat "instr_0" "instr_0*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp (simEnv10 B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv10 B) ρ (iterPat "admininstr'" "admininstr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  exact dderives_of_ruleAt (hasRuleAt_ctxtLabel10 B) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei'))))))
    (prems_one (.rulePr Equiv.evalArgs_nil
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs))

/-- **`Step/ctxt-frame`** of the 1.0 script: a step of `s; f'; admininstr*` to
`s'; f''; admininstr'*` lifts under `FRAME_ n {f'}` at any outer frame `f`. -/
theorem sstep10_ctxtFrame {s s' f fr fr' n : Value} {is is' : List Value}
    (hs₁ : TypedV (simEnv10 B) storeT s) (hs₂ : TypedV (simEnv10 B) storeT s')
    (hf : TypedV (simEnv10 B) frameT f) (hfr : TypedV (simEnv10 B) frameT fr)
    (hfr' : TypedV (simEnv10 B) frameT fr') (hn : TypedV (simEnv10 B) nT n)
    (his : TypedV (simEnv10 B) adminsT (.list is))
    (his' : TypedV (simEnv10 B) adminsT (.list is'))
    (hst : SStep (simEnv10 B) (cfgV (stV s fr) is) (cfgV (stV s' fr') is')) :
    SStep (simEnv10 B) (cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])])
      (cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])]) := by
  let ρ := VarEnv.empty.bindVals [("s", s), ("f", f), ("n", n), ("f'", fr),
    ("admininstr*", .list is), ("s'", s'), ("f''", fr'), ("admininstr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fs : ρ.findVal? "s" = some s := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fn : ρ.findVal? "n" = some n := rfl
  have ffr : ρ.findVal? "f'" = some fr := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fs' : ρ.findVal? "s'" = some s' := rfl
  have ffr' : ρ.findVal? "f''" = some fr' := rfl
  have fi' : ρ.findVal? "admininstr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv10 B) ρ [.expP "s" storeT, .expP "f" frameT, .expP "n" nT,
      .expP "f'" frameT, .expP "admininstr*" adminsT, .expP "s'" storeT, .expP "f''" frameT,
      .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fs (hs₁ ρ hρ) (QuantsOk.cons ff (hf ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons ffr (hfr ρ hρ) (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fs' (hs₂ ρ hρ)
      (QuantsOk.cons ffr' (hfr' ρ hρ) (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))))
  have ei : EvalExp (simEnv10 B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv10 B) ρ (iterPat "admininstr'" "admininstr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have est : EvalExp (simEnv10 B) ρ (stE (.varE "s") (.varE "f")) (stV s f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff))
  have est' : EvalExp (simEnv10 B) ρ (stE (.varE "s'") (.varE "f")) (stV s' f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff))
  have ein : EvalExp (simEnv10 B) ρ (stE (.varE "s") (.varE "f'")) (stV s fr) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr))
  have ein' : EvalExp (simEnv10 B) ρ (stE (.varE "s'") (.varE "f''")) (stV s' fr') :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr'))
  exact dderives_of_ruleAt (hasRuleAt_ctxtFrame10 B) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 est (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%") (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 est' (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%")
          (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr') ei'))))))
    (prems_one (.rulePr Equiv.evalArgs_nil
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 ein ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 ein' ei'))) hst))

end Silmaril.Wasm.SpecTec.Sim10.Whole
