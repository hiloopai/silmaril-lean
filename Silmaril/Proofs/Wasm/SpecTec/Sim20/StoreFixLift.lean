module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixTyped

/-!
# The corrected `Step` in `simEnv20T`: `ctxt-instrs`

* `hasRuleAt_ctxtInstrsFixT`, `hasRuleAt_storeNumTrapT`: the `STORE` errata leave `Step`
  unchanged, so `ctxt-instrs` is rule 2 and `store-num-trap` rule 12, as in `simEnv20S`;
* `sstepT_ctxtInstrs`: `Step/ctxt-instrs` lifts steps in `simEnv20T` (the proof of
  `StepFix.sstepS_ctxtInstrs`, at the other environment).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat pctV)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk DDerives otherwise Fires PremW SStep cfgV TypedV
  ValsOnly stateT dderives_iff_fires dderives_of_ruleAt evalExp_tup2 evalExp_case
  evalExp_cat evalExp_ne_nil evalExp_or prems_two)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB closedB Closed closed_of_closedB closed_congr
  dderivesB_otherwise_iff_of_closed)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S ctxtInstrsFix valsTy adminsTy valsE iterV)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat storeNumTrapRule)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## The corrected `Step` in `simEnv20T` -/

theorem hasRuleAt_ctxtInstrsFixT : HasRuleAt (simEnv20T B) "Step" "%~>%" 2 ctxtInstrsFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_storeNumTrapT : HasRuleAt (simEnv20T B) "Step" "%~>%" 12 storeNumTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable {B}

/-- **`Step/ctxt-instrs`** in `simEnv20T` (the proof of `StepFix.sstepS_ctxtInstrs`). -/
theorem sstepT_ctxtInstrs {z z' : Value} {vs is is' rest : List Value}
    (hz : TypedV (simEnv20T B) stateT z) (hz' : TypedV (simEnv20T B) stateT z')
    (hvs : TypedV (simEnv20T B) valsTy (.list vs)) (his : TypedV (simEnv20T B) adminsTy (.list is))
    (his' : TypedV (simEnv20T B) adminsTy (.list is'))
    (hrest : TypedV (simEnv20T B) adminsTy (.list rest)) (hne : vs ≠ [] ∨ rest ≠ [])
    (hs : SStep (simEnv20T B) (cfgV z is) (cfgV z' is')) :
    SStep (simEnv20T B) (cfgV z (vs ++ is ++ rest)) (cfgV z' (vs ++ is' ++ rest)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("val*", .list vs), ("instr*", .list is),
    ("instr_1*", .list rest), ("z'", z'), ("instr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fv : ρ.findVal? "val*" = some (.list vs) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fr : ρ.findVal? "instr_1*" = some (.list rest) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "instr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv20T B) ρ [.expP "z" stateT, .expP "val*" valsTy,
      .expP "instr*" adminsTy, .expP "instr_1*" adminsTy, .expP "z'" stateT,
      .expP "instr'*" adminsTy] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons fr (hrest ρ hρ)
      (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ev : EvalExp (simEnv20T B) ρ valsE (.list vs) := evalExp_subIterPat (by decide) fv
  have ev' : EvalExp (simEnv20T B) ρ (iterV "val" "val*") (.list vs) :=
    evalExp_iterPat (by decide) fv
  have ei : EvalExp (simEnv20T B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv20T B) ρ (iterV "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have er : EvalExp (simEnv20T B) ρ (iterV "instr_1" "instr_1*") (.list rest) :=
    evalExp_iterPat (by decide) fr
  have hor : EvalExp (simEnv20T B) ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (iterV "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterV "instr_1" "instr_1*") (.listE [])))
      (.bool (decide (vs ≠ [] ∨ rest ≠ []))) :=
    evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er)
  have hd : decide (vs ≠ [] ∨ rest ≠ []) = true := decide_eq_true hne
  have hg : SStep (simEnv20T B) (cfgV z (vs ++ (is ++ rest))) (cfgV z' (vs ++ (is' ++ rest))) :=
    dderives_of_ruleAt (hasRuleAt_ctxtInstrsFixT B) _ hq
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

end Silmaril.Wasm.SpecTec.Sim20.StoreFix
