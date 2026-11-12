module

public import Silmaril.Wasm.SpecTec.Sim20.StepFix.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StepFix
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeVecRefute

/-!
# The corrected 2.0 script runs: `nop nop` steps and `unreachable` traps

`stepErratum20` (`Sim20.StepFix.Defs`) gives wasm-2.0 `Step` the five structural rules of 3.0's
shape. This module builds derivations with them in `simEnv20S B`:

* `sstepB20S_iff`: `Step`, `Step_pure` and `Step_read` stay closed in the corrected script, so its
  backend reading is its declarative reading;
* `sstepS_pure`, `sstepS_ctxtInstrs`: `Step/pure` and `Step/ctxt-instrs` lift a step, for
  arbitrary values of the right IL types. They are the 3.0 lemmas `Sim.sstep_pure` and
  `Sim.sstep_ctxtInstrs` (`Sim/Lift.lean`), restated for the erratum's rules, which type the code
  `admininstr*` and coerce `val*` to `admininstr`;
* `sstepS_nopNop`: `NOP NOP` steps to `NOP` (in the original script it is stuck,
  `Whole.stuck_nopNop`);
* `sstepS_unreachable`: `UNREACHABLE` steps to `TRAP` (in the original script it is stuck,
  `Whole.stuck_unreachable`);

`StepFixRefute` uses these to refute `Task.wholeStepValidS`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StepFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat caseNilV)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk DDerives otherwise Fires PremW SStep SPure cfgV TypedV
  ValsOnly stateT dderives_iff_fires dderives_of_ruleAt evalExp_tup2 evalExp_case
  evalExp_cat evalExp_ne_nil evalExp_or prems_one prems_two)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB closedB Closed closed_of_closedB closed_congr
  dderivesB_otherwise_iff_of_closed)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## Provenance and closedness -/

theorem hasRuleAt_pureFix : HasRuleAt (simEnv20S B) "Step" "%~>%" 0 pureFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_ctxtInstrsFix : HasRuleAt (simEnv20S B) "Step" "%~>%" 2 ctxtInstrsFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step`, `Step_pure` and `Step_read` are closed in the corrected script. -/
theorem closedB_step20S :
    closedB (envOfScript fixedS20) ["Step", "Step_pure", "Step_read"] = true := by
  decide +kernel

/-- The three reduction relations are closed in `simEnv20S B`. -/
theorem closed_step20S : Closed (simEnv20S B) (· ∈ ["Step", "Step_pure", "Step_read"]) :=
  closed_congr (fun _ => rfl) (closed_of_closedB closedB_step20S)

/-- **On the corrected `Step` the backend reading is the declarative reading.** -/
theorem sstepB20S_iff {c c' : Value} : SStepB (simEnv20S B) c c' ↔ SStep (simEnv20S B) c c' :=
  dderivesB_otherwise_iff_of_closed (closed_step20S B) (by simp)

/-! ## Lifting through `Step/pure` and `Step/ctxt-instrs` -/

/-- `val*`, the type of the value prefix of `ctxt-instrs`. -/
abbrev valsTy : Typ := .iterT (.varT "val" []) .list

variable {B}

/-- **`Step/pure`** of the corrected script: a `Step_pure` step between `admininstr*` sequences is
a `Step` step at any state. (After `Sim.sstep_pure`.) -/
theorem sstepS_pure {z : Value} {is js : List Value} (hz : TypedV (simEnv20S B) stateT z)
    (his : TypedV (simEnv20S B) adminsTy (.list is)) (hjs : TypedV (simEnv20S B) adminsTy (.list js))
    (hp : SPure (simEnv20S B) is js) : SStep (simEnv20S B) (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("instr*", .list is), ("instr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fj : ρ.findVal? "instr'*" = some (.list js) := rfl
  have hq : QuantsOk (simEnv20S B) ρ
      [.expP "z" stateT, .expP "instr*" adminsTy, .expP "instr'*" adminsTy] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp (simEnv20S B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp (simEnv20S B) ρ (iterV "instr'" "instr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  exact dderives_of_ruleAt (hasRuleAt_pureFix B) _ hq
    (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ej)))
    (prems_one (.rulePr Equiv.evalArgs_nil (evalExp_tup2 ei ej) hp))

/-- **`Step/ctxt-instrs`** of the corrected script: a step under a value prefix `vs` and a suffix
`rest`, not both empty. (After `Sim.sstep_ctxtInstrs`.) -/
theorem sstepS_ctxtInstrs {z z' : Value} {vs is is' rest : List Value}
    (hz : TypedV (simEnv20S B) stateT z) (hz' : TypedV (simEnv20S B) stateT z')
    (hvs : TypedV (simEnv20S B) valsTy (.list vs)) (his : TypedV (simEnv20S B) adminsTy (.list is))
    (his' : TypedV (simEnv20S B) adminsTy (.list is'))
    (hrest : TypedV (simEnv20S B) adminsTy (.list rest)) (hne : vs ≠ [] ∨ rest ≠ [])
    (hs : SStep (simEnv20S B) (cfgV z is) (cfgV z' is')) :
    SStep (simEnv20S B) (cfgV z (vs ++ is ++ rest)) (cfgV z' (vs ++ is' ++ rest)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("val*", .list vs), ("instr*", .list is),
    ("instr_1*", .list rest), ("z'", z'), ("instr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fv : ρ.findVal? "val*" = some (.list vs) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fr : ρ.findVal? "instr_1*" = some (.list rest) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "instr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv20S B) ρ [.expP "z" stateT, .expP "val*" valsTy,
      .expP "instr*" adminsTy, .expP "instr_1*" adminsTy, .expP "z'" stateT,
      .expP "instr'*" adminsTy] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons fr (hrest ρ hρ)
      (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ev : EvalExp (simEnv20S B) ρ valsE (.list vs) := evalExp_subIterPat (by decide) fv
  have ev' : EvalExp (simEnv20S B) ρ (iterV "val" "val*") (.list vs) :=
    evalExp_iterPat (by decide) fv
  have ei : EvalExp (simEnv20S B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv20S B) ρ (iterV "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have er : EvalExp (simEnv20S B) ρ (iterV "instr_1" "instr_1*") (.list rest) :=
    evalExp_iterPat (by decide) fr
  have hor : EvalExp (simEnv20S B) ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (iterV "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterV "instr_1" "instr_1*") (.listE [])))
      (.bool (decide (vs ≠ [] ∨ rest ≠ []))) :=
    evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er)
  have hd : decide (vs ≠ [] ∨ rest ≠ []) = true := decide_eq_true hne
  have hg : SStep (simEnv20S B) (cfgV z (vs ++ (is ++ rest))) (cfgV z' (vs ++ (is' ++ rest))) :=
    dderives_of_ruleAt (hasRuleAt_ctxtInstrsFix B) _ hq
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

/-! ## Typing in every scope, from typing in the empty scope -/

/-- A closed type name, from the empty scope to every scope binding term variables only. -/
theorem typedV_of_empty {x : IL.Id} {v : Value}
    (h : HasTyp (simEnv20S B) VarEnv.empty (.varT x []) v) : TypedV (simEnv20S B) (.varT x []) v :=
  fun _ hρ => Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ hρ h

/-- A list over a closed type name, likewise. -/
theorem typedV_list_of_empty {x : IL.Id} {l : List Value}
    (h : HasTyp (simEnv20S B) VarEnv.empty (.iterT (.varT x []) .list) (.list l)) :
    TypedV (simEnv20S B) (.iterT (.varT x []) .list) (.list l) := by
  intro ρ hρ
  obtain ⟨l', he, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := Value.list.inj he
  exact hasTyp_iterT_list_iff.2 ⟨l, rfl, hasTypList_iff.2 fun u hu =>
    Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ hρ (hasTypList_iff.1 hl u hu)⟩

/-! ## `nop nop` steps and `unreachable` traps -/

section Runs

variable (B)

theorem hasRuleAt_unreachableS :
    HasRuleAt (simEnv20S B) "Step_pure" "%~>%" 0 Equiv.Execution.unreachableRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_nopS : HasRuleAt (simEnv20S B) "Step_pure" "%~>%" 1 Equiv.Execution.nopRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
theorem typedV_nil : TypedV (simEnv20S B) adminsTy (.list []) :=
  typedV_list_of_empty ⟨10, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typedV_vals_nil : TypedV (simEnv20S B) valsTy (.list []) :=
  typedV_list_of_empty ⟨10, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typedV_nop : TypedV (simEnv20S B) adminsTy (.list [Whole.nopV]) :=
  typedV_list_of_empty ⟨20, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typedV_unreachable : TypedV (simEnv20S B) adminsTy (.list [Whole.unreachableV]) :=
  typedV_list_of_empty ⟨20, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typedV_trap : TypedV (simEnv20S B) adminsTy (.list [caseNilV "TRAP"]) :=
  typedV_list_of_empty ⟨100, by with_unfolding_all rfl⟩

/-- **`NOP NOP` steps to `NOP`** in the corrected script, at every typed state, by
`ctxt-instrs` over `Step/pure` of `nop`. In the original script it is stuck
(`Whole.stuck_nopNop`). -/
theorem sstepS_nopNop {z : Value} (hz : TypedV (simEnv20S B) stateT z) :
    SStepB (simEnv20S B) (cfgV z [Whole.nopV, Whole.nopV]) (cfgV z [Whole.nopV]) := by
  have h₁ : SStep (simEnv20S B) (cfgV z [Whole.nopV]) (cfgV z []) :=
    sstepS_pure hz (typedV_nop B) (typedV_nil B)
      (Sim.IntNumeric.spure_nopRule (hasRuleAt_nopS B))
  have h₂ := sstepS_ctxtInstrs (vs := []) (rest := [Whole.nopV]) hz hz (typedV_vals_nil B)
    (typedV_nop B) (typedV_nil B) (typedV_nop B) (.inr (by simp)) h₁
  exact (sstepB20S_iff B).2 (by simpa using h₂)

/-- **`UNREACHABLE` traps** in the corrected script, at every typed state. In the original script it
is stuck (`Whole.stuck_unreachable`): `TRAP` is not an `instr`. -/
theorem sstepS_unreachable {z : Value} (hz : TypedV (simEnv20S B) stateT z) :
    SStepB (simEnv20S B) (cfgV z [Whole.unreachableV]) (cfgV z [caseNilV "TRAP"]) :=
  (sstepB20S_iff B).2 (sstepS_pure hz (typedV_unreachable B) (typedV_trap B)
    (Sim.IntNumeric.spure_unreachable (hasRuleAt_unreachableS B)))

set_option maxHeartbeats 4000000 in
/-- The empty state is typed. -/
theorem typedV_emptyState {H : Type} (hn : H → String) :
    TypedV (simEnv20S B) stateT (stateV hn {} {}) :=
  typedV_of_empty ⟨100, by with_unfolding_all rfl⟩

/-- **V2's `nop nop` in the empty store and frame steps in the corrected script**, to the image of
V2's own successor (`Whole.step_nopNop`). -/
theorem sstepS_nopNop_empty {H : Type} (hn : H → String) :
    SStepB (simEnv20S B) (configV hn ⟨{}, {}, [.plain .nop, .plain .nop]⟩)
      (configV hn ⟨{}, {}, [.plain .nop]⟩) :=
  sstepS_nopNop B (typedV_emptyState B hn)

/-- **V2's `unreachable` in the empty store and frame traps in the corrected script**, to the image
of V2's own successor (`Whole.step_unreachable`). -/
theorem sstepS_unreachable_empty {H : Type} (hn : H → String) :
    SStepB (simEnv20S B) (configV hn ⟨{}, {}, [.plain .unreachable]⟩)
      (configV hn ⟨{}, {}, [.trap]⟩) :=
  sstepS_unreachable B (typedV_emptyState B hn)

end Runs

end Silmaril.Wasm.SpecTec.Sim20.StepFix
