module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeVecEdge

/-!
# `Task.wholeStepBwdV`, refuted

`WholeVecEdge` shows that rule 39 of wasm-2.0 `Step_pure` (`vtestop-false`) reduces
`v128.const ones; i64x2.all_true` to `i32.const 0` at the spec's scalar builtins
(`Sim.Floats.floatIntB`), which do not interpret `$lanes_`, while V2 only reduces it to
`i32.const 1`. Here the step is lifted through `Step/pure` (rule 0 of `Step`) to the whole
configuration in the empty store and frame, whose image is typed (`typed20_allTrue`) and whose code
has no conversion (`CvtOkL`). So the backward whole-step target at those builtins is false:

```lean
theorem not_wholeStepBwdV : ¬ Task.wholeStepBwdV
```
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk DDerives otherwise Fires PremW SStep cfgV
  dderives_iff_fires evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

set_option maxRecDepth 100000

variable {H : Type}

/-- `Step/pure` (rule 0 of wasm-2.0 `Step`) lifts a `Step_pure` derivation between typed `instr*`
sequences to the configuration. -/
theorem sstep20_of_pure {B : Builtins} {z : Value} {is js : List Value}
    (hz : HasTyp (simEnv20 B) (VarEnv.empty.bindVals
      [("z", z), ("instr*", .list is), ("instr'*", .list js)]) (.varT "state" []) z)
    (hi : HasTyp (simEnv20 B) (VarEnv.empty.bindVals
      [("z", z), ("instr*", .list is), ("instr'*", .list js)]) instrsT20 (.list is))
    (hj : HasTyp (simEnv20 B) (VarEnv.empty.bindVals
      [("z", z), ("instr*", .list is), ("instr'*", .list js)]) instrsT20 (.list js))
    (hp : DDerives (simEnv20 B) (otherwise (simEnv20 B)) "Step_pure" "%~>%" []
      (.tuple [.list is, .list js])) :
    SStep (simEnv20 B) (cfgV z is) (cfgV z js) := by
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (simEnv20 B).findRel? "Step" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩
  refine (dderives_iff_fires hrel).2 ⟨0, Pure.fires_of_ruleAt (hasRuleAt_stepPure B)
    [("z", z), ("instr*", .list is), ("instr'*", .list js)] ?_ ?_ ?_⟩
  · exact QuantsOk.cons rfl hz (QuantsOk.cons rfl hi
      (QuantsOk.cons rfl hj QuantsOk.nil))
  · exact evalExp_tup2 (evalExp_case (evalExp_tup2 (Silmaril.Wasm.SpecTec.Sim.evalExp_var rfl)
      (evalExp_subIterPat (by decide) rfl)))
      (evalExp_case (evalExp_tup2 (Silmaril.Wasm.SpecTec.Sim.evalExp_var rfl)
      (evalExp_subIterPat (by decide) rfl)))
  · intro pr hpr
    rw [List.mem_singleton.1 hpr]
    exact PremW.rulePr Equiv.evalArgs_nil (evalExp_tup2 (evalExp_subIterPat (by decide) rfl)
      (evalExp_subIterPat (by decide) rfl)) hp

/-- The configuration of the counterexample: `v128.const ones; i64x2.all_true` in the empty store
and frame. -/
abbrev allTrueCfg : Config Empty := ⟨{}, {}, allTrueCode ones128⟩

/-- Its image under `Sim.Floats.floatIntB`'s `Step` (the script's answer). -/
abbrev zeroCfg : Config Empty := ⟨{}, {}, [constI32 0]⟩

set_option maxHeartbeats 4000000 in
/-- The image of `allTrueCfg` is IL-typed. -/
theorem typed20_allTrue (B : Builtins) : Typed20 (simEnv20 B) Empty.elim allTrueCfg :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
/-- **The 2.0 script steps from `allTrueCfg` to `zeroCfg`** at the spec's scalar builtins. -/
theorem sstepB_allTrue (P : Profile) :
    SStepB (simEnv20 (Sim.Floats.floatIntB P)) (configV Empty.elim allTrueCfg)
      (configV Empty.elim zeroCfg) := by
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (simEnv20 (Sim.Floats.floatIntB P)).findRel? "Step_pure" = some ([], "%~>%", t, rules) :=
    ⟨_, _, rfl⟩
  refine (sstepB20_iff _).2 (sstep20_of_pure ?_ ?_ ?_ ((dderives_iff_fires hrel).2 ⟨39, fires39 P⟩))
  · exact ⟨100, by with_unfolding_all rfl⟩
  · exact ⟨100, by with_unfolding_all rfl⟩
  · exact ⟨100, by with_unfolding_all rfl⟩

/-- `zeroCfg` is not the image of a configuration whose code is `i32.const 1`. -/
theorem configV_zero_ne {c : Config Empty} (hc : c.code = [constI32 1]) :
    configV Empty.elim zeroCfg ≠ configV Empty.elim c := by
  intro h
  obtain ⟨s, f, code⟩ := c
  simp only at hc
  subst hc
  simp [configV, adminsToV, adminToV, instrToV, valV, numV, Equiv.Execution.pctV] at h

/-- **`Task.wholeStepBwdV` is false.** At `Profile.spec false {}` (any `nd` and `r` would do) the
wasm-2.0 script, at the spec's scalar builtins, reduces `v128.const ones; i64x2.all_true` (typed,
no conversion) to `i32.const 0`, which is not the image of any V2 step. -/
theorem not_wholeStepBwdV : ¬ Task.wholeStepBwdV := by
  intro h
  obtain ⟨c', hw, hs⟩ := h Empty Empty.elim (fun a => a.elim) (fun _ _ _ _ => False) false {}
    allTrueCfg _ (typed20_allTrue _) (by simp [CvtOkL, CvtOkA]) (sstepB_allTrue _)
  exact configV_zero_ne ((step_allTrue hs).1 rfl) hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
