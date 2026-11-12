module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StepFixRun

/-!
# `Task.wholeStepValidS`, refuted

The erratum `stepErratum20` changes only `Step`; `Step_pure` is the 2.0 script's
(`relRules_pure20S`). So the `vtestop` edge of `WholeVecEdge` holds in `simEnv20S` as well
(`allTrueEnv20S`): at the spec's scalar builtins (`Sim.Floats.floatIntB`), which do not answer
`$lanes_`, `vtestop-false` reduces `v128.const ones; i64x2.all_true` to `i32.const 0`, and
`Step/pure` of the corrected script lifts that to the configuration (`sstepBS_allTrue`). V2 only
reduces it to `i32.const 1` (`Whole.step_allTrue`). So the backward half of the corrected target
fails:

```lean
theorem not_wholeStepValidS : ¬ Task.wholeStepValidS
```
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StepFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

set_option maxRecDepth 100000

variable (B : Builtins)


/-- The erratum leaves `Step_pure` alone. -/
theorem relRules_pure20S :
    Sim.RefsGC.relRules (simEnv20S B) "Step_pure" = Sim.RefsGC.relRules (simEnv20 B) "Step_pure" :=
  rfl

/-- The `vtestop` edge of `WholeVecEdge` holds in the corrected script. -/
theorem allTrueEnv20S (P : Profile) : Whole.AllTrueEnv (simEnv20S (Sim.Floats.floatIntB P)) where
  r38 := ⟨_, _, _, rfl, rfl, rfl⟩
  r39 := ⟨_, _, _, rfl, rfl, rfl⟩
  tags := by rw [relRules_pure20S]; exact (Whole.allTrueEnv20 P).tags
  lanesDef := ⟨_, _, rfl⟩
  lanesNone := Whole.floatIntB_lanes P

set_option maxHeartbeats 4000000 in
/-- **The corrected script also steps from `v128.const ones; i64x2.all_true` to `i32.const 0`** at
the spec's scalar builtins. -/
theorem sstepBS_allTrue (P : Profile) :
    SStepB (simEnv20S (Sim.Floats.floatIntB P)) (configV Empty.elim Whole.allTrueCfg)
      (configV Empty.elim Whole.zeroCfg) := by
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (simEnv20S (Sim.Floats.floatIntB P)).findRel? "Step_pure" = some ([], "%~>%", t, rules) :=
    ⟨_, _, rfl⟩
  have hq : QuantsOk (simEnv20S (Sim.Floats.floatIntB P)) (VarEnv.empty.bindVals Whole.allTrueσ)
      [.expP "c" (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]), .expP "Jnn" (.varT "Jnn" []),
        .expP "N" (.varT "N" [])] :=
    QuantsOk.cons rfl ⟨100, by with_unfolding_all rfl⟩ (QuantsOk.cons rfl
      ⟨100, by with_unfolding_all rfl⟩ (QuantsOk.cons rfl ⟨100, by with_unfolding_all rfl⟩
        QuantsOk.nil))
  exact (sstepB20S_iff _).2 (sstepS_pure (typedV_emptyState _ Empty.elim)
    (typedV_list_of_empty ⟨100, by with_unfolding_all rfl⟩)
    (typedV_list_of_empty ⟨100, by with_unfolding_all rfl⟩)
    ((dderives_iff_fires hrel).2 ⟨39, Whole.fires39_of (allTrueEnv20S P) hq⟩))

set_option maxHeartbeats 4000000 in
/-- The image of `Whole.allTrueCfg` is typed in the corrected script. -/
theorem typed20S_allTrue (B : Builtins) : Typed20 (simEnv20S B) Empty.elim Whole.allTrueCfg :=
  ⟨100, by with_unfolding_all rfl⟩

/-- **`Task.wholeStepValidS` is false.** Its backward half fails at
`v128.const ones; i64x2.all_true` in the empty store and frame: the corrected script, at the spec's
scalar builtins, reduces it to `i32.const 0`, V2 only to `i32.const 1`. -/
theorem not_wholeStepValidS : ¬ Task.wholeStepValidS := by
  intro h
  obtain ⟨-, hb⟩ := h Empty Empty.elim (fun a => a.elim) (fun _ _ _ _ => False) false {}
  obtain ⟨c', hw, hs⟩ := hb Whole.allTrueCfg _ (typed20S_allTrue _) (by simp [CvtOkL, CvtOkA])
    (sstepBS_allTrue _)
  exact Whole.configV_zero_ne ((Whole.step_allTrue hs).1 rfl) hw

end Silmaril.Wasm.SpecTec.Sim20.StepFix
