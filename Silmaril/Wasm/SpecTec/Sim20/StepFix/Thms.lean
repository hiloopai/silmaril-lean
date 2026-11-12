module

public import Silmaril.Wasm.SpecTec.Sim20.StepFix.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StepFix
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StepFixRun
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StepFixRefute
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StepFixLift

/-!
# The 2.0 `Step` erratum: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.StepFix`; see `docs/projects/spectec/README.md`.

* `stepErratum20_applies` (kernel): the erratum applies to `Scripts.Wasm20.fixed`;
  `applyErratum_step20`: the result is `fixedS20`.
* `Task.wholeStepValidS` (the corrected forward and backward whole-step target) is stated in
  `StepFix.Defs`. It is **refuted** in pass 7: `not_wholeStepValidS` (`StepFixRefute`).

Pass 7, `StepFixRun`:

* `closedB_step20S`, `sstepB20S_iff`: the corrected `Step`, `Step_pure`, `Step_read` are closed,
  so the backend reading is the declarative one;
* `sstepS_pure`, `sstepS_ctxtInstrs`: the erratum's `Step/pure` and `Step/ctxt-instrs` lift steps
  (after the 3.0 `Sim.sstep_pure`, `Sim.sstep_ctxtInstrs`);
* `sstepS_nopNop`, `sstepS_nopNop_empty`: `NOP NOP` steps to `NOP`;
* `sstepS_unreachable`, `sstepS_unreachable_empty`: `UNREACHABLE` steps to `TRAP`.

Round 2 pass 5, `StepFixLift`: `sstepS_read`, `sstepS_ctxtLabel`, `sstepS_ctxtFrame`, the other
three structural rules of the erratum (after the 3.0 `Sim.sstep_read`, `Sim.sstep_ctxtLabel`,
`Sim.sstep_ctxtFrame`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StepFix.applyErratum_step20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StepFix.applyErratum_step20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_nopNop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_nopNop

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_unreachable

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StepFix.not_wholeStepValidS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StepFix.not_wholeStepValidS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_read

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_ctxtLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_ctxtLabel

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_ctxtFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StepFix.sstepS_ctxtFrame
