module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Refute.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Refute.RefTest
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Refute.Promote

/-!
# SpecTec ↔ Core 3.0, round 6, track refute: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.Refute`; see `docs/projects/spectec/README.md`.

* `not_wholeStepValidSel`: **`Round5.Task.wholeStepValidSel` is false.** At
  `ref.null; ref.test (ref null any)` (`testCfg`, valid and `BoundedSel`), SpecTec steps to
  `i32.const 0` in every `simEnv B` (`sstep_testCfg`), and Core only to `i32.const 1`
  (`step_testCfg_inv`), so the backward conjunct fails (`not_backwardSel_testCfg`).
* `step_refTest_inv`: Core's `Step` inverted at `[ref r, ref.test rt]`.
* `sread_refTestFalseN`, `fwdP_refTest0`: SpecTec's `ref.test-false` fires whenever SpecTec's
  `Ref_ok` fails, whatever Core's `RefOk` says.
* At `v128.const nanLane0; f64x2.promote_low_f32x4` (`promCfg`), Core has two different successors
  under the spec NaN profile (`step_promCfg`, `promDone_ne`) and SpecTec none
  (`not_sstep_promCfg`, so `sstep_promCfg_det` holds vacuously). The witness is not `BoundedSel`
  (`not_boundedSel_promCfg`: the instruction is `FloatMissel`), so it does not bear on
  `wholeStepValidSel`; it only refutes `wholeStepValidOk` again (`not_forwardOk_promCfg`).
-/

namespace Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Refute.not_wholeStepValidSel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round6.Refute.not_wholeStepValidSel

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Refute.not_backwardSel_testCfg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round6.Refute.not_backwardSel_testCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Refute.step_refTest_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round6.Refute.step_refTest_inv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Refute.not_sstep_promCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round6.Refute.not_sstep_promCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Refute.promDone_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Round6.Refute.promDone_ne

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Refute.not_boundedSel_promCfg' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Round6.Refute.not_boundedSel_promCfg

end Silmaril.Wasm.SpecTec.Sim
