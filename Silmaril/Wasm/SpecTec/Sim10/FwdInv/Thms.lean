module

public import Silmaril.Wasm.SpecTec.Sim10.Fwd.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SubjRed
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdRestQ

/-!
# The forward 1.0 half under a reachability invariant (round 3, pass 2)

In `Silmaril.Wasm.SpecTec.Sim10.Whole`.

* **The invariant** (`Sim10.PlainInv`): `Plain10 code`, plain instructions after the first
  non-value, recursively in label and frame bodies. `plain10_step`/`plain10_steps`: every V1 step
  and run preserves it; `plain10_invoke`: an invocation's code satisfies it. `GSetOk` (round 2)
  passes inwards (`gsetOk_mid`, `gsetOk_label`, `gsetOk_frame`).
* **New forward leaves**, at every builtins:
  - `fwdAt10_labelBranch`, `fwdAt10_labelBranchOuter`, `fwdAt10_labelReturn`,
    `fwdAt10_frameReturn`, `fwdAt10_trapValues`, `fwdAt10_trapTail` (`Sim10.FwdCtrl`), at a plain
    suffix; `typedV_instr_of_admin10` (an instruction typed as `admininstr` is typed as `instr`),
    `typedV_labelidx10`;
  - `fwdAt10_globalSet` (`Sim10.FwdState`), for a value of the global's type;
  - `not_typed_host10`, so `fwdAt10_invokeHost` and `fwdAt10_invokeHostDiverges` are vacuous;
  - `fwdAt10_block`, `fwdAt10_loop`, `fwdAt10_ifNonzero`, `fwdAt10_ifZero` (`Sim10.FwdBlock`);
  - `fwdAt10_num` (`Sim10.FwdNum`): the ten numeric steps under `NumAgree10` at the spec profile,
    so at `floatIntB` (`fwdAt10_num_floatIntB`);
  - `not_typedV_store10` (`Sim10.FwdStoreVac`): no 1.0 `STORE` is typed, so the four store
    leaves are vacuous.
* **Assembly**: `fwd10_of_restP` (`Sim10.FwdRestP`) and `wholeStepFwd10_of_restQ`
  (`Sim10.FwdRestQ`): under `FwdRestQ10` (12 obligations: `br_table`, `call_indirect` ×4,
  `invokeWasm`, loads ×4, `memory.size`, `memory.grow`), every V1 step from a typed image
  satisfying `Plain10` and `GSetOk` to a typed image is a step of the 1.0 script at
  `floatIntB (Profile.spec nd r)`.
* **Subject reduction for the fragment** (`Sim10.SubjRed`): `typed10_of_nest`, and
  `wholeStepNest10'`, `Task.wholeStepNest10` without the successor's typing.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.plain10_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.plain10_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10_of_restP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10_of_restP

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_of_restQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_of_restQ

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepNest10'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepNest10'

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_typedV_store10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_typedV_store10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_num_floatIntB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_num_floatIntB
