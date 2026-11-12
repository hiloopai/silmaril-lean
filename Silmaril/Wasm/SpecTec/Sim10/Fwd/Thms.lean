module

public import Silmaril.Wasm.SpecTec.Sim10.Whole.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdReduce

/-!
# The forward 1.0 half: what is proved

In `Silmaril.Wasm.SpecTec.Sim10.Whole`. The wasm-1.0 script needs no erratum: its `Step` has the five
structural rules (`pure`, `read`, `ctxt-label`, `ctxt-frame` with a successor inner frame, and
`ctxt-instrs`) that 2.0 lacks and that `Sim20.StepFix` adds back.

* `sstep10_pure`, `sstep10_read`, `sstep10_ctxtInstrs`, `sstep10_ctxtLabel`, `sstep10_ctxtFrame`
  (`Sim10.FwdLift`): each structural rule lifts a step, given typed quantifiers.
* The typing inversions (`Sim10.FwdNest`): `typedV_state_of_typed10`, `typedV_code_of_typed10`,
  `typedV_stV_iff10`, `label_inv10`, `frame_inv10`, `typedV_val_of_admin10`.
* `fwd10_context`, `fwd10_label`, `fwd10_frame`: V1's `context`, `label` and `frame` on images,
  with every typing read off the outer configurations.
* **`fwd10_nest`**: the forward obligation `FwdAt10` passes from leaves `L` to `Nest10 L`, the
  closure under any nesting of V1's three structural rules, at every builtins.
* `fwdAt10_unreachable`, `fwdAt10_nop`, `fwdAt10_drop`, `fwdAt10_labelDone`, `fwdAt10_frameDone`,
  `fwdAt10_labelTrap`, `fwdAt10_frameTrap`, `fwdAt10_localTee`, `fwdAt10_localGet`,
  `fwdAt10_globalGet`, `fwdAt10_call`, `fwdAt10_localSet` (`Sim10.FwdLeaf`): twelve leaves, at
  every builtins, each quantifier typed from the configuration (`typedV_idx_of_case10` for
  indices, `label_inv10`/`frame_inv10` for label and frame components).
* `fwdAt10_brIfZero`, `fwdAt10_brIfNonzero`, `fwdAt10_selectZero`, `fwdAt10_selectNonzero`
  (`Sim10.FwdLeafI32`): four more, the condition `c : val_(I32)` typed from its `CONST`
  (`typedV_valI32_of_const10`).
* **`wholeStepNest10 : Task.wholeStepNest10`** (`Sim10.FwdReduce`): every `Nest10 Leaf10F` step
  (`Leaf10F`: the sixteen leaves above)
  between configurations whose images are typed is a step of the 1.0 script, at every builtins.
* `fwd10_of_leaves`, `fwd10_of_rest`: every V1 step satisfies `FwdAt10` under `FwdLeaves10` (one
  obligation per V1 constructor), or under the open part `FwdRest10`.

As for 2.0, the successor's typing is a hypothesis; subject reduction for the image is not proved.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10_nest

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepNest10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepNest10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10_of_rest
