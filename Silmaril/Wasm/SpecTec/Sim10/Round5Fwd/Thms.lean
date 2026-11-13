module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdWitness10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CtrlRefute10

/-!
# The 1.0 route, an earlier step (track v10): the forward half in `simEnv10T`, one invariant

See `docs/projects/spectec/README.md`, "v10".

* `FwdBase10T` (namespace `Sim10.Whole`): firings of `simEnv10T` built from `simEnv10`
  evaluations and `simEnv10T` quantifier typings (`fires_of_ruleAtT`), `Step/pure` and
  `Step/read` in `simEnv10T`, and the code-typing inversions there.
* `FwdLeaf10T` … `FwdLoadVal10T`: the 78 forward leaves of rounds 2–4 at `FwdAt10T`
  (`fwdAt10T_*`).
* `FwdWhole10T`: every V1 step under `Plain10`, `GSetOk` and `MemsAligned10` satisfies `FwdAt10T`
  (`fwd10T_step`), and the whole step with typed images (`wholeStepFwd10T_inv`).
* `SubjRed10T`: subject reduction in `simEnv10T`, stores included (`typed10_stepT`).
* `FwdRun10T`: the whole step under one invariant without a successor hypothesis
  (`wholeStepFwd10T_one`), along runs (`wholeRunFwd10T`), from `CoreTyped10`
  (`Valid.wholeRunFwd10CT`) and from an invocation (`Valid.wholeRunFwd10InvT`).
* `FwdWitness10T` (namespace `Sim10.Witness10T`): valid Core stores with a function, for round
  4's `Task.wholeRunFwd10Inv` (`wholeRunFwd10Inv_nopDrop`) and, with a storing function untyped
  in `simEnv10`, for `wholeRunFwd10InvT` (`wholeRunFwd10InvT_storeBody`).
* `CtrlRefute10`: the unrestricted `br-zero` leaf (any tail, not only a plain one) is false
  (`not_labelBranchField10`): the script is stuck at `LABEL_ 0 {ε} (BR 0; TRAP)`
  (`not_sstep10_brTrap`), where V1 steps.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fires_of_ruleAtT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fires_of_ruleAtT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10T_callIndirectTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10T_callIndirectTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10T_invokeWasm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10T_invokeWasm

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10T_num' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10T_num

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10T_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10T_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10T_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10T_inv

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.typed10_stepT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.typed10_stepT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10T_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10T_one

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10T_stores_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10T_stores_one

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeRunFwd10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeRunFwd10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10InvT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10InvT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Witness10T.storeOk_storeBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Witness10T.storeOk_storeBody

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Witness10T.wholeRunFwd10Inv_nopDrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Witness10T.wholeRunFwd10Inv_nopDrop

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Witness10T.not_typed10_storeBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Witness10T.not_typed10_storeBody

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Witness10T.wholeRunFwd10InvT_storeBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Witness10T.wholeRunFwd10InvT_storeBody

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Witness10T.sstep10T_invoke_storeBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Witness10T.sstep10T_invoke_storeBody

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstep10_brTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstep10_brTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelBranchField10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelBranchField10
