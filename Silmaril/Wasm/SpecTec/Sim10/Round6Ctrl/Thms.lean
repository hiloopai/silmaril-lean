module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CtrlRefuteAll
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitness10

/-!
# The 1.0 route, round 6 (track v10): control leaves refuted, the forward run from instantiation

See `docs/projects/spectec/README.md`, "v10-inst".

* `CtrlStuckG` (namespace `Sim10.Whole`): `Like10 B E`, what the refutations read of an
  environment (relations of `simEnv10`, `val*` as `CONST`s, `TRAP` not an `instr`, `labelidx` a
  number); `simEnv10` and `simEnv10T` satisfy it (`like10_simEnv10`, `like10_simEnv10T`). Over
  any such `E`: `z; ε`, `z; x`, `z; x TRAP`, `z; TRAP` and `z; TRAP TRAP` are stuck.
* `CtrlLabG`: `z; LABEL_ 0 {ε} (x TRAP)` and `z; FRAME_ 0 {f} (x TRAP)` are stuck over any such
  `E` (`not_sstepG_labX`, `not_sstepG_frmX`).
* `CtrlRefuteAll`: the unrestricted `br-succ`, `return-label`, `return-frame` and `trap-vals`
  (`trapTail`) obligations are false in `simEnv10`, and all five (with `br-zero`) are false in
  `simEnv10T`, at every builtins.
* `InstValid10` (namespace `Sim10.Valid`): `CoreTyped10` and `MemsAligned10` at an invocation
  from a valid Core store erasing to the image (`coreTyped10_invoke_erase`); a V1 instantiation
  under the copied `InstantiationBounds` yields one (`instantiation_core10`); so round 4's
  `Task.wholeRunFwd10Inv` and its `simEnv10T` form hold with Core `StoreOk` of the invoked store
  replaced by V1 instantiation (`wholeRunFwd10InvV`, `wholeRunFwd10InvVT`,
  `wholeRunFwd10InvV_empty`).
* `InstWitness10` (namespace `Sim10.InstWitness10`): a valid V1 module instantiated into the
  empty store at which every hypothesis of `wholeRunFwd10InvV_empty` holds
  (`wholeRunFwd10InvV_add0`, first step `sstep10_invoke_add0`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.like10_simEnv10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.like10_simEnv10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_hasTyp_trap_instr10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_hasTyp_trap_instr10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstepG_trapTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstepG_trapTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstepG_labX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstepG_labX

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstepG_frmX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstepG_frmX

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelBranchOuterField10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelBranchOuterField10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelReturnField10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelReturnField10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_frameReturnField10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_frameReturnField10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_trapTailField10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_trapTailField10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelBranchField10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelBranchField10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelBranchOuterField10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelBranchOuterField10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelReturnField10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_labelReturnField10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_frameReturnField10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_frameReturnField10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_trapTailField10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_trapTailField10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.coreTyped10_invoke_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.coreTyped10_invoke_erase

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.instantiation_core10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.instantiation_core10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10InvV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10InvV

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10InvVT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10InvVT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10InvV_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10InvV_empty

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstWitness10.wholeRunFwd10InvV_add0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstWitness10.wholeRunFwd10InvV_add0

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstWitness10.sstep10_invoke_add0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstWitness10.sstep10_invoke_add0
