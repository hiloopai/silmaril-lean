module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostStubWit10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Name10Store

/-!
# The 1.0 route with host functions, round 7

See `docs/projects/spectec/README.md`, "v10-host".

* `HostStub10`, `HostStubCore10` (namespace `Sim10.HostStub`): the stub restatement. The 1.0
  IL has no host function instance; a host function instance is read as the defined function
  instance `stubF (.host t h) = .wasm t (stubMod t) stubFn` (`FUNC 0 [] [UNREACHABLE]` in a
  module instance with the one type `t`). Runs under the empty host commute with the stub
  (`steps_stub`); every V1 step is a step under the empty host or has a host call as its redex
  (`step_empty_or_hostCall`). The Core hypotheses move to the stubbed store (`storeOk_stub`,
  `invokeOk_stub`, `storeWF_stub`). **`wholeRunFwd10Stub`**, `wholeRunFwd10StubT`,
  **`wholeRunFwd10StubRH`**, `wholeRunFwd10StubRHT`: the forward run at stores with host
  functions, for runs that call none.
* `HostStubWit10` (namespace `Sim10.HostStubWit`): at round 6's `hostB` the stubbed invocation
  of `add` is IL-typed, so **`wholeRunFwd10StubRH_hostB`** holds with every hypothesis
  discharged, and `stub_nonvacuous`.
* `Name10`, `Name10Store` (namespace `Sim10.Name10`): the export-name failure . The
  1.0 `$utf8` clauses are out of fuel on every non-empty list at every fuel
  (`tryClauses_utf8_ne10`), so a string is a 1.0 `name` exactly when it is empty
  (`typedV_name10_iff`), and no configuration over a store holding a function instance whose
  module exports a non-empty name is typed (`not_typed10_export_ne`, `not_typed10T_export_ne`);
  in particular silmaril's `addModule`, exporting `"add"` (`not_typed10_add_invoke`).
-/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStub.steps_stub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStub.steps_stub
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStub.step_empty_or_hostCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStub.step_empty_or_hostCall
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStub.storeOk_stub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStub.storeOk_stub
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStub.wholeRunFwd10Stub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStub.wholeRunFwd10Stub
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStub.wholeRunFwd10StubT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStub.wholeRunFwd10StubT
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStub.wholeRunFwd10StubRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStub.wholeRunFwd10StubRH
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStub.wholeRunFwd10StubRHT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStub.wholeRunFwd10StubRHT
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStubWit.wholeRunFwd10StubRH_hostB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStubWit.wholeRunFwd10StubRH_hostB
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStubWit.wholeRunFwd10StubRHT_hostB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStubWit.wholeRunFwd10StubRHT_hostB
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostStubWit.stub_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostStubWit.stub_nonvacuous
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Name10.tryClauses_utf8_ne10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Name10.tryClauses_utf8_ne10
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Name10.typedV_name10_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Name10.typedV_name10_iff
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Name10.not_typed10_export_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Name10.not_typed10_export_ne
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Name10.not_typed10T_export_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Name10.not_typed10T_export_ne
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Name10.not_typed10_add_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Name10.not_typed10_add_invoke
