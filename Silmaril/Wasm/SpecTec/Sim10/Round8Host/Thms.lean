module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostImplWitE10

/-!
# The 1.0 route with runs that call host functions, round 8 (track v10-host)

See `docs/projects/spectec/README.md`, "v10-host".

* `HostImpl10`, `HostImplCore10` (namespace `Sim10.HostRead`): a host function instance
  `.host t h` is read in the 1.0 IL as its **implementation**, the defined function
  `implF ι (.host t h) = .wasm t (stubMod t) (ι h)` in a closed module instance. Round 7's stub
  is the constant implementation `FUNC 0 [] [UNREACHABLE]` (`stubF_eq_implF`). Under the V1
  obligation `HostImpl ι σ host` (every host return is matched by a V1 run of the implementing
  code under the empty host), every V1 run, host calls included, is a run under the empty host
  between the implemented configurations (`steps_impl`), and so a run of the 1.0 script
  (**`wholeRunFwd10Impl`**, `wholeRunFwd10ImplT`, `wholeRunFwd10ImplRH`, `wholeRunFwd10ImplRHT`).
  Limit: a host with an implementation keeps the function list (`hostImpl_funcs`).
  `wholeRunFwd10InvRHV`, `wholeRunFwd10InvRHVT`: round 6's `ReachH10` forms with V1 data in
  place of Core's `InvokeOk`.
* `HostImplInst10`: Core's `InvokeOk` for exported functions from V1 validation at stores with
  host functions (`instantiation_export_invokeOkH`), and the forward run from instantiation with
  no Core hypothesis on the invocation (**`wholeRunFwd10ImplRHE`**, `wholeRunFwd10ImplRHET`).
* `HostImplWit10` (namespace `Sim10.HostReadWit`): at round 6's `hostB`, a V1 run that calls
  the host function under `noopHost` is a run of the 1.0 script (**`hostCall_run10`**). Round 7's
  stub implements exactly the trapping hosts it is shown to (`hostImpl_stub`,
  `wholeRunFwd10StubTrap`). A host that allocates a function has no implementation
  (**`not_hostImpl_alloc`**).
* `HostImplWitE10` (namespace `Sim10.HostReadWitE`): a module re-exporting the host function,
  instantiated into `hostBase`; the call of the export is a host call and a run of the 1.0
  script, from V1 instantiation and validation only (**`exportHostCall_run10`**).
-/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.steps_impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.steps_impl
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.step_impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.step_impl
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.stubF_eq_implF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.stubF_eq_implF
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.hostImpl_funcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.hostImpl_funcs
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.hostImpl_funcs_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.hostImpl_funcs_length
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.storeOk_impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.storeOk_impl
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10Impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10Impl
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplT
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplRH
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplRHT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplRHT
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10InvRHV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10InvRHV
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10InvRHVT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10InvRHVT
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.instantiation_funcsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.instantiation_funcsH
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.instantiation_export_invokeOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.instantiation_export_invokeOkH
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplRHE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplRHE
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplRHET' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostRead.wholeRunFwd10ImplRHET
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWit.hostImpl_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWit.hostImpl_noop
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWit.implOk_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWit.implOk_noop
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWit.wholeRunFwd10ImplRH_hostB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWit.wholeRunFwd10ImplRH_hostB
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWit.wholeRunFwd10ImplRHT_hostB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWit.wholeRunFwd10ImplRHT_hostB
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWit.hostCall_run10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWit.hostCall_run10
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWit.hostImpl_stub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWit.hostImpl_stub
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWit.wholeRunFwd10StubTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWit.wholeRunFwd10StubTrap
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWit.not_hostImpl_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWit.not_hostImpl_alloc
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWitE.reexModule_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWitE.reexModule_valid
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWitE.wholeRunFwd10ImplRHE_reex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWitE.wholeRunFwd10ImplRHE_reex
/-- info: 'Silmaril.Wasm.SpecTec.Sim10.HostReadWitE.exportHostCall_run10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.HostReadWitE.exportHostCall_run10
