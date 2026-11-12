module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitnessHost10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitnessExp10

/-!
# The 1.0 route, an earlier step (track v10-inst)

See `docs/projects/spectec/README.md`, "v10-inst".

* `InstHost10` (namespace `Sim10.InstH`): the instantiation route with host functions.
  **`instantiation_core10GH`**: a V1 instantiation under any V1 host with a compatibility chain
  to a Core host satisfying `HostOk` (`HostChain10`; the empty host has one) yields a valid Core
  store erasing to the image of its result, with no `NoHost10`/`StoreOk10` hypothesis on the
  store before. **`wholeRunFwd10InvGH`**, `wholeRunFwd10InvGHT`; iterated from any base store
  (`ReachH10`, which may hold host functions): **`reachH10_ok`**, **`wholeRunFwd10InvRH`**,
  `wholeRunFwd10InvRHT`; an earlier `Reach10` is `ReachH10 {}` (`reachH10_of_reach10`).
  **`noHost10_of_typed10_invoke`**, `noHost10_of_typed10T_invoke`: the forward theorems' own
  IL-typing hypothesis excludes host functions from the invoked store (the 1.0 script has no
  host function instance).
* `InstInvoke10` (namespace `Sim10.InstInvoke`): Core's `InvokeOk` from V1
  (`invokeOk_of_v1`); after preparation and after instantiation from a host-free store, the
  instance's function addresses hold functions of the validation context's types
  (`prepare?_funcs`, `instantiation_funcs`); so for every exported function
  (`instantiation_export_invokeOk`), and **`wholeRunFwd10InvRUE`**, `wholeRunFwd10InvRTUE`:
  an earlier iterated run for an exported function with no `InvokeOk` hypothesis.
* `InstWitnessHost10`: `addModule0` instantiated into a store with a host function; the
  result is reached and its Core image is valid (`coreOk_hostB`), and no invocation over it is
  IL-typed (`not_typed10_hostB`).
* `InstWitnessExp10`: a module exporting its function under the empty name; the export form
  applies (`wholeRunFwd10InvRUE_addE`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstH.instantiation_core10GH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstH.instantiation_core10GH

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstH.wholeRunFwd10InvGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstH.wholeRunFwd10InvGH

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstH.wholeRunFwd10InvGHT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstH.wholeRunFwd10InvGHT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstH.reachH10_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstH.reachH10_ok

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstH.wholeRunFwd10InvRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstH.wholeRunFwd10InvRH

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstH.wholeRunFwd10InvRHT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstH.wholeRunFwd10InvRHT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstH.reachH10_of_reach10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstH.reachH10_of_reach10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstH.noHost10_of_typed10_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstH.noHost10_of_typed10_invoke

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstH.noHost10_of_typed10T_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstH.noHost10_of_typed10T_invoke

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstInvoke.invokeOk_of_v1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstInvoke.invokeOk_of_v1

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstInvoke.prepare?_funcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstInvoke.prepare?_funcs

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstInvoke.instantiation_funcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstInvoke.instantiation_funcs

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstInvoke.instantiation_export_invokeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstInvoke.instantiation_export_invokeOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstInvoke.wholeRunFwd10InvRUE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstInvoke.wholeRunFwd10InvRUE

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstInvoke.wholeRunFwd10InvRTUE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstInvoke.wholeRunFwd10InvRTUE

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstWitnessHost10.coreOk_hostB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstWitnessHost10.coreOk_hostB

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstWitnessHost10.not_typed10_hostB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstWitnessHost10.not_typed10_hostB

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstWitnessExp10.wholeRunFwd10InvRUE_addE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstWitnessExp10.wholeRunFwd10InvRUE_addE
