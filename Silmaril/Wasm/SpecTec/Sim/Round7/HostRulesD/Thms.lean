module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostRulesD.Bwd

/-!
# Round 7, `BD`: the host-call rules at `configVD`, both directions

Round 5, pass 1 proved that `BM` (the builtins of `Round7.Task.wholeStepValidRM`'s reduction)
answers no `$hostcall` made from a `storeVD` image of a store with memory SIMD code
(`MSPres.bm_hostcall_none`). Pass 2 defined `HostD.BD`, whose `$hostcall` is keyed on `storeVD`
images. Here Core's two host-call steps and SpecTec's `Step` rules 8 and 9 correspond between
`configVD` images at `BD`, for every store, memory SIMD code included:

* forward: `fwd_callRefHostD` (`call_ref` into a host function that returns, rule 8) and
  `fwd_callRefHostDivD` (one that diverges, rule 9), for typed images and a bounded callee type;
* backward: `bwd_callRefHostD`, `bwd_callRefHostDivD`: a firing of rule 8 or 9 from the `configVD`
  image of a configuration with a typed image is the image of a Core host-call step
  (`MemSimd.BwdUpToD`); `hostStepsD` packages both as the rule-8/9 obligations of round 7's
  dispatch at `simEnv (BD …)`.

All assume an injective `hn` and a finite host. The `$unrolldt`/`Expand` facts are restated at
`BD` (`applies_unrolldtD`, `dderives_expandD`, `callTypesD`, `expand_of_dderivesD`, `callInvD`),
and the left-hand side is decoded at `configVD` (`hostLhsD_of`).

**Not covered.** `OpenRMRest` at `BD`: the other fields (`typed`, `rest`, the memory SIMD rules
`readMSD`/`stepMSD`) are proved or stated at `BM`, and moving them needs either restatements or
a declarative transfer for builtins that agree off `$hostcall`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD.fwd_callRefHostD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms fwd_callRefHostD

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD.fwd_callRefHostDivD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms fwd_callRefHostDivD

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD.hostStepsD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hostStepsD

end Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD
