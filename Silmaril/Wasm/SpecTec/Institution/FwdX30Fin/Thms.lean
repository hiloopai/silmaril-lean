module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdX30Fin

/-!
# The forward direction at wasm-3.0, finished: results

Namespace `Silmaril.Wasm.SpecTec.Institution.FwdX30Fin`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{FwdX30FinLeaves,FwdX30Fin}`; see
`docs/projects/wasm-components.md`, "Stretch, instfwd2".

With `FwdX30`, this covers all 99 Core constructors labelled `Step_read`.

At the concrete primitives `Round4Int.BI`, the model of `Cover.toModelDom`:

* `sreadB_of_castRead`: the eight cast rules (`CastRead`) are `Step_read` facts of the backend
  reading, 's cast leaf before the lift;
* `sreadB_retFrameAddr`: `return_call_ref` out of a frame at an address (`RetFrameAddr`) is a
  `Step_read` fact up to `ConfigEq` (to SpecTec's code, with the `CALL_REF` index kept);
* `readFactCast_complete`/`_dom`/`_core_complete`/`_unique` and the `readFactRet_` versions, in
  the shape of `FwdX30.readFactX_*`.

At the choice-made primitives `Wasm30.builtins`, the target of `Wasm30.toModel`:

* `sat_builtins_iff_BI`: on `DomDet` the two models satisfy the same `CfgRel`-respecting
  sentences;
* `stepObs_builtins`, `pureFactX_builtins`, `readFactX_builtins`, `readFactCast_builtins`,
  `readFactRet_builtins`: at each classified redex, the `Step` observations of
  `stepModel builtins` are the classified successor up to `CfgRel`, next to the
  `Step_pure`/`Step_read` fact at `BI`;
* `pureFact_unique_builtins`, `readFact_unique_builtins`: every `Step_pure`/`Step_read` fact of
  `stepModel builtins` to typed code is that successor up to `CfgRel`. Their existence at
  `builtins` is not proved: `builtins` is a `Classical.choose`, and nothing is known of its
  primitives.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.sreadB_of_castRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.sreadB_of_castRead

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.sreadB_retFrameAddr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.sreadB_retFrameAddr

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.readFactCast_core_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.readFactCast_core_complete

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.readFactRet_core_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.readFactRet_core_complete

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.readFactCast_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.readFactCast_unique

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.readFactRet_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.readFactRet_unique

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.sat_builtins_iff_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.sat_builtins_iff_BI

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.pureFactX_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.pureFactX_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.readFactX_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.readFactX_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.readFactCast_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.readFactCast_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.readFactRet_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.readFactRet_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.pureFact_unique_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.pureFact_unique_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.readFact_unique_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30Fin.readFact_unique_builtins
