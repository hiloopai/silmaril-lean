module

public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Wasm30Rel
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Wasm30

/-!
# The SpecTec specification institution and the Wasm atlas, at wasm-3.0: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Wasm30`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.Wasm30`; see `docs/projects/spectec/README.md`, §4.

* `modelChart_canon`: the step chart of the declarative canonical model
  `canon env (otherwise env)` is `Atlas.SpecTec.specChart env` (by `rfl`).
* `stepModel_facts`: `Round6.Int.wholeStepValidR_backend`, restated for the step facts of the
  backend canonical model `stepModel B`.
* `toModel`: the semi-comorphism, a transition from the Core step chart on `DomDet` (valid,
  `BoundedSel`, `BoundedSel` successors, at most one successor) to `modelChart (stepModel B)`,
  equal on `CfgRel`-respecting sentences; `sat_iff_stepModel` states it directly.
* `pureFact_sound`, `readFact_sound` (`Silmaril.Proofs.Wasm.SpecTec.Institution.Wasm30Rel`): the
  backward half for `Step_pure` and `Step_read` facts of `stepModel B` at typed results, through
  the script's `Step/pure` and `Step/read` rules; `pureFact_core`, `readFact_core` on `DomDet`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm30.stepModel_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm30.stepModel_facts

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm30.sat_iff_stepModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm30.sat_iff_stepModel

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm30.pureFact_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm30.pureFact_sound

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm30.readFact_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm30.readFact_sound
