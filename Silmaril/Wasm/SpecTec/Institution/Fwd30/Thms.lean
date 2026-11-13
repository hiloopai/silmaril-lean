module

public import Silmaril.Wasm.SpecTec.Institution.Fwd30.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Fwd30

/-!
# The forward direction for `Step_pure` and `Step_read`, at wasm-3.0: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Fwd30`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{Fwd30Leaves,Fwd30}`; see `docs/projects/spectec/README.md`,
"fwdinst".

* `PureHead.step`, `ReadHead.step`: the classified head steps are Core steps that keep the
  state.
* `spure_of_pureHead`, `sread_of_readHead`: they are `Step_pure`/`Step_read` facts of the
  declarative reading at every `B`.
* `pureFact_complete`, `readFact_complete`: the same facts in `stepModel B`;
  `pureFact_fwd`, `readFact_fwd`: on round 6's domain `Wasm30.Dom`, with typing proved.
* `pureFact_core_complete`, `readFact_core_complete`: on `Wasm30.DomDet`, through
  `Wasm30.toModel`, Core's successor is an observation whose image is the `Step_pure`
  (`Step_read`) fact, lifted to `Step` by `Step/pure` (`Step/read`).
* `pureFact_unique`, `readFact_unique`: with the sound direction (`Wasm30.pureFact_core`,
  `Wasm30.readFact_core`), every `Step_pure` (`Step_read`) fact from such a redex to typed code is
  that successor up to `CfgRel`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Fwd30.pureFact_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fwd30.pureFact_fwd

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Fwd30.readFact_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fwd30.readFact_fwd

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Fwd30.pureFact_core_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fwd30.pureFact_core_complete

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Fwd30.readFact_core_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fwd30.readFact_core_complete

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Fwd30.pureFact_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fwd30.pureFact_unique

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Fwd30.readFact_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fwd30.readFact_unique
