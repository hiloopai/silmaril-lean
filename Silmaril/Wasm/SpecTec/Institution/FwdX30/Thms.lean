module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdX30

/-!
# The forward direction at wasm-3.0, extended: results

Namespace `Silmaril.Wasm.SpecTec.Institution.FwdX30`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{FwdX30Table,FwdX30Mem,FwdX30Agg,FwdX30Ctrl,FwdX30Vec,`
`FwdX30Leaves,FwdX30}`; see `docs/projects/spectec/README.md`, "instfwd".

At the concrete primitives `Round4Int.BI`, the model of `Cover.toModelDom`:

* `PureHeadX.step`, `ReadHeadX.step`: the classified head steps are Core steps that keep the
  state.
* `spure_of_pureHeadX`, `sread_of_readHeadX`: they are `Step_pure`/`Step_read` facts of the
  declarative reading (the forward leaves of rounds 2–5, before the lift to `Step`), the
  latter from a bounded configuration to typed code. Per family: `spure_numeric`,
  `spure_of_vector`, `sread_of_tableStep`, `sread_of_memStep`, `sread_of_aggStep`,
  `sread_of_ctrlRead`.
* `pureFactX_complete`, `readFactX_complete`, `pureFactX_dom`, `readFactX_dom`: the same facts in
  `stepModel BI`, and on round 6's domain `Wasm30.Dom` with typing proved (`readFactX_dom`
  at a `HostOk` host, for the typing of the successor).
* `pureFactX_core_complete`, `readFactX_core_complete`: on `Dom`, Core's successor is an
  observation, its image is the `Step_pure` (`Step_read`) fact, lifted to `Step`.
* `pureFactX_sound`, `readFactX_sound`: on `Dom`, every such fact to typed code is a Core
  successor up to `CfgRel`; `pureFactX_unique`, `readFactX_unique`: on `DomDet`, the classified
  one.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30.pureFactX_core_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30.pureFactX_core_complete

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30.readFactX_core_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30.readFactX_core_complete

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30.pureFactX_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30.pureFactX_unique

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30.readFactX_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30.readFactX_unique

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30.pureFactX_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30.pureFactX_sound

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdX30.readFactX_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdX30.readFactX_sound
