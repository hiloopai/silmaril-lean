module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi4.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi4.WitnessBnd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi4.Assemble

/-!
# SpecTec ↔ Core 3.0, round 5, track multi (pass 4): what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Multi`; see `docs/projects/spectec/README.md`.

* `witnessBnd`: `Int2.WitnessBnd B hn` holds for every `B` and encoding, through
  `tyBnd_of_tyI` (the converse of `tyT_tyV`, by induction on Core's `Ty`),
  `listT_inv` (`list(X)` inverted) and `tyBnd_of_callRef`. With `Multi.succTyped`
  (`Round5/Multi/Thms.lean`), the backward multi-step relation needs no hypothesis beyond the
  one-step backward direction's.
* `bwdRel_of_partsOkS`, `bwdRel_of_open2`, `runs_of_open2`, `runs_of_open4`,
  `multiOk3_of_multiOk2`, `multiOk3_of_multiOk`, `multiOk3_of_open4`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.tyBnd_of_tyI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.tyBnd_of_tyI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.witnessBnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.witnessBnd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.bwdRel_of_partsOkS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.bwdRel_of_partsOkS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.multiOk3_of_multiOk2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.multiOk3_of_multiOk2

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.runs_of_open4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.runs_of_open4
