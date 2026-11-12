module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int4.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Int4.Assemble

/-!
# SpecTec ↔ Core 3.0, round 5, pass-4 integration: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Int4`; see `docs/projects/spectec/README.md`.

* `bwdRelSel_of_partsSel`: the backward relation on `FloatMissel`-free sources from
  `Target.PartsSel` alone (`succTyped`, `witnessBnd` plugged into track target's
  reduction);
* `bwdRelSel_of_open5`, `multiSel3_of_multiSel`, `multiSel3_of_open5`, `runsSel_of_open5`: the
  run corollaries of `Task.wholeStepValidSel` with no hypothesis on the backward half. The
  `Open5` forms are vacuous (`Target.not_open5_spec`; also `RefOk.not_refOkB`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int4.bwdRelSel_of_partsSel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int4.bwdRelSel_of_partsSel

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int4.multiSel3_of_open5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int4.multiSel3_of_open5

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int4.runsSel_of_open5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int4.runsSel_of_open5
