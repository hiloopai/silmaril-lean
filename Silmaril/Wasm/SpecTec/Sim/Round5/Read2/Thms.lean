module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Read2.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Read2.Assemble

/-!
# SpecTec ↔ Core 3.0, round 5, pass 3, track read: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Read2`; see `docs/projects/spectec/README.md`.

* `read_done2`: `Step_read` 39, 41, 69, 71, 76, 79, 91, 92 and 102, backward, for the concrete
  builtins, under `Round5.Read.ReadValidS`.
* `readRest`: pass 2's `Round5.Read.ReadRest` holds (`readDone2_covers`).
* `open2_of_open3`, `open3_of_open2`, `wholeStepValidOk_of_open3`, `multiOk2_of_open3`,
  `runs_of_open3`: the restated target and the multi-step corollaries from `Open3`, pass 2's
  `Round5.Int2.Open2` without its `read` leaf.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read2.read_done2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Read2.read_done2

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read2.readRest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Read2.readRest

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read2.runs_of_open3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Read2.runs_of_open3

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read2.wholeStepValidOk_of_open3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.Read2.wholeStepValidOk_of_open3

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read2.multiOk2_of_open3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Read2.multiOk2_of_open3
