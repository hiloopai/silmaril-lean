module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Int2.Assemble
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Int2.Multi

/-!
# SpecTec ↔ Core 3.0, round 5, pass-2 integration: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Int2`; see `docs/projects/spectec/README.md`.

* `wholeStepValidOk_of_open2`: the restated target `Round5.Task.wholeStepValidOk` from `Open2`,
  the leaves still open after pass 2 (`partsOkS_of_open2`). `open2_of_openT`: `Open2` asks no
  more than `OpenT`.
* `fwdRel_of_open2`, `bwdRel_of_open2`, `multiOk2_of_open2`, `runs_of_open2`: the multi-step
  corollary from `Open2`. The forward half needs nothing more. The backward half also needs
  `Multi.SuccTyped` and `WitnessBnd`.
* `Multi.fwdResp_of_step_host`: `fwdResp_of_step` with the host `call_ref` rules as
  a hypothesis (`Multi.HostCallsFwd`), so that it also applies under `HostRespectsT`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int2.wholeStepValidOk_of_open2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.Int2.wholeStepValidOk_of_open2

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int2.partsOkS_of_open2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int2.partsOkS_of_open2

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int2.open2_of_openT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int2.open2_of_openT

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int2.fwdRel_of_open2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int2.fwdRel_of_open2

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int2.bwdRel_of_open2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int2.bwdRel_of_open2

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int2.multiOk2_of_open2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int2.multiOk2_of_open2

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int2.runs_of_open2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int2.runs_of_open2

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.fwdResp_of_step_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.fwdResp_of_step_host
