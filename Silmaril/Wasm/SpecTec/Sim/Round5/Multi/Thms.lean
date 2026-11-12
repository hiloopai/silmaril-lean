module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi.Respect
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi.Eq
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi.Runs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi.SuccCalls

/-!
# SpecTec ↔ Core 3.0, round 5, track multi: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Multi`; see `docs/projects/spectec/README.md`.

* `fwdResp_of_step`: SpecTec respects `ConfigEq` along every Core step from a bounded source,
  for the concrete `B`, from `Obl`.
* `configEq_trans`, `readValidR_of_configEq`, `typed_of_configEq`, `succTyped_of_calls`.
* `fwdRel_of_obl`, `fwdRel_of_open`; `bwdRel_of_partsOkR`, `bwdRel_of_open` (under
  `SuccTyped`).
* `steps_sim`, `ssteps_sim`, `vals_iff`: the run corollaries along `SimRel`.
* `multiOk_of_open`, `runs_of_open`: from `Int.Open`.
* Pass 4 (`SuccCalls.lean`): `succCallsTyped`, `succTyped`: `SuccCallsTyped B hn` and
  `SuccTyped B hn` hold for every `B` and encoding, by one syntactic check (`chk`, `succRule`)
  over the 36 rules of `Step`, run by `rfl` (`stepRules_checked`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.fwdResp_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.fwdResp_of_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.succTyped_of_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.succTyped_of_calls

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.bwdRel_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.bwdRel_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.vals_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.vals_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.multiOk_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.multiOk_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.runs_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.runs_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.succCallsTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.succCallsTyped

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Multi.succTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Multi.succTyped
