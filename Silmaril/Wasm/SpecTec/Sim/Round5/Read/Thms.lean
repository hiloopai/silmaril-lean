module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Read.Assemble

/-!
# SpecTec ↔ Core 3.0, round 5, pass 2, track read: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Read`; see `docs/projects/spectec/README.md`.

* `readValidS_of_bounded`, `readValidS_ctxClosed`: a valid, bounded configuration satisfies
  `ReadValidS` (`ReadValidR`, the aggregate segment indices resolve, bounded active code), and
  `ReadValidS` survives the context decompositions.
* `read_doneS`: `Step_read` 42–51 (vacuously), 72, 74, 75, 85, 90, 96, 97, 100 and 101, backward,
  for the concrete builtins.
* `read_doneK`: `Step_read` 2–5 and 65–68 (the casts), backward, from `Fwd.RefOkB`.
* `lt_of_fires_read`: no `Step_read` rule has index `≥ 103`.
* `readOpenS_of_rest`, `readOpenS_of_readOpen`: `ReadOpenS` from `Fwd.RefOkB` and what is left
  (`ReadRest`); pass 1's `ReadOpen` implies it.
* `wholeStepValidOk_of_partsOkS`, `wholeStepValidOk_of_openS`: `Round5.Task.wholeStepValidOk`
  from the restated reductions; `partsOkS_of_partsOkR`, `openS_of_open`: they ask no more than
  pass 1's.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read.readValidS_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Read.readValidS_of_bounded

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read.read_doneS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Read.read_doneS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read.wholeStepValidOk_of_openS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.Read.wholeStepValidOk_of_openS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read.openS_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Read.openS_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read.read_doneK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Read.read_doneK

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Read.lt_of_fires_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Read.lt_of_fires_read
