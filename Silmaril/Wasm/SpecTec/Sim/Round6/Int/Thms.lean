module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Int.Assemble

/-!
# SpecTec ↔ Core 3.0, round 6, integration: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.Int`; see `docs/projects/spectec/README.md`.

* `not_wholeStepValidR_declarative`: `Round6.Task.wholeStepValidR Target.declarative` is false.
* `wholeStepValidR_backend_of_open`: `Round6.Task.wholeStepValidR backend` from
  `Target.OpenR backend` at every injective encoding, finite `HostOk` host and spec profile.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.not_wholeStepValidR_declarative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.not_wholeStepValidR_declarative

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.wholeStepValidR_backend_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.wholeStepValidR_backend_of_open
