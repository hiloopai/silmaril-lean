module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Strip.Core
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Strip.Domain

/-!
# SpecTec ↔ Core 3.0, round 7: Core's `Step` up to export lists (proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7`; see `docs/projects/spectec/README.md`.
Definitions (`stripFrame`, `stripAdmins`, `stripConfig`, `ExRel`, `Stripped`) are in
`Round7/Utf8/Defs.lean`, next to `stripStore` and `HostExportBlind`.

* `exRel_step`: **agreement up to export lists is a simulation of `Step`** for export-blind
  hosts: a step from `c` is matched, from any `d` with `ExRel c d`, by a step to a configuration
  related to the successor. `ExRel` is symmetric, so this is a bisimulation.
* `stripped_step`: steps from export-free configurations stay export-free.
* **The Core stripping lemmas**: `step_strip` (`c → c'` gives `stripConfig c → stripConfig c'`)
  and `step_of_strip` (every step from `stripConfig c` comes from a step of `c`).

* **The round-6 domain at stripped configurations**: `configOk_strip` (Core typing survives
  removing exports) and `boundedSel_strip` (round 7's `BoundedSelE` maps into round 6's
  `BoundedSel`, with `noExports_strip`).

These are the Core half of the export-stripping route to `Round7.Task.wholeStepValidREH`. The
SpecTec half (stripping `SStepB` derivations, and agreement of `utf8Env B` with `simEnv B` at
export-free images, including the negative `otherwise` premises) is not formalised.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.exRel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.exRel_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.stripped_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.stripped_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.step_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.step_strip

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.configOk_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.configOk_strip

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.boundedSel_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.boundedSel_strip

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.step_of_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.step_of_strip
