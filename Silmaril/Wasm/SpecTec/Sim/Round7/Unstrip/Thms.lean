module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Unstrip.Assemble

/-!
# SpecTec ↔ Core 3.0, round 7: un-stripping exports (pass 6, proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7`; see `docs/projects/spectec/README.md`.
Definitions are in `Round7/Unstrip/Defs.lean`.

* **Core's `Step` commutes with export-only rewritings** (`step_mapConfig`): for `ExportOnly μ`
  and a host invariant under `μ` (`HostModMap host μ`), `c → c'` gives
  `mapConfig μ c → mapConfig μ c'`. Unlike `exRel_step` it names the successor.
* **Un-stripping**: `exportOnly_unstrip`, `unstrip_strip` and `mapConfig_unstrip_strip`
  (`mapConfig (unstrip c) (stripConfig c) = c` under `StripInj c`), `mapConfig_stripModule`
  (`stripConfig` is `mapConfig stripModule`), `configEq_map`, `stripped_of_configEq`.
* **The side condition holds** on export-free configurations (`stripInj_of_stripped`) and on
  configurations whose module instances are all one module, exports included
  (`stripInj_of_single`).
* **The reduction**: `step_unstrip`, `unstrip_strip_succ`, `fwdREI_of_leaves`,
  `bwdREI_of_leaves` and `wholeStepValidREI_of_leaves : Task.swapEquiv → Task.envAgreeNE →
  Task.wholeStepValidREI`, with `B := BI (Profile.spec nd r) hn host`.
* `wholeStepValidREI_of_REH`: the new target is weaker than `Task.wholeStepValidREH`.
  `hostExportParam_divHost`: its new host hypothesis is satisfiable.

**Open:** the two leaves `Task.swapEquiv` and `Task.envAgreeNE` (frozen), hence
`Task.wholeStepValidREI`; and `Task.wholeStepValidREH` and `Task.wholeStepValidRE` without the
side condition.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.step_mapConfig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.step_mapConfig

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.mapConfig_unstrip_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.mapConfig_unstrip_strip

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.wholeStepValidREI_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.wholeStepValidREI_of_leaves

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.wholeStepValidREI_of_REH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.wholeStepValidREI_of_REH

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.stripInj_of_single' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.stripInj_of_single
