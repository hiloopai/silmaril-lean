module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostMods.Reach

/-!
# SpecTec ↔ Core 3.0, REI without `HostExportParam` (proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.HostMods`; see `docs/projects/spectec/README.md`, "re
". Definitions (`HostModsSub`, `HostModMapAt`, `StepValidREM`) are in
`Round7/HostMods/Defs.lean`.

* **`stepValidREM_holds`**: `Round7.Task.wholeStepValidREI` holds with `HostModsSub` (the host
  returns only module instances of the calling store) in place of `HostExportParam`. It implies
  the old statement (`wholeStepValidREI_of_REM`, via `hostModsSub_of_param`).
* **Core side**: `step_mapConfigAt` (unrefined copy of `Round7.step_mapConfig` with a
  store-local host hypothesis), `step_unstripM`, `unstrip_strip_succM`.
* **SpecTec side**: `ruleFwd_hostM`, `ruleBwd_hostM` (unrefined copies of
  `Round7.EraseDer.ruleFwd_host`/`ruleBwd_host`), `excRules_QCM`, `swapAt_fwdM`, `swapAt_bwdM`.
* **Runs**: `runsREM`, `fwdRelEM`, `bwdRelEM`, and `reachE_of_detM` (`StripInj` along
  deterministic steps).
* **Every run**: a Core step introduces no module instance (`mods_step_sub`, unrefined), so
  `StripInj` and `NamesBnd` hold along every run from a source that has them (`stripInj_steps`,
  `namesBnd_steps`), and `ReachE`/`RunDomE` need them only at the source (`reachE_of_stripInj`,
  `runDomE_of_stripInj`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostMods

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.step_mapConfigAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_mapConfigAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.ruleFwd_hostM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleFwd_hostM

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.ruleBwd_hostM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleBwd_hostM

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.stepValidREM_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepValidREM_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.wholeStepValidREI_of_REM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidREI_of_REM

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.runsREM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runsREM

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.reachE_of_detM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reachE_of_detM

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.mods_step_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mods_step_sub

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.reachE_of_stripInj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reachE_of_stripInj

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.runDomE_of_stripInj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runDomE_of_stripInj

end Silmaril.Wasm.SpecTec.Sim.Round7.HostMods
