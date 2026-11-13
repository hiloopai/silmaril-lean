module

public import Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.CoreStrip.Assemble
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.CoreStrip.Stripped

/-!
# SpecTec ↔ Core 3.0, the Core side of RE without `StripInj` or `HostExportBlind`

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip`; see `docs/projects/spectec/README.md`, "Round 9,
re-core". Definitions are in `Round9/CoreStrip/Defs.lean`.

* **The replacement for `HostExportBlind`**: round 6 is run at `stripConfig c` with the host
  `stripHostAt host c.store`, which answers at the stripped store the stripped outcomes of
  `host` at `c.store`. It is finite and `HostOk` (`stripHostAt_finite`, `stripHostAt_ok`), and
  equal to `host` when `host` is export-blind (`stripHostAt_of_blind`).
* **The Core side without `StripInj`**: `exRel_step₂` (`ExRel` is a simulation between two hosts
  related at one store, unrefined), `stripped_stepAt` (unrefined), and the stripping lemmas at the
  stripped host, `step_stripAt` and `step_of_stripAt`.
* **RE up to export lists**: `stepValidREX_of_leaves`, from the SpecTec leaves `EraseFwdAt` and
  `EraseBwdAt` alone.
* **RE and REH**: `wholeStepValidRE_of_leaves` (from `LeavesRE`: the two SpecTec leaves and the
  export leaf `ExactAt`), `wholeStepValidREH_of_leaves` (from `LeavesREH`).
* **Where the leaves stand**: `eraseFwdAt_of_blind` (at export-blind hosts, the forward leaf
  from `ElseBwd.BadFwdE` and `ElseBwd.ElseBwdBLeft''`), `eraseBwdAt_blind_iff` (the backward leaf
  at one set of builtins), `exactAt_of_REM` (the export leaf on the domain of
  `Round7.HostMods.StepValidREM`), `leavesAt_stripped` (all three leaves at an export-free
  configuration, for an export-blind host: round 6's domain).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.exRel_step₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exRel_step₂

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.stripped_stepAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stripped_stepAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.stripHostAt_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stripHostAt_ok

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.stripHostAt_of_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stripHostAt_of_blind

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.step_of_stripAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_of_stripAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.stepValidREX_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepValidREX_of_leaves

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.wholeStepValidRE_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRE_of_leaves

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.wholeStepValidREH_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidREH_of_leaves

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.eraseFwdAt_of_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseFwdAt_of_blind

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.exactAt_of_REM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exactAt_of_REM

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.leavesAt_stripped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms leavesAt_stripped

end Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip
