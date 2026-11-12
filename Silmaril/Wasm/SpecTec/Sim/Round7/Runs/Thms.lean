module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Runs.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Runs.Pres

/-!
# SpecTec ↔ Core 3.0, round 7: runs at the round-7 reading (round 5, pass 1, proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.Runs`; see `docs/projects/spectec/README.md`.
Definitions (`RelE`, `ReachE`) are in `Round7/Runs/Defs.lean`.

* **The export swap at a witness** (`swapAt_fwd`, `swapAt_bwd`): the two halves of
  `Round7.Task.swapEquiv` hold at the image of any configuration `d` whose module instances are
  among those of a `StripInj`, `NamesBnd` configuration `c`, valid or not. The witnesses of
  `Bwd.ConfigEq` have the module instances of their source (`mods_configEq`).
* **One step along `RelE`** (`fwdRelE`, `bwdRelE`): `Round7.Task.wholeStepValidREI`'s two
  halves from every `RelE` witness, through round 6's relational steps at the stripped pair.
* **Runs** (`runsRE`): from a valid source whose reachable configurations are `BoundedSelE` and
  `StripInj` (`ReachE`), deterministic Core runs are runs of `Round7.backendE` and runs of
  `Round7.backendE` are Core runs, both up to `Bwd.ConfigEq`, at `BI (Profile.spec nd r) hn host`,
  for an injective `hn` and a finite, `HostOk`, export-blind, export-parametric host.
* **`StripInj` along deterministic steps** (`mods_sub_of_det`, `stripInj_of_det`,
  `reachE_of_det`): an only successor has no new module instances, so `ReachE` on a
  deterministic source needs `StripInj` at the source only.
* **Round 6's run domain is inside `ReachE`** (`boundedSelE_of_boundedSel`,
  `reachE_of_boundedReachSel`): export-free configurations are `BoundedSelE` and `StripInj`.

`Round7.Task.wholeStepValidREH` and `Round7.Task.wholeStepValidRE` are unchanged and still open;
these results keep `StripInj` and `HostExportParam`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Runs

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Runs.swapAt_bwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms swapAt_bwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Runs.fwdRelE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwdRelE

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Runs.bwdRelE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bwdRelE

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Runs.runsRE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runsRE

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Runs.reachE_of_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reachE_of_det

end Silmaril.Wasm.SpecTec.Sim.Round7.Runs
