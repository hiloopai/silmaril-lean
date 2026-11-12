module

public import Silmaril.Wasm.Atlas.SpecTecR7Runs.Defs
public import Silmaril.Wasm.Atlas.SpecTecR6.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Runs.Thms

/-!
# The SpecTec run charts at the round-7 reading: transitions

`Round7.Runs.runsRE` wired into the atlas, at `Profile.spec nd r`, an injective `hn`, a finite,
`HostOk`, export-blind (`HostExportBlind`) and export-parametric (`HostExportParam`) host, and the
concrete builtins `BI := Round4Int.BI (Profile.spec nd r) hn host`. Runs
(`SpecTecR6.runChart … RunDomE` → `SpecTecR6.readRunChart Round7.backendE BI`):

* `toBackendERunsUniv`: from `runsRE`'s backward half, Core's universal `CfgRel`-respecting
  reachability sentences hold of the round-7 reading's runs (direction `preserves`).
* `toBackendERunsDet`: on `RunDomDetE` every Core run is deterministic, so `runsRE`'s forward half
  applies and the run transition is **equal** on `CfgRel`-respecting sentences
  (`sat_iff_backendE_runs_det`).
* `runDomDetE_of`: on a source whose reachable configurations are `BoundedSelE` and have at most
  one successor, `StripInj` at the source is enough (`Round7.Runs.reachE_of_det`).
* `runDomE_of_runDom`, `runDomDetE_of_runDomDet`: round 6's run domains (`SpecTecR6.RunDom`,
  `RunDomDet`, export-free) are inside these, so the round-7 run charts extend round 6's.

Still restricted: `StripInj` and `HostExportParam` are hypotheses, as in `Atlas.SpecTecR7U`.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecR7Runs

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec
open Silmaril.Wasm.Atlas.SpecTecR6 (runChart readRunChart runObs readRunObs StepDet)

variable {H : Type} {hn : H → String} {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}

theorem runsE_bwd_upto (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) (c : Config H)
    (hc : RunDomE (Profile.spec nd r) host c) (u : Unit) :
    ∀ b' ∈ readRunObs Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
        (Sim.configV hn c) u,
      ∃ b ∈ runObs (Profile.spec nd r) host hn c u, SpecTec.CfgRel hn b b' := by
  intro w hw
  obtain ⟨ts, hok⟩ := hc.1
  obtain ⟨c', d', he, rfl, hs⟩ := (Sim.Round7.Runs.runsRE hinj hf hh hb hp).2 c ts w hok hc.2 hw
  exact ⟨_, ⟨c', hs, rfl⟩, c', d', he, rfl, rfl⟩

theorem runsE_fwd_upto_det (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) (c : Config H)
    (hc : RunDomDetE (Profile.spec nd r) host c) (u : Unit) :
    ∀ b ∈ runObs (Profile.spec nd r) host hn c u,
      ∃ b' ∈ readRunObs Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
        (Sim.configV hn c) u, SpecTec.CfgRel hn b b' := by
  rintro b ⟨c', hs, rfl⟩
  obtain ⟨ts, hok⟩ := hc.1.1
  obtain ⟨d, he, hrun⟩ := (Sim.Round7.Runs.runsRE hinj hf hh hb hp).1 c c' ts hok hc.1.2
    (SpecTecR6.detSteps_of_steps hs hc.2)
  exact ⟨_, hrun, c', d, he, rfl, rfl⟩

/-- **Core runs → round-7 runs, universal**: Core's universal respecting reachability sentences
hold of the round-7 reading's runs, from every source in `RunDomE`. -/
noncomputable def toBackendERunsUniv (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    Transition (runChart (Profile.spec nd r) host hn (RunDomE (Profile.spec nd r) host))
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofSupUpToUniv (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (runsE_bwd_upto hinj hf hh hb hp)

/-- **Core runs ↔ round-7 runs on deterministic sources**: equal on every `CfgRel`-respecting
reachability sentence. -/
noncomputable def toBackendERunsDet (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    Transition (runChart (Profile.spec nd r) host hn (RunDomDetE (Profile.spec nd r) host))
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofUpTo (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (runsE_fwd_upto_det hinj hf hh hb hp) (fun c hc => runsE_bwd_upto hinj hf hh hb hp c hc.1)

theorem toBackendERunsDet_dir (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    (toBackendERunsDet (nd := nd) (r := r) hinj hf hh hb hp).dir = .equal := rfl

/-- **The round-7 run theorem, stated directly**: from a valid source whose reachable
configurations are all `BoundedSelE`, `StripInj` and have at most one Core successor, a
`CfgRel`-respecting reachability sentence holds in Core iff it holds of the image under the runs
of `Step` in `utf8Env BI`. -/
theorem sat_iff_backendE_runs_det (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) {c : Config H}
    (hc : RunDomDetE (Profile.spec nd r) host c) {s : BSen Unit Value}
    (hs : s.Respects (SpecTec.CfgRel hn)) :
    (runChart (Profile.spec nd r) host hn (RunDomDetE (Profile.spec nd r) host)).Sat c s ↔
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  by simpa only [toBackendERunsDet, BTrans.ofUpTo, BSen.rename_id] using
    (toBackendERunsDet hinj hf hh hb hp).sat_iff rfl hc hs

/-- **`RunDomDetE` from `StripInj` at the source**: on a valid source whose reachable
configurations are `BoundedSelE` and have at most one Core successor. -/
theorem runDomDetE_of {P : Profile} (hp : Sim.Round7.HostExportParam host) {c : Config H}
    {ts : List CValType} (hok : ConfigOk c ts) (hi : Sim.Round7.StripInj c)
    (hb : ∀ c', Steps P host c c' → Sim.Round7.BoundedSelE c')
    (hd : ∀ c', Steps P host c c' → StepDet P host c') : RunDomDetE P host c :=
  ⟨⟨⟨ts, hok⟩, Sim.Round7.Runs.reachE_of_det hp hi hb hd⟩, hd⟩

/-- **Round 6's run domain is inside round 7's**: the round-7 run charts extend round 6's. -/
theorem runDomE_of_runDom {P : Profile} {c : Config H} (h : SpecTecR6.RunDom P host c) :
    RunDomE P host c :=
  ⟨h.1, Sim.Round7.Runs.reachE_of_boundedReachSel h.2⟩

theorem runDomDetE_of_runDomDet {P : Profile} {c : Config H} (h : SpecTecR6.RunDomDet P host c) :
    RunDomDetE P host c :=
  ⟨runDomE_of_runDom h.1, h.2⟩

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7Runs.sat_iff_backendE_runs_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backendE_runs_det

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7Runs.runDomDetE_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runDomDetE_of

end Silmaril.Wasm.Atlas.SpecTecR7Runs
