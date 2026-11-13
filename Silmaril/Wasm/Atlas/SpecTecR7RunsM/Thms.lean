module

public import Silmaril.Wasm.Atlas.SpecTecR7RunsM.Defs
public import Silmaril.Wasm.Atlas.SpecTecR7Runs.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.Thms

/-!
# The SpecTec run charts at the round-7 reading, with `HostModsSub`: transitions

`Atlas.SpecTecR7Runs`'s run transitions restated with `Round7.HostMods.HostModsSub` (the host
returns only module instances of the calling store) in place of `HostExportParam`, from
`Round7.HostMods.runsREM`. The host is finite, `HostOk` and export-blind (`HostExportBlind`); `hn`
is injective; the builtins are `BI := Round4Int.BI (Profile.spec nd r) hn host`.

* `toBackendERunsUnivM` (direction `preserves`) on `RunDomE`, and `toBackendERunsDetM` (direction
  `equal`) on `RunDomDetE`, with `sat_iff_backendE_runs_detM`.
* The same transitions on the source-only domains `RunSrcE` and `RunSrcDetE`
  (`toBackendERunsSrcUniv`, `toBackendERunsSrcDet`, `sat_iff_backendE_runs_src`). There
  `StripInj` and `NamesBnd` are asked of the source only, and determinism is not needed for them.
* `runDomE_of_src`, `runDomDetE_of_srcDet`: the source-only domains are inside the old ones.
* `sat_iff_backendE_runs_det_of_param`: the old run theorem
  (`Atlas.SpecTecR7Runs.sat_iff_backendE_runs_det`) is the special case
  `HostModsSub := hostModsSub_of_param`.

`Round7.HostStrict` gives a host for which these charts apply and the old ones do not.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecR7RunsM

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec
open Silmaril.Wasm.Atlas.SpecTecR6 (runChart readRunChart runObs readRunObs StepDet)
open Silmaril.Wasm.Atlas.SpecTecR7Runs (RunDomE RunDomDetE)
open Silmaril.Wasm.SpecTec.Sim.Round7.HostMods (HostModsSub)

variable {H : Type} {hn : H → String} {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}

/-! ## The source-only domains -/

/-- **`RunSrcE` is inside `RunDomE`**, for a host that invents no module. -/
theorem runDomE_of_src {P : Profile} (hm : HostModsSub host) {c : Config H}
    (h : RunSrcE P host c) : RunDomE P host c :=
  ⟨h.1, Sim.Round7.HostMods.reachE_of_stripInj hm h.2.1 h.2.2.1 h.2.2.2⟩

theorem runDomDetE_of_srcDet {P : Profile} (hm : HostModsSub host) {c : Config H}
    (h : RunSrcDetE P host c) : RunDomDetE P host c :=
  ⟨runDomE_of_src hm h.1, h.2⟩

/-! ## The two halves, along `runsREM` -/

theorem runsEM_bwd_upto (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host)
    (c : Config H) (hc : RunDomE (Profile.spec nd r) host c) (u : Unit) :
    ∀ b' ∈ readRunObs Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
        (Sim.configV hn c) u,
      ∃ b ∈ runObs (Profile.spec nd r) host hn c u, SpecTec.CfgRel hn b b' := by
  intro w hw
  obtain ⟨ts, hok⟩ := hc.1
  obtain ⟨c', d', he, rfl, hs⟩ :=
    (Sim.Round7.HostMods.runsREM hinj hf hh hb hm).2 c ts w hok hc.2 hw
  exact ⟨_, ⟨c', hs, rfl⟩, c', d', he, rfl, rfl⟩

theorem runsEM_fwd_upto_det (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host)
    (c : Config H) (hc : RunDomDetE (Profile.spec nd r) host c) (u : Unit) :
    ∀ b ∈ runObs (Profile.spec nd r) host hn c u,
      ∃ b' ∈ readRunObs Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
        (Sim.configV hn c) u, SpecTec.CfgRel hn b b' := by
  rintro b ⟨c', hs, rfl⟩
  obtain ⟨ts, hok⟩ := hc.1.1
  obtain ⟨d, he, hrun⟩ := (Sim.Round7.HostMods.runsREM hinj hf hh hb hm).1 c c' ts hok hc.1.2
    (SpecTecR6.detSteps_of_steps hs hc.2)
  exact ⟨_, hrun, c', d, he, rfl, rfl⟩

/-! ## The transitions on `RunDomE` and `RunDomDetE` -/

/-- **Core runs → round-7 runs, universal, for a host that invents no module.** -/
noncomputable def toBackendERunsUnivM (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host) :
    Transition (runChart (Profile.spec nd r) host hn (RunDomE (Profile.spec nd r) host))
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofSupUpToUniv (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (runsEM_bwd_upto hinj hf hh hb hm)

/-- **Core runs ↔ round-7 runs on deterministic sources, for a host that invents no module.** -/
noncomputable def toBackendERunsDetM (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host) :
    Transition (runChart (Profile.spec nd r) host hn (RunDomDetE (Profile.spec nd r) host))
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofUpTo (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (runsEM_fwd_upto_det hinj hf hh hb hm) (fun c hc => runsEM_bwd_upto hinj hf hh hb hm c hc.1)

theorem toBackendERunsDetM_dir (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host) :
    (toBackendERunsDetM (nd := nd) (r := r) hinj hf hh hb hm).dir = .equal := rfl

/-- **The round-7 run theorem with `HostModsSub`**: on `RunDomDetE`, a `CfgRel`-respecting
reachability sentence holds in Core iff it holds of the image under the runs of `Step` in
`utf8Env BI`. -/
theorem sat_iff_backendE_runs_detM (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host)
    {c : Config H} (hc : RunDomDetE (Profile.spec nd r) host c) {s : BSen Unit Value}
    (hs : s.Respects (SpecTec.CfgRel hn)) :
    (runChart (Profile.spec nd r) host hn (RunDomDetE (Profile.spec nd r) host)).Sat c s ↔
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  by simpa only [toBackendERunsDetM, BTrans.ofUpTo, BSen.rename_id] using
    (toBackendERunsDetM hinj hf hh hb hm).sat_iff rfl hc hs

/-- **The old run theorem is a special case**: `HostExportParam` gives `HostModsSub`
(`Round7.HostMods.hostModsSub_of_param`). -/
theorem sat_iff_backendE_runs_det_of_param (hinj : Function.Injective hn)
    (hf : Sim.HostFinite host) (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) {c : Config H}
    (hc : RunDomDetE (Profile.spec nd r) host c) {s : BSen Unit Value}
    (hs : s.Respects (SpecTec.CfgRel hn)) :
    (runChart (Profile.spec nd r) host hn (RunDomDetE (Profile.spec nd r) host)).Sat c s ↔
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  sat_iff_backendE_runs_detM hinj hf hh hb (Sim.Round7.HostMods.hostModsSub_of_param hf hp) hc hs

/-! ## The transitions on the source-only domains -/

/-- **Core runs → round-7 runs, universal, from `RunSrcE`.** -/
noncomputable def toBackendERunsSrcUniv (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host) :
    Transition (runChart (Profile.spec nd r) host hn (RunSrcE (Profile.spec nd r) host))
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofSupUpToUniv (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (fun c hc => runsEM_bwd_upto hinj hf hh hb hm c (runDomE_of_src hm hc))

/-- **Core runs ↔ round-7 runs on `RunSrcDetE`.** -/
noncomputable def toBackendERunsSrcDet (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host) :
    Transition (runChart (Profile.spec nd r) host hn (RunSrcDetE (Profile.spec nd r) host))
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofUpTo (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (fun c hc => runsEM_fwd_upto_det hinj hf hh hb hm c (runDomDetE_of_srcDet hm hc))
    (fun c hc => runsEM_bwd_upto hinj hf hh hb hm c (runDomE_of_src hm hc.1))

theorem toBackendERunsSrcDet_dir (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host) :
    (toBackendERunsSrcDet (nd := nd) (r := r) hinj hf hh hb hm).dir = .equal := rfl

/-- **The round-7 run theorem from the source**: on a valid source with `StripInj` and `NamesBnd`,
whose reachable configurations are `Round6.MemSimd.BoundedSelE` and have at most one Core
successor, a `CfgRel`-respecting reachability sentence holds in Core iff it holds of the image
under the runs of `Step` in `utf8Env BI`. -/
theorem sat_iff_backendE_runs_src (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) (hm : HostModsSub host)
    {c : Config H} (hc : RunSrcDetE (Profile.spec nd r) host c) {s : BSen Unit Value}
    (hs : s.Respects (SpecTec.CfgRel hn)) :
    (runChart (Profile.spec nd r) host hn (RunSrcDetE (Profile.spec nd r) host)).Sat c s ↔
      (readRunChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  by simpa only [toBackendERunsSrcDet, BTrans.ofUpTo, BSen.rename_id] using
    (toBackendERunsSrcDet hinj hf hh hb hm).sat_iff rfl hc hs

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7RunsM.sat_iff_backendE_runs_detM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backendE_runs_detM

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7RunsM.sat_iff_backendE_runs_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backendE_runs_src

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7RunsM.sat_iff_backendE_runs_det_of_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backendE_runs_det_of_param

end Silmaril.Wasm.Atlas.SpecTecR7RunsM
