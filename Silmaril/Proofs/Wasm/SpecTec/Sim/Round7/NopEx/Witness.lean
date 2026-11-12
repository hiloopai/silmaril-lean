module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NopEx.Step
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitLoops
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.Thms
public import Silmaril.Wasm.Atlas.SpecTecR7Runs.Thms

/-!
# a run-domain witness with exports

Round 5's `expNopCfg` (`nop` in a frame over `ConfigOk.exportModule`, which exports global `0` as
`"g"`) and its successor `expDoneCfg`.

* `step_expNop_inv`: **for every profile and host, `expDoneCfg` is the only successor of
  `expNopCfg`**. The code is call-free, so the step is a `noHost` step
  (`step_noHost_of_callFree`); Silmaril's `Step.head_inv` and `Head.fam_inv` reduce it to a
  `ParametricStep` of `[nop]`, which is deterministic (`ParametricStep.det`).
* `steps_expNop`: the configurations reachable from `expNopCfg` are `expNopCfg` and `expDoneCfg`.
* `runDomDetE_expNopCfg`: **`expNopCfg` is in `Atlas.SpecTecR7Runs.RunDomDetE`** for every profile
  and host. Its frame's module exports a name (`exports_expNopCfg`) and it takes a step
  (`Round5.Pos.step_expNopCfg`).
* `backendE_step_expNopCfg`, `backendE_bwd_expNopCfg`: at round 6's primitives, for an
  injective `hn` and a finite, `HostOk`, export-blind host that invents no module, the image of
  `expNopCfg` takes a step of `Round7.backendE` (`utf8Env`) to the image of a witness of
  `expDoneCfg`, and every such step does. In `simEnv` it takes none
  (`Round5.Pos.not_sstep_expNopCfg`).
* `hostExportBlind_divHost`, `hostModsSub_divHost`: round 5's diverging host qualifies.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NopEx

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SingleThreaded.Det (Head.fam_inv ParametricStep.det)
open Round5.Pos (expNopCfg expDoneCfg)
open Round4Int (BI)

variable {H : Type}

/-! ## Core: `expDoneCfg` is the only successor -/

/-- **`expDoneCfg` is the only successor of `expNopCfg`**, for every profile and host. -/
theorem step_expNop_inv {P : Profile} {host : HostSemantics H} {c : Config H}
    (h : Step P host (expNopCfg (H := H)) c) : c = expDoneCfg := by
  have h₀ := step_noHost_of_callFree h rfl
  obtain ⟨pre, args, c₀, hpa, hH, rfl⟩ :=
    Step.head_inv (ws := []) (rest := []) h₀ rfl (by simp) (by simp)
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hpa.symm
  obtain ⟨is', hst, rfl⟩ := Head.fam_inv hH (by decide)
  obtain ⟨-, rfl⟩ := ParametricStep.det hst .nop (p := []) rfl
  rfl

/-- `expDoneCfg` has no successor. -/
theorem not_step_expDone {P : Profile} {host : HostSemantics H} {c : Config H} :
    ¬ Step P host (expDoneCfg (H := H)) c :=
  Step.not_vals (vs := [])

/-- **The configurations reachable from `expNopCfg`.** -/
theorem steps_expNop {P : Profile} {host : HostSemantics H} {c : Config H}
    (h : Steps P host (expNopCfg (H := H)) c) : c = expNopCfg ∨ c = expDoneCfg := by
  induction h with
  | refl => exact .inl rfl
  | tail _ h₂ ih =>
    rcases ih with rfl | rfl
    · exact .inr (step_expNop_inv h₂)
    · exact absurd h₂ not_step_expDone

/-! ## The domain -/

theorem modNamesBnd_exportModule : ModNamesBnd ConfigOk.exportModule := by
  intro e he
  simp only [ConfigOk.exportModule, List.mem_singleton] at he
  subst he
  decide

theorem namesBnd_exp {code : List Admin} (hc : AdminsNB code) :
    NamesBnd (⟨ConfigOk.exportStore, ⟨[], ConfigOk.exportModule⟩, code⟩ : Config H) :=
  ⟨by simp [ConfigOk.exportStore], modNamesBnd_exportModule, hc⟩

theorem boundedSelE_expNop : BoundedSelE (expNopCfg (H := H)) :=
  ⟨⟨Round5.Pos.bounded_expNopCfg, Round6.MemSimd.noMissel_expNopCfg⟩,
    namesBnd_exp ⟨trivial, trivial⟩⟩

theorem boundedSelE_expDone : BoundedSelE (expDoneCfg (H := H)) :=
  ⟨⟨Round5.Pos.bounded_expDoneCfg, Round6.MemSimd.noMissel_expDoneCfg⟩, namesBnd_exp trivial⟩

theorem stripInj_expNop : StripInj (expNopCfg (H := H)) :=
  stripInj_of_single (m₀ := ConfigOk.exportModule) fun m hm => by
    simpa [mods, expNopCfg, ConfigOk.exportStore, modsAdmins, modsAdmin] using hm

theorem stripInj_expDone : StripInj (expDoneCfg (H := H)) :=
  stripInj_of_single (m₀ := ConfigOk.exportModule) fun m hm => by
    simpa [mods, expDoneCfg, ConfigOk.exportStore, modsAdmins] using hm

/-- The frame's module of `expNopCfg` exports a name. -/
theorem exports_expNopCfg : (expNopCfg (H := H)).frame.module.exports = [⟨"g", .global 0⟩] := rfl

/-- **`expNopCfg` is in the round-7 deterministic run domain**, for every profile and host. -/
theorem runDomDetE_expNopCfg (P : Profile) (host : HostSemantics H) :
    Atlas.SpecTecR7Runs.RunDomDetE P host (expNopCfg (H := H)) := by
  refine ⟨⟨⟨[], Round5.Pos.configOk_expNopCfg⟩, fun c hc => ?_⟩, fun c hc c₁ c₂ h₁ h₂ => ?_⟩
  · rcases steps_expNop hc with rfl | rfl
    · exact ⟨boundedSelE_expNop, stripInj_expNop⟩
    · exact ⟨boundedSelE_expDone, stripInj_expDone⟩
  · rcases steps_expNop hc with rfl | rfl
    · rw [step_expNop_inv h₁, step_expNop_inv h₂]
    · exact absurd h₁ not_step_expDone

/-! ## The round-7 reading steps from its image -/

theorem hostExportBlind_divHost : HostExportBlind Round5.Pos.divHost :=
  ⟨fun _ _ _ o (h : o = .diverged) => by subst h; rfl,
    fun _ _ _ o' (h : o' = .diverged) => ⟨.diverged, rfl, h⟩⟩

theorem hostModsSub_divHost : HostMods.HostModsSub Round5.Pos.divHost :=
  fun _ _ _ _ _ h => nomatch (h : Silmaril.Wasm.Execution.Host.Outcome.returned _ _ = .diverged)

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) (hb : HostExportBlind host)
  (hm : HostMods.HostModsSub host) (nd : Bool) (r : RelaxedChoice)
include hinj hf hh hb hm

/-- **The image of `expNopCfg` steps in the round-7 reading** to the image of a witness of
`expDoneCfg`. -/
theorem backendE_step_expNopCfg :
    ∃ d, Bwd.ConfigEq (expDoneCfg (H := H)) d ∧
      backendE.step (BI (Profile.spec nd r) hn host) (configV hn expNopCfg) (configV hn d) := by
  obtain ⟨c'', hs, -, d, hd, hst⟩ := HostMods.fwdREM hinj hf hh hb hm expNopCfg expDoneCfg []
    Round5.Pos.configOk_expNopCfg boundedSelE_expNop stripInj_expNop
    (fun c₁ h₁ => step_expNop_inv h₁ ▸ boundedSelE_expDone)
    (Round5.Pos.step_expNopCfg _ host)
  rw [step_expNop_inv hs] at hd
  exact ⟨d, hd, hst⟩

/-- **Every step of the round-7 reading from the image of `expNopCfg`** goes to the image of a
witness of `expDoneCfg`. -/
theorem backendE_bwd_expNopCfg {w : Value}
    (hs : backendE.step (BI (Profile.spec nd r) hn host) (configV hn expNopCfg) w) :
    ∃ d, Bwd.ConfigEq (expDoneCfg (H := H)) d ∧ w = configV hn d := by
  obtain ⟨c', d, hd, rfl, hst⟩ := HostMods.bwdREM hinj hf hh hb hm expNopCfg [] w
    Round5.Pos.configOk_expNopCfg boundedSelE_expNop stripInj_expNop hs
  rw [step_expNop_inv hst] at hd
  exact ⟨d, hd, rfl⟩

end

/-- **At the diverging host**: the image of `expNopCfg` steps in `utf8Env`. -/
theorem backendE_step_expNopCfg_divHost (nd : Bool) (r : RelaxedChoice) :
    ∃ d, Bwd.ConfigEq (expDoneCfg (H := Unit)) d ∧
      backendE.step (BI (Profile.spec nd r) Round5.Pos.hnU Round5.Pos.divHost)
        (configV Round5.Pos.hnU expNopCfg) (configV Round5.Pos.hnU d) :=
  backendE_step_expNopCfg Round5.Pos.hnU_injective Round5.Pos.hostFinite_divHost
    Round5.Pos.hostOk_divHost hostExportBlind_divHost hostModsSub_divHost nd r

/-- **The round-7 run theorem at `expNopCfg`**, at the diverging host: a `CfgRel`-respecting
reachability sentence holds of `expNopCfg` in Core iff it holds of its image under the runs of
`Step` in `utf8Env BI`. -/
theorem sat_iff_expNopCfg (nd : Bool) (r : RelaxedChoice) {s : Atlas.BSen Unit Value}
    (hs : s.Respects (Atlas.SpecTec.CfgRel Round5.Pos.hnU)) :
    (Atlas.SpecTecR6.runChart (Profile.spec nd r) Round5.Pos.divHost Round5.Pos.hnU
        (Atlas.SpecTecR7Runs.RunDomDetE (Profile.spec nd r) Round5.Pos.divHost)).Sat
        expNopCfg s ↔
      (Atlas.SpecTecR6.readRunChart backendE
        (BI (Profile.spec nd r) Round5.Pos.hnU Round5.Pos.divHost)).Sat
        (configV Round5.Pos.hnU expNopCfg) s :=
  Atlas.SpecTecR7Runs.sat_iff_backendE_runs_det Round5.Pos.hnU_injective
    Round5.Pos.hostFinite_divHost Round5.Pos.hostOk_divHost hostExportBlind_divHost
    hostExportParam_divHost (runDomDetE_expNopCfg _ _) hs

end Silmaril.Wasm.SpecTec.Sim.Round7.NopEx
