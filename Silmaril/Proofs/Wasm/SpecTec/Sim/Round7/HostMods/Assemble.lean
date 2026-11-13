module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostMods.Step

/-!
# REI without `HostExportParam`: the one-step target and runs

* `fwdREM`, `bwdREM`: the two halves of `StepValidREM`, by the route of
  `Round7.fwdREI_of_leaves`/`bwdREI_of_leaves` with the two leaves discharged as in
  `Round7.Runs` (`swapAt_fwdM`/`swapAt_bwdM` at `d := c`, and `Round7.Runs.agree_strip`).
* `stepValidREM_holds`, and `wholeStepValidREI_of_REM`: the new statement implies
  `Round7.Task.wholeStepValidREI` (by `hostModsSub_of_param`).
* `runsREM`: `Round7.Runs.runsRE` with `HostModsSub` in place of `HostExportParam`.
* `mods_sub_of_detM`, `stripInj_of_detM`, `reachE_of_detM`: `StripInj` along deterministic steps,
  for a host that invents no module (`bump c` fixes the calling store's modules).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostMods

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim.Round7.Runs (RelE ReachE agree_strip relE_refl bump
  exportOnly_bump mem_of_bump_eq fix_of_mapConfig_id)
open Round6.Target (DetSteps RSteps)
open Round4Int (BI)

variable {H : Type}

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) (hb : HostExportBlind host)
  (hm : HostModsSub host) {nd : Bool} {r : RelaxedChoice}
include hinj hf hh hb hm

/-- **The forward half of `StepValidREM`.** -/
theorem fwdREM (c c' : Config H) (ts : List CValType) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hic : StripInj c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁)
    (hs : Step (Profile.spec nd r) host c c') :
    ∃ c'', Step (Profile.spec nd r) host c c'' ∧
      ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        backendE.step (BI (Profile.spec nd r) hn host) (configV hn c) (configV hn d') := by
  obtain ⟨c₀, hs₀, hu₀, d₀, hd₀, hst₀⟩ :=
    Round6.Target.fwdR_of_open hinj hf hh (Round6.Int.openR_backend hinj hf hh) (stripConfig c)
      (stripConfig c') ts (configOk_strip hc) (boundedSel_strip hbc)
      (boundedSel_succ_strip hb hsucc) (step_strip hb hs)
  have hstrd : Stripped d₀ :=
    stripped_of_configEq hd₀ (stripped_step hb hs₀ (stripped_stripConfig c))
  have hst₁ := (agree_strip hb (Profile.spec nd r) c _).mpr hst₀
  have hst₂ := swapAt_fwdM hinj hf hb hm _ hic hbc.2 (fun _ h => h) hstrd hst₁
  refine ⟨mapConfig (unstrip c) c₀, step_unstripM hm hb hic hs₀, fun hu => ?_,
    mapConfig (unstrip c) d₀, configEq_map _ hd₀, hst₂⟩
  have hu' : ∀ c₃, Step (Profile.spec nd r) host (stripConfig c) c₃ → c₃ = stripConfig c' := by
    intro c₃ h₃
    obtain ⟨c₃', h₃', rfl⟩ := step_of_strip hb h₃
    rw [hu c₃' h₃']
  rw [hu₀ hu']
  exact unstrip_strip_succM hm hic hs hu

/-- **The backward half of `StepValidREM`.** -/
theorem bwdREM (c : Config H) (ts : List CValType) (w : Value) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hic : StripInj c)
    (hs : backendE.step (BI (Profile.spec nd r) hn host) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c' := by
  obtain ⟨w₀, hs₀, hw⟩ := swapAt_bwdM hinj hf hb hm _ hic hbc.2 (fun _ h => h) hs
  have hs₁ := (agree_strip hb (Profile.spec nd r) c w₀).mp hs₀
  obtain ⟨c₀, d₀, hd, rfl, hst⟩ :=
    Round6.Target.bwdR_of_open hinj hf (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) (Round6.Int.openR_backend hinj hf hh) (stripConfig c) ts _
      (configOk_strip hc) (boundedSel_strip hbc) hs₁
  have hstr : Stripped d₀ :=
    stripped_of_configEq hd (stripped_step hb hst (stripped_stripConfig c))
  exact ⟨mapConfig (unstrip c) c₀, mapConfig (unstrip c) d₀, configEq_map _ hd,
    hw d₀ hstr rfl, step_unstripM hm hb hic hst⟩

end

/-- **`StepValidREM` holds**: `Round7.Task.wholeStepValidREI` with `HostModsSub` in place of
`HostExportParam`, at `B := BI (Profile.spec nd r) hn host`. -/
theorem stepValidREM_holds : StepValidREM := fun _ _ hinj _ hf hh hb hm _ _ =>
  ⟨_, fun c c' ts hc hbc hic hsucc hs => fwdREM hinj hf hh hb hm c c' ts hc hbc hic hsucc hs,
    fun c ts w hc hbc hic hs => bwdREM hinj hf hh hb hm c ts w hc hbc hic hs⟩

/-- **The new statement is stronger than `Round7.Task.wholeStepValidREI`.** -/
theorem wholeStepValidREI_of_REM (h : StepValidREM) : Task.wholeStepValidREI :=
  fun H hn hinj host hf hh hb hp nd r =>
    h H hn hinj host hf hh hb (hostModsSub_of_param hf hp) nd r

/-! ## Runs -/

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) (hb : HostExportBlind host)
  (hm : HostModsSub host) {nd : Bool} {r : RelaxedChoice}
include hinj hf hh hb hm

/-- **Deterministic Core runs are runs of the round-7 reading, along `RelE`.** -/
theorem stepsREM_sim {c₀ d₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
    (hR : ReachE (Profile.spec nd r) host c₀)
    (hd : RelE (BI (Profile.spec nd r) hn host) hn c₀ d₀) {c : Config H}
    (hs : DetSteps (Profile.spec nd r) host c₀ c) :
    ∃ d, RelE (BI (Profile.spec nd r) hn host) hn c d ∧
      RSteps backendE (BI (Profile.spec nd r) hn host) (configV hn d₀) (configV hn d) := by
  induction hs with
  | refl => exact ⟨d₀, hd, .refl⟩
  | @tail c₁ c₂ h₁ h₂ ih =>
    obtain ⟨d₁, hr₁, hr⟩ := ih
    have hrun : Steps (Profile.spec nd r) host c₀ c₁ := Round6.Target.steps_of_detSteps h₁
    obtain ⟨hb₁, hi₁⟩ := hR c₁ hrun
    obtain ⟨d₂, hr₂, hst⟩ := fwdRelEM hinj hf hh hb hm c₁ d₁ c₂ ts (Steps.safe hh hc hrun).1
      hb₁ hi₁ (fun c' h' => (hR c' (hrun.tail h')).1) hr₁ h₂.1 h₂.2
    exact ⟨d₂, hr₂, hr.tail hst⟩

/-- **Runs of the round-7 reading are Core runs, along `RelE`.** -/
theorem sstepsREM_sim {c₀ d₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
    (hR : ReachE (Profile.spec nd r) host c₀)
    (hd : RelE (BI (Profile.spec nd r) hn host) hn c₀ d₀) {w : Value}
    (hs : RSteps backendE (BI (Profile.spec nd r) hn host) (configV hn d₀) w) :
    ∃ c d, RelE (BI (Profile.spec nd r) hn host) hn c d ∧ w = configV hn d ∧
      Steps (Profile.spec nd r) host c₀ c := by
  induction hs with
  | refl => exact ⟨c₀, d₀, hd, rfl, .refl⟩
  | @tail w₁ w₂ _ h₂ ih =>
    obtain ⟨c₁, d₁, hr₁, rfl, hs₁⟩ := ih
    obtain ⟨hb₁, hi₁⟩ := hR c₁ hs₁
    obtain ⟨c₂, d₂, hr₂, hw, hst⟩ := bwdRelEM hinj hf hh hb hm c₁ d₁ ts w₂
      (Steps.safe hh hc hs₁).1 hb₁ hi₁ (fun c' h' => (hR c' (hs₁.tail h')).1) hr₁ h₂
    exact ⟨c₂, d₂, hr₂, hw, hs₁.tail hst⟩

/-- **The multi-step corollary at the round-7 reading, for a host that invents no module.** -/
theorem runsREM :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      ReachE (Profile.spec nd r) host c₀ → DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        RSteps backendE (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      ReachE (Profile.spec nd r) host c₀ →
      RSteps backendE (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) := by
  refine ⟨fun c₀ c ts hc hR hs => ?_, fun c₀ ts w hc hR hs => ?_⟩
  · obtain ⟨d, hr, hss⟩ := stepsREM_sim hinj hf hh hb hm hc hR
      (relE_refl hc (hR c₀ .refl).1) hs
    exact ⟨d, hr.1, hss⟩
  · obtain ⟨c, d, hr, hw, hss⟩ := sstepsREM_sim hinj hf hh hb hm hc hR
      (relE_refl hc (hR c₀ .refl).1) hs
    exact ⟨c, d, hr.1, hw, hss⟩

end

/-! ## `StripInj` along deterministic steps -/

/-- **A configuration's only successor has no new module instances**, for a host that invents
no module. -/
theorem mods_sub_of_detM {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c c' : Config H} (hs : Step P host c c') (hu : ∀ c₃, Step P host c c₃ → c₃ = c') :
    ∀ m ∈ mods c', m ∈ mods c := by
  have hfix : ∀ fi ∈ c.store.funcs, bump c fi.module = fi.module := fun fi hfi => by
    unfold bump
    simp [mem_mods_store hfi]
  have hst := step_mapConfigAt (exportOnly_bump c) hs (hostModMapAt_of_fix hm hfix)
  rw [mapConfig_id_of _ fun m hm => by unfold bump; simp [hm]] at hst
  have hfix' := fix_of_mapConfig_id (hu _ hst)
  exact fun m hm => mem_of_bump_eq (hfix' m hm)

/-- **`StripInj` passes to the only successor**, for a host that invents no module. -/
theorem stripInj_of_detM {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c c' : Config H} (hi : StripInj c) (hs : Step P host c c')
    (hu : ∀ c₃, Step P host c c₃ → c₃ = c') : StripInj c' :=
  fun m₁ h₁ m₂ h₂ he =>
    hi m₁ (mods_sub_of_detM hm hs hu m₁ h₁) m₂ (mods_sub_of_detM hm hs hu m₂ h₂) he

/-- **`ReachE` on deterministic sources** from `StripInj` at the source alone, for a host that
invents no module. -/
theorem reachE_of_detM {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c₀ : Config H} (hi : StripInj c₀)
    (hb : ∀ c, Steps P host c₀ c → BoundedSelE c)
    (hd : ∀ c, Steps P host c₀ c → ∀ c₁ c₂, Step P host c c₁ → Step P host c c₂ → c₁ = c₂) :
    ReachE P host c₀ := by
  intro c hc
  refine ⟨hb c hc, ?_⟩
  induction hc with
  | refl => exact hi
  | @tail c₁ c₂ h₁ h₂ ih =>
    exact stripInj_of_detM hm ih h₂ fun c₃ h₃ => hd c₁ h₁ c₃ c₂ h₃ h₂

end Silmaril.Wasm.SpecTec.Sim.Round7.HostMods
