module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.HostMods.HostRule
public import Silmaril.Wasm.SpecTec.Sim.Round7.Runs.Thms

/-!
# REI without `HostExportParam`: one step

The route of `Round7.Runs.fwdRelE`/`bwdRelE` with `HostModsSub` in place of
`HostExportParam`:

* `excRules_QCM`, `swapAt_fwdM`, `swapAt_bwdM`: the export swap at a witness, with the host-call
  rules `ruleFwd_hostM`, `ruleBwd_hostM`;
* `step_unstripM`, `unstrip_strip_succM`: the Core side, with the store-local
  `step_mapConfigAt`. The host is called only at the store of the source: at `stripStore c.store`
  for `step_unstripM` (`hostModMapAt_unstrip`), and at `c.store`, whose modules
  `unstrip c ∘ stripModule` fixes, for `unstrip_strip_succM` (`hostModMapAt_of_fix`);
* `fwdRelEM`, `bwdRelEM`: one step along `RelE`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostMods

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (gdB)
open Silmaril.Wasm.SpecTec.Sim.Round7.Runs (RelE mods_configEq agree_strip relE_unstrip simRel_strip)
open Round6.Reading (SStepB)
open Round4Int (BI)

variable {H : Type}

/-! ## The SpecTec side -/

/-- **The four rules outside the kernel check commute with erasure on `QC c`**, for a host that
invents no module. -/
theorem excRules_QCM {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
    (hf : HostFinite host) (hb : HostExportBlind host) (hm : HostModsSub host)
    (P : Profile) {c : Config H} (hi : StripInj c) (hnb : NamesBnd c) :
    ∀ nm ∈ excNames, RuleFwd (QC c) (utf8Env (BI P hn host)) nm ∧
      RuleBwd (QC c) (utf8Env (BI P hn host)) nm := by
  intro nm hnm
  have HE := EraseAll.hyps_BI hi P hn host
  have HB := EraseAll.hyps_B hi P hn host
  have H' := hyps_eImg_B hi P hn host
  obtain ⟨K, hK⟩ := qExp_QC (BI P hn host) hnb
  have hT := typFwd_gd (gd' := gdB) (typFwd_utf8Env HE)
  have hTb := typBwd_gd (gd' := gdB) (typBwd_utf8Env HE hK)
  rcases mem_excNames hnm with hh | hg
  · exact ⟨ruleFwd_hostM HB H' hT hTb hQA_QC hinj hf hm hb hh,
      ruleBwd_hostM HB H' hT hTb hQA_QC hi hinj hf hm hb hh⟩
  · exact ⟨ruleFwd_grow HE HB H' hT hTb hQA_QC hg, ruleBwd_grow HE HB H' hT hTb hQA_QC hg⟩

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hb : HostExportBlind host) (hm : HostModsSub host) (P : Profile)
  {c d : Config H} (hi : StripInj c) (hnb : NamesBnd c) (hsub : ∀ m ∈ mods d, m ∈ mods c)
include hinj hf hb hm hi hnb hsub

/-- **Forward swap at a witness**, for a host that invents no module. -/
theorem swapAt_fwdM {e : Config H} (he : Stripped e)
    (h : SStepB (utf8Env (BI P hn host)) (configV hn (stripConfig d)) (configV hn e)) :
    SStepB (utf8Env (BI P hn host)) (configV hn d) (configV hn (mapConfig (unstrip c) e)) := by
  have ha : AllIn (QC c) (configV hn d) :=
    allIn_configV_of hn fun m hm => Or.inl ⟨m, hsub m hm, rfl⟩
  rw [← eraseV_configV] at h
  obtain ⟨h₁, h₂, h₃⟩ := sStepB_QC_bwd hi hnb P hn host
    (fun nm hnm => (excRules_QCM hinj hf hb hm P hi hnb nm hnm).2) ha h
  rwa [← eq_configV_unstrip hn hi he h₁ h₂]

/-- **Backward swap at a witness**, for a host that invents no module. -/
theorem swapAt_bwdM {w : Value} (h : SStepB (utf8Env (BI P hn host)) (configV hn d) w) :
    ∃ w₀, SStepB (utf8Env (BI P hn host)) (configV hn (stripConfig d)) w₀ ∧
      ∀ e : Config H, Stripped e → w₀ = configV hn e →
        w = configV hn (mapConfig (unstrip c) e) := by
  have ha : AllIn (QC c) (configV hn d) :=
    allIn_configV_of hn fun m hm => Or.inl ⟨m, hsub m hm, rfl⟩
  obtain ⟨h₁, h₂⟩ := sStepB_QC_fwd hi hnb P hn host
    (fun nm hnm => (excRules_QCM hinj hf hb hm P hi hnb nm hnm).1) ha h
  rw [eraseV_configV] at h₁
  exact ⟨eraseV w, h₁, fun e he hw => eq_configV_unstrip hn hi he h₂ hw⟩

end

/-! ## The Core side -/

/-- **Carrying a step of `stripConfig c` back to `c`**, under `StripInj c`, for an export-blind
host that invents no module. -/
theorem step_unstripM {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    (hb : HostExportBlind host) {c d : Config H} (hinj : StripInj c)
    (h : Step P host (stripConfig c) d) : Step P host c (mapConfig (unstrip c) d) := by
  have := step_mapConfigAt (exportOnly_unstrip c) h (hostModMapAt_unstrip hm hb hinj)
  rwa [mapConfig_unstrip_strip hinj] at this

/-- **The only successor survives the round trip**, for a host that invents no module. -/
theorem unstrip_strip_succM {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c c' : Config H} (hinj : StripInj c) (hs : Step P host c c')
    (hu : ∀ c₃, Step P host c c₃ → c₃ = c') :
    mapConfig (unstrip c) (stripConfig c') = c' := by
  have hν : ExportOnly (unstrip c ∘ stripModule) :=
    (exportOnly_unstrip c).comp exportOnly_stripModule
  have := step_mapConfigAt hν hs
    (hostModMapAt_of_fix hm fun fi hfi => unstrip_strip hinj (mem_mods_store hfi))
  rw [mapConfig_unstrip_comp hinj] at this
  rw [← mapConfig_stripModule, mapConfig_comp]
  exact hu _ this

/-! ## One step along `RelE` -/

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) (hb : HostExportBlind host)
  (hm : HostModsSub host) {nd : Bool} {r : RelaxedChoice}
include hinj hf hh hb hm

/-- **The forward step along `RelE`**, for a host that invents no module. -/
theorem fwdRelEM (c d c' : Config H) (ts : List CValType) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hic : StripInj c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁)
    (hd : RelE (BI (Profile.spec nd r) hn host) hn c d)
    (hs : Step (Profile.spec nd r) host c c')
    (hu : ∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') :
    ∃ d', RelE (BI (Profile.spec nd r) hn host) hn c' d' ∧
      backendE.step (BI (Profile.spec nd r) hn host) (configV hn d) (configV hn d') := by
  obtain ⟨c₀, d₂, hs₀, hu₀, hr₂, hst⟩ :=
    Round6.Target.fwdRelR_of_open hinj hf hh (Round6.Int.openR_backend hinj hf hh)
      (stripConfig c) (stripConfig d) (stripConfig c') ts (configOk_strip hc)
      (boundedSel_strip hbc) (boundedSel_succ_strip hb hsucc) (simRel_strip hd)
      (step_strip hb hs)
  have hu' : ∀ c₃, Step (Profile.spec nd r) host (stripConfig c) c₃ → c₃ = stripConfig c' := by
    intro c₃ h₃
    obtain ⟨c₃', h₃', rfl⟩ := step_of_strip hb h₃
    rw [hu c₃' h₃']
  have hstr : Stripped d₂ :=
    stripped_of_configEq hr₂.1 (stripped_step hb hs₀ (stripped_stripConfig c))
  have hst₁ := (agree_strip hb (Profile.spec nd r) d _).mpr hst
  have hsub : ∀ m ∈ mods d, m ∈ mods c := fun m hm => mods_configEq hd.1 ▸ hm
  refine ⟨mapConfig (unstrip c) d₂, ?_,
    swapAt_fwdM hinj hf hb hm _ hic hbc.2 hsub hstr hst₁⟩
  have hrel := relE_unstrip (c := c) hr₂ hstr
  rwa [hu₀ hu', unstrip_strip_succM hm hic hs hu] at hrel

/-- **The backward step along `RelE`**, for a host that invents no module. -/
theorem bwdRelEM (c d : Config H) (ts : List CValType) (w : Value) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hic : StripInj c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁)
    (hd : RelE (BI (Profile.spec nd r) hn host) hn c d)
    (hs : backendE.step (BI (Profile.spec nd r) hn host) (configV hn d) w) :
    ∃ c' d', RelE (BI (Profile.spec nd r) hn host) hn c' d' ∧ w = configV hn d' ∧
      Step (Profile.spec nd r) host c c' := by
  have hsub : ∀ m ∈ mods d, m ∈ mods c := fun m hm => mods_configEq hd.1 ▸ hm
  obtain ⟨w₀, hs₀, hw⟩ := swapAt_bwdM hinj hf hb hm _ hic hbc.2 hsub hs
  have hs₁ := (agree_strip hb (Profile.spec nd r) d w₀).mp hs₀
  obtain ⟨c₀, d₂, hr₂, rfl, hst⟩ :=
    Round6.Target.bwdRelR_of_open hinj hf hh (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) (Round6.Int.openR_backend hinj hf hh) (stripConfig c)
      (stripConfig d) ts _ (configOk_strip hc) (boundedSel_strip hbc)
      (boundedSel_succ_strip hb hsucc) (simRel_strip hd) hs₁
  have hstr : Stripped d₂ :=
    stripped_of_configEq hr₂.1 (stripped_step hb hst (stripped_stripConfig c))
  exact ⟨_, _, relE_unstrip hr₂ hstr, hw d₂ hstr rfl, step_unstripM hm hb hic hst⟩

end

end Silmaril.Wasm.SpecTec.Sim.Round7.HostMods
