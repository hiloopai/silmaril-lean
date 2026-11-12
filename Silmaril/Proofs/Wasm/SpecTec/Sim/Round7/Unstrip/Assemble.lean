module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Unstrip.Step
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms

/-!
# Round 7: `Task.wholeStepValidREI` from the two SpecTec leaves

`wholeStepValidREI_of_leaves`: the target with the injectivity side condition follows from
`Task.swapEquiv` (SpecTec's `Step` commutes with un-stripping) and `Task.envAgreeNE` (the two
environments agree on round 6's domain). The rest is proved:

* round 6 at `stripConfig c` (`Round6.Target.fwdR_of_open`, `bwdR_of_open` with
  `Round6.Int.openR_backend`), whose domain `stripConfig c` is in (`configOk_strip`,
  `boundedSel_strip`, and `step_of_strip` for the successors);
* successors of export-free configurations are export-free (`stripped_step`), and so are their
  `ConfigEq` witnesses (`stripped_of_configEq`);
* Core's `Step` commutes with `unstrip c` (`step_mapConfig`), and `unstrip c` undoes stripping on
  `c` (`mapConfig_unstrip_strip`), so a step of `stripConfig c` is carried back to a step of `c`;
* for the uniqueness clause, `unstrip c ∘ stripModule` fixes `c` (`mapConfig_unstrip_comp`), so
  `step_mapConfig` sends the only successor `c'` of `c` to a successor of `c`, hence to `c'`.

Also: `wholeStepValidREI_of_REH` (the new target is weaker) and `hostExportParam_divHost` (the
new host hypothesis is satisfiable).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

/-- **The target with the side condition is weaker than `Task.wholeStepValidREH`.** -/
theorem wholeStepValidREI_of_REH (h : Task.wholeStepValidREH) : Task.wholeStepValidREI := by
  intro H hn hinj host hf hh hb _ nd r
  obtain ⟨B, hF, hB⟩ := h H hn hinj host hf hh hb nd r
  exact ⟨B, fun c c' ts hc hbc _ hsucc hs => hF c c' ts hc hbc hsucc hs,
    fun c ts w hc hbc _ hs => hB c ts w hc hbc hs⟩

/-- `HostExportParam` is satisfiable by a finite `HostOk` host: round 5's diverging host. -/
theorem hostExportParam_divHost : HostExportParam Round5.Pos.divHost :=
  fun _ _ _ _ _ o (h : o = .diverged) => by subst h; rfl

/-- The successors of `stripConfig c` are `Round5.Target.BoundedSel` when those of `c` are
`BoundedSelE`. -/
theorem boundedSel_succ_strip {P : Profile} {host : HostSemantics H} (hb : HostExportBlind host)
    {c : Config H} (hsucc : ∀ c₁, Step P host c c₁ → BoundedSelE c₁) :
    ∀ c₁, Step P host (stripConfig c) c₁ → Round5.Target.BoundedSel c₁ := by
  intro c₁ h₁
  obtain ⟨c₁', h₁', rfl⟩ := step_of_strip hb h₁
  exact boundedSel_strip (hsucc c₁' h₁')

/-- **Carrying a step of `stripConfig c` back to `c`**, under `StripInj c`. -/
theorem step_unstrip {P : Profile} {host : HostSemantics H} (hp : HostExportParam host)
    {c d : Config H} (hinj : StripInj c) (h : Step P host (stripConfig c) d) :
    Step P host c (mapConfig (unstrip c) d) := by
  have := step_mapConfig (exportOnly_unstrip c) (hp _ (exportOnly_unstrip c)) h
  rwa [mapConfig_unstrip_strip hinj] at this

/-- **The only successor survives the round trip**: if `c'` is the only successor of `c`, the
only successor of `stripConfig c` is `stripConfig c'`, and un-stripping it gives back `c'`. -/
theorem unstrip_strip_succ {P : Profile} {host : HostSemantics H} (hp : HostExportParam host)
    {c c' : Config H} (hinj : StripInj c) (hs : Step P host c c')
    (hu : ∀ c₃, Step P host c c₃ → c₃ = c') :
    mapConfig (unstrip c) (stripConfig c') = c' := by
  have hν : ExportOnly (unstrip c ∘ stripModule) :=
    (exportOnly_unstrip c).comp exportOnly_stripModule
  have := step_mapConfig hν (hp _ hν) hs
  rw [mapConfig_unstrip_comp hinj] at this
  rw [← mapConfig_stripModule, mapConfig_comp]
  exact hu _ this

/-- **The forward half of `Task.wholeStepValidREI`, from the two leaves.** -/
theorem fwdREI_of_leaves (hS : Task.swapEquiv) (hA : Task.envAgreeNE) {hn : H → String}
    (hinj : Function.Injective hn) {host : HostSemantics H} (hf : HostFinite host)
    (hh : HostOk host) (hb : HostExportBlind host) (hp : HostExportParam host) {nd : Bool}
    {r : RelaxedChoice} (c c' : Config H) (ts : List CValType) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hic : StripInj c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁)
    (hs : Step (Profile.spec nd r) host c c') :
    ∃ c'', Step (Profile.spec nd r) host c c'' ∧
      ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        backendE.step (Round4Int.BI (Profile.spec nd r) hn host) (configV hn c) (configV hn d') := by
  have hcs := configOk_strip hc
  have hbs := boundedSel_strip hbc
  obtain ⟨c₀, hs₀, hu₀, d₀, hd₀, hst₀⟩ :=
    Round6.Target.fwdR_of_open hinj hf hh (Round6.Int.openR_backend hinj hf hh) (stripConfig c)
      (stripConfig c') ts hcs hbs (boundedSel_succ_strip hb hsucc) (step_strip hb hs)
  have hstrd : Stripped d₀ :=
    stripped_of_configEq hd₀ (stripped_step hb hs₀ (stripped_stripConfig c))
  have hst₁ := (hA _ hn hinj host hf hh hb nd r (stripConfig c) ts hcs hbs _).mpr hst₀
  have hst₂ := (hS _ hn hinj host hf hh hb hp nd r c ts hc hbc hic).1 d₀ hstrd hst₁
  refine ⟨mapConfig (unstrip c) c₀, step_unstrip hp hic hs₀, fun hu => ?_,
    mapConfig (unstrip c) d₀, configEq_map _ hd₀, hst₂⟩
  have hu' : ∀ c₃, Step (Profile.spec nd r) host (stripConfig c) c₃ → c₃ = stripConfig c' := by
    intro c₃ h₃
    obtain ⟨c₃', h₃', rfl⟩ := step_of_strip hb h₃
    rw [hu c₃' h₃']
  rw [hu₀ hu']
  exact unstrip_strip_succ hp hic hs hu

/-- **The backward half of `Task.wholeStepValidREI`, from the two leaves.** -/
theorem bwdREI_of_leaves (hS : Task.swapEquiv) (hA : Task.envAgreeNE) {hn : H → String}
    (hinj : Function.Injective hn) {host : HostSemantics H} (hf : HostFinite host)
    (hh : HostOk host) (hb : HostExportBlind host) (hp : HostExportParam host) {nd : Bool}
    {r : RelaxedChoice} (c : Config H) (ts : List CValType) (w : Value) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hic : StripInj c)
    (hs : backendE.step (Round4Int.BI (Profile.spec nd r) hn host) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c' := by
  have hcs := configOk_strip hc
  have hbs := boundedSel_strip hbc
  obtain ⟨w₀, hs₀, hw⟩ := (hS _ hn hinj host hf hh hb hp nd r c ts hc hbc hic).2 w hs
  have hs₁ := (hA _ hn hinj host hf hh hb nd r (stripConfig c) ts hcs hbs w₀).mp hs₀
  obtain ⟨c₀, d₀, hd, rfl, hst⟩ :=
    Round6.Target.bwdR_of_open hinj hf (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) (Round6.Int.openR_backend hinj hf hh) (stripConfig c) ts _
      hcs hbs hs₁
  have hstr : Stripped d₀ :=
    stripped_of_configEq hd (stripped_step hb hst (stripped_stripConfig c))
  exact ⟨mapConfig (unstrip c) c₀, mapConfig (unstrip c) d₀, configEq_map _ hd,
    hw d₀ hstr rfl, step_unstrip hp hic hst⟩

/-- **`Task.wholeStepValidREI` from the two SpecTec leaves**, with `B := BI (Profile.spec nd r)
hn host`, round 6's primitives. -/
theorem wholeStepValidREI_of_leaves (hS : Task.swapEquiv) (hA : Task.envAgreeNE) :
    Task.wholeStepValidREI := fun _ _ hinj _ hf hh hb hp _ _ =>
  ⟨_, fun c c' ts hc hbc hic hsucc hs =>
      fwdREI_of_leaves hS hA hinj hf hh hb hp c c' ts hc hbc hic hsucc hs,
    fun c ts w hc hbc hic hs => bwdREI_of_leaves hS hA hinj hf hh hb hp c ts w hc hbc hic hs⟩

end Silmaril.Wasm.SpecTec.Sim.Round7
