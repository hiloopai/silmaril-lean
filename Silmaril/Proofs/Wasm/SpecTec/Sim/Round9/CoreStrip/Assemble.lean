module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.CoreStrip.Host
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.CoreStrip.Step
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.CoreStrip.Pres
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Runs.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Thms

/-!
# the Core side of RE without `StripInj` or `HostExportBlind`, assembled

* `step_stripAt`, `step_of_stripAt`: **the Core stripping lemmas at the stripped host.** A step
  of `c` with `host` gives a step of `stripConfig c` with `stripHostAt host c.store` to the
  stripped successor, and every step of `stripConfig c` with that host is the stripped form of a
  step of `c`. No hypothesis on the host or on the modules of `c`.
* `fwdREX`, `bwdREX`, `stepValidREX_of_leaves`: round 6 at the stripped configuration and the
  stripped host, with the SpecTec leaves `EraseBwdAt`/`EraseFwdAt`, give RE up to export lists.
* `wholeStepValidRE_of_leaves`, `wholeStepValidREH_of_leaves`: RE and REH from the three leaves.
* `eraseFwdAt_of_blind`: at an export-blind host the forward SpecTec leaf follows 's
  forward transfer (`ElseBwd.sStepB_fwd_BI_left''`, given `BadFwdE` and `ElseBwdBLeft''`) and
  `Round7.Runs.agree_strip`.
* `exactAt_of_REM`: on the domain of `Round7.HostMods.StepValidREM` (`StripInj`, an
  export-blind host that invents no module) the export leaf holds, by `HostMods.bwdREM`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round7
open Round4Int (BI)

variable {H : Type}

/-! ## The Core stripping lemmas at the stripped host -/

theorem storeOk_of_configOk {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) :
    StoreOk c.store :=
  let ⟨_, hs, _⟩ := hc
  hs.1

/-- `c` agrees with its stripped form up to export lists. -/
theorem exRel_stripConfig (c : Config H) : ExRel c (stripConfig c) :=
  (stripped_stripConfig c).symm

/-- **A step of `c` is a step of `stripConfig c` at the stripped host**, to the stripped
successor. -/
theorem step_stripAt {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hs₀ : StoreOk c.store) (h : Step P host c c') :
    Step P (stripHostAt host c.store) (stripConfig c) (stripConfig c') := by
  obtain ⟨d', hd', hr⟩ := exRel_step₂ h (stripConfig c) (exRel_stripConfig c)
    (hostRelAt_strip host hs₀)
  have hstr : stripConfig d' = d' :=
    stripped_stepAt hd' (hostStrippedAt_strip host hs₀) (stripped_stripConfig c)
  have he : stripConfig c' = d' := hr.trans hstr
  rw [he]
  exact hd'

/-- **Every step of `stripConfig c` at the stripped host is the stripped form of a step of
`c`.** -/
theorem step_of_stripAt {P : Profile} {host : HostSemantics H} {c d₀ : Config H}
    (hs₀ : StoreOk c.store) (h : Step P (stripHostAt host c.store) (stripConfig c) d₀) :
    ∃ c', Step P host c c' ∧ stripConfig c' = d₀ := by
  obtain ⟨c', hc', hr⟩ := exRel_step₂ h c (stripped_stripConfig c) (hostRelAt_unstrip host hs₀)
  have hstr : stripConfig d₀ = d₀ :=
    stripped_stepAt h (hostStrippedAt_strip host hs₀) (stripped_stripConfig c)
  exact ⟨c', hc', hr.symm.trans hstr⟩

/-- The successors of `stripConfig c` at the stripped host are 's domain when those of
`c` are 's. -/
theorem boundedSel_succ_stripAt {P : Profile} {host : HostSemantics H} {c : Config H}
    (hs₀ : StoreOk c.store) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSelE c₁) :
    ∀ c₁, Step P (stripHostAt host c.store) (stripConfig c) c₁ → Round5.Target.BoundedSel c₁ := by
  intro c₁ h₁
  obtain ⟨c₂, h₂, rfl⟩ := step_of_stripAt hs₀ h₁
  exact boundedSel_strip (hsucc c₂ h₂)

/-! ## RE up to export lists -/

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) {nd : Bool} {r : RelaxedChoice}
include hinj hf hh

/-- **The forward half of RE up to export lists**, from the backward SpecTec leaf. -/
theorem fwdREX (c c' : Config H) (ts : List CValType) (hc : ConfigOk c ts) (hbc : BoundedSelE c)
    (hB : EraseBwdAt hn (Profile.spec nd r) host c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁)
    (hs : Step (Profile.spec nd r) host c c') :
    ∃ c'', Step (Profile.spec nd r) host c c'' ∧
      ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ w, backendE.step (BI (Profile.spec nd r) hn host) (configV hn c) w ∧ ExAgree hn c'' w := by
  have hs₀ := storeOk_of_configOk hc
  have hf' := stripHostAt_finite hf c.store
  have hh' := stripHostAt_ok hh c.store
  obtain ⟨c₀, hs₀', -, d₀, hd₀, hst₀⟩ :=
    Round6.Target.fwdR_of_open hinj hf' hh' (Round6.Int.openR_backend hinj hf' hh')
      (stripConfig c) (stripConfig c') ts (configOk_strip hc) (boundedSel_strip hbc)
      (boundedSel_succ_stripAt hs₀ hsucc) (step_stripAt hs₀ hs)
  obtain ⟨c'', hs'', rfl⟩ := step_of_stripAt hs₀ hs₀'
  obtain ⟨w, hw, he⟩ := hB _ hst₀
  exact ⟨c'', hs'', fun hu => hu c'' hs'', w, hw, d₀, hd₀, he⟩

/-- **The backward half of RE up to export lists**, from the forward SpecTec leaf. -/
theorem bwdREX (c : Config H) (ts : List CValType) (w : Value) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hF : EraseFwdAt hn (Profile.spec nd r) host c)
    (hs : backendE.step (BI (Profile.spec nd r) hn host) (configV hn c) w) :
    ∃ c', Step (Profile.spec nd r) host c c' ∧ ExAgree hn c' w := by
  have hs₀ := storeOk_of_configOk hc
  have hf' := stripHostAt_finite hf c.store
  have hh' := stripHostAt_ok hh c.store
  obtain ⟨c₀, d₀, hd, hw, hst⟩ :=
    Round6.Target.bwdR_of_open hinj hf' (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) (Round6.Int.openR_backend hinj hf' hh') (stripConfig c) ts
      _ (configOk_strip hc) (boundedSel_strip hbc) (hF w hs)
  obtain ⟨c', hs', rfl⟩ := step_of_stripAt hs₀ hst
  exact ⟨c', hs', d₀, hd, hw⟩

end

/-- **RE up to export lists, from the SpecTec leaves**, for every injective encoding and finite
`HostOk` host, with neither `StripInj` nor any hypothesis on export names. -/
theorem stepValidREX_of_leaves : StepValidREX := fun _ _ hinj _ hf hh _ _ =>
  ⟨fun c c' ts hc hbc hB hsucc hs => fwdREX hinj hf hh c c' ts hc hbc hB hsucc hs,
    fun c ts w hc hbc hF hs => bwdREX hinj hf hh c ts w hc hbc hF hs⟩

/-! ## RE and REH from the three leaves -/

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) {nd : Bool} {r : RelaxedChoice}
include hinj hf hh

/-- The forward half of RE at one configuration, from its leaves. -/
theorem fwdRE_of_leaves (c c' : Config H) (ts : List CValType) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hB : EraseBwdAt hn (Profile.spec nd r) host c)
    (hE : ExactAt hn (Profile.spec nd r) host c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁)
    (hs : Step (Profile.spec nd r) host c c') :
    ∃ c'', Step (Profile.spec nd r) host c c'' ∧
      ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        backendE.step (BI (Profile.spec nd r) hn host) (configV hn c) (configV hn d') := by
  obtain ⟨c₁, hs₁, -, w, hw, hag⟩ := fwdREX hinj hf hh c c' ts hc hbc hB hsucc hs
  obtain ⟨c₂, d', hd', rfl, hs₂⟩ := hE c₁ w hs₁ hw hag
  exact ⟨c₂, hs₂, fun hu => hu c₂ hs₂, d', hd', hw⟩

/-- The backward half of RE at one configuration, from its leaves. -/
theorem bwdRE_of_leaves (c : Config H) (ts : List CValType) (w : Value) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hF : EraseFwdAt hn (Profile.spec nd r) host c)
    (hE : ExactAt hn (Profile.spec nd r) host c)
    (hs : backendE.step (BI (Profile.spec nd r) hn host) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c' := by
  obtain ⟨c₁, hs₁, hag⟩ := bwdREX hinj hf hh c ts w hc hbc hF hs
  exact hE c₁ w hs₁ hs hag

end

/-- **`Round7.Task.wholeStepValidRE` from the three leaves**, at `B := BI (Profile.spec nd r) hn
host`. The Core side is proved here with no `StripInj` and no host hypothesis on export names. -/
theorem wholeStepValidRE_of_leaves (h : LeavesRE) : Task.wholeStepValidRE :=
  fun H hn hinj host hf hh nd r =>
    ⟨BI (Profile.spec nd r) hn host,
      fun c c' ts hc hbc hsucc hs =>
        have hl := h H hn hinj host hf hh nd r c ts hc hbc
        fwdRE_of_leaves hinj hf hh c c' ts hc hbc hl.2.1 hl.2.2 hsucc hs,
      fun c ts w hc hbc hs =>
        have hl := h H hn hinj host hf hh nd r c ts hc hbc
        bwdRE_of_leaves hinj hf hh c ts w hc hbc hl.1 hl.2.2 hs⟩

/-- **`Round7.Task.wholeStepValidREH` from the three leaves at export-blind hosts.** -/
theorem wholeStepValidREH_of_leaves (h : LeavesREH) : Task.wholeStepValidREH :=
  fun H hn hinj host hf hh hb nd r =>
    ⟨BI (Profile.spec nd r) hn host,
      fun c c' ts hc hbc hsucc hs =>
        have hl := h H hn hinj host hf hh hb nd r c ts hc hbc
        fwdRE_of_leaves hinj hf hh c c' ts hc hbc hl.2.1 hl.2.2 hsucc hs,
      fun c ts w hc hbc hs =>
        have hl := h H hn hinj host hf hh hb nd r c ts hc hbc
        bwdRE_of_leaves hinj hf hh c ts w hc hbc hl.1 hl.2.2 hs⟩

/-- The leaves of RE contain those of REH. -/
theorem leavesREH_of_leavesRE (h : LeavesRE) : LeavesREH :=
  fun H hn hinj host hf hh _ nd r c ts hc hbc => h H hn hinj host hf hh nd r c ts hc hbc

/-! ## The leaves at export-blind hosts -/

/-- **At an export-blind host the forward SpecTec leaf is round 9's forward transfer**: it
follows from `BadFwdE` (8 rules) and `ElseBwdBLeft''` (9 pairs) at round 4's primitives, by
`ElseBwd.sStepB_fwd_BI_left''`, `Swap.eraseV_configV` and `Runs.agree_strip`. -/
theorem eraseFwdAt_of_blind {hn : H → String} {host : HostSemantics H}
    (hb : HostExportBlind host) (P : Profile)
    (hE : ElseBwd.BadFwdE (NxPrims.envBI P hn host))
    (hL : ElseBwd.ElseBwdBLeft'' (NxPrims.envBI P hn host)) (c : Config H) :
    EraseFwdAt hn P host c := by
  intro w hw
  have h₁ := ElseBwd.sStepB_fwd_BI_left'' P hn host hE hL hw
  rw [Swap.eraseV_configV] at h₁
  rw [stripHostAt_of_blind hb]
  exact (Runs.agree_strip hb P c _).mp h₁

/-- **At an export-blind host the backward SpecTec leaf** is a statement about one set of
builtins: a step of the round-6 reading from the stripped image lifts along `Swap.eraseV`. -/
theorem eraseBwdAt_blind_iff {hn : H → String} {host : HostSemantics H}
    (hb : HostExportBlind host) (P : Profile) (c : Config H) :
    EraseBwdAt hn P host c ↔
      ∀ w₀, Round6.Reading.SStepB (simEnv (BI P hn host)) (configV hn (stripConfig c)) w₀ →
        ∃ w, Round6.Reading.SStepB (utf8Env (BI P hn host)) (configV hn c) w ∧
          Swap.eraseV w = w₀ := by
  unfold EraseBwdAt
  rw [stripHostAt_of_blind hb]
  rfl

/-! ## The export leaves on the domain of `StepValidREM` -/

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) (hb : HostExportBlind host)
  (hm : HostMods.HostModsSub host) {nd : Bool} {r : RelaxedChoice}
include hinj hf hh hb hm

/-- **The export leaf at a `StripInj` configuration**, for an export-blind host that invents no
module (`HostMods.bwdREM`). -/
theorem exactAt_of_REM (c : Config H) (ts : List CValType) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hic : StripInj c) : ExactAt hn (Profile.spec nd r) host c :=
  fun _ w _ hw _ => HostMods.bwdREM hinj hf hh hb hm c ts w hc hbc hic hw

end

end Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip
