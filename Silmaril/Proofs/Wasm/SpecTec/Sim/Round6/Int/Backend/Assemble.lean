module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Backend.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Casts.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.Thms

/-!
# SpecTec ↔ Core 3.0, round 6, integration (pass 2): the target at the backend reading

Pass 2 put the two leaves of `Target.OpenR Int.backend` side by side:

* track transfer proved `Target.Transfer Int.backend` outright
  (`Transfer.transfer_backend_BI`);
* track casts proved `Target.Casts Int.backend` from `Reading.RefOkBB`
  (`Casts.casts_backend_spec_of_refOkBB`);
* track refokbb refuted `Reading.RefOkBB (simEnv B)` for every `B` (`RefOkB.not_refOkBB`).

So the route to `Round6.Task.wholeStepValidR Int.backend` through `RefOkBB` is closed. This file
records what the three tracks give together:

* `openR_backend_of_refOkBB`, `wholeStepValidR_backend_of_refOkBB`, `runsR_backend_of_refOkBB`:
  the target and its multi-step corollary from `RefOkBB`; **vacuous**, since the hypothesis
  family is false (`not_refOkBB_family`).
* `wholeStepValidRNC_backend` (**proved outright**): the target with `¬ CastRedex c.code` added
  to both halves, from track transfer and track target's cast-free halves (`forwardR'`,
  `backwardNC`). `wholeStepValidRNC_of_wholeStepValidR`: it is a restriction of the target.
* `runsRNC_backend` (**proved outright**): its multi-step corollary, for sources from which no
  reachable Core configuration has a cast redex (`NoCastReach`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Int

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel)
open Round4Int (BI)
open Round5.Target (BoundedSel BoundedReachSel typed_of_configOk_sel)
open Target (CastRedex DetSteps RSteps)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## The route through `RefOkBB` (vacuous) -/

/-- `Target.OpenR Int.backend` from `RefOkBB`: track transfer's transfer lemma and track casts'
cast leaf. -/
theorem openR_backend_of_refOkBB {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (KB : Reading.RefOkBB (simEnv (BI (Profile.spec nd r) hn host))) :
    Target.OpenR backend hn (Profile.spec nd r) host :=
  ⟨Transfer.transfer_backend_BI hn _ host, Casts.casts_backend_spec_of_refOkBB hinj hf hh KB⟩

/-- **`Round6.Task.wholeStepValidR Int.backend` from `RefOkBB`** at every injective encoding,
finite `HostOk` host and spec profile. Vacuous: `not_refOkBB_family`. -/
theorem wholeStepValidR_backend_of_refOkBB
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice),
          Reading.RefOkBB (simEnv (BI (Profile.spec nd r) hn host))) :
    Round6.Task.wholeStepValidR backend :=
  wholeStepValidR_backend_of_open fun H hn hinj host hf hh nd r =>
    openR_backend_of_refOkBB hinj hf hh (h H hn hinj host hf hh nd r)

/-- **The multi-step corollary at the backend reading, from `RefOkBB`** (`Target.runsR_of_open`
at `Int.backend`). Vacuous: `RefOkB.not_refOkBB`. -/
theorem runsR_backend_of_refOkBB {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (KB : Reading.RefOkBB (simEnv (BI (Profile.spec nd r) hn host))) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        RSteps backend (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ →
      RSteps backend (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  Target.runsR_of_open hinj hf hh (openR_backend_of_refOkBB hinj hf hh KB)

/-- **The hypothesis of `wholeStepValidR_backend_of_refOkBB` is false**: `RefOkBB` fails at
every `B` (`RefOkB.not_refOkBB`), in particular at round 5's unit host. -/
theorem not_refOkBB_family :
    ¬ ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice),
          Reading.RefOkBB (simEnv (BI (Profile.spec nd r) hn host)) := fun h =>
  RefOkB.not_refOkBB _ (h Unit Round5.Pos.hnU Round5.Pos.hnU_injective Round5.Pos.divHost
    Round5.Pos.hostFinite_divHost Round5.Pos.hostOk_divHost false {})

/-! ## Away from cast redexes (proved outright) -/

/-- The full target gives its cast-free restriction. -/
theorem wholeStepValidRNC_of_wholeStepValidR {Rd : Target.Reading}
    (h : Round6.Task.wholeStepValidR Rd) : wholeStepValidRNC Rd :=
  fun H hn hinj host hf hh nd r =>
    (h H hn hinj host hf hh nd r).imp fun _ hB =>
      ⟨fun c c' ts hc hb _ => hB.1 c c' ts hc hb, fun c ts w hc hb _ => hB.2 c ts w hc hb⟩

/-- **The forward half at the backend reading, away from cast redexes**: track target's
`forwardR'` carried through track transfer's transfer lemma. -/
theorem fwdNC (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (c c' : Config H) (ts : List CValType) (hc : ConfigOk c ts) (hb : BoundedSel c)
    (hx : ¬ CastRedex c.code) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁)
    (hs : Step P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ backend.step (BI P hn host) (configV hn c) (configV hn d') := by
  have htc := typed_of_configOk_sel (BI P hn host) hn hc hb
  have hr : SimRel (BI P hn host) hn c c := ⟨Bwd.ConfigEq.refl c, htc⟩
  obtain ⟨c'', hs'', hu, hfu⟩ := Target.forwardR' hinj hf hs hb.1.1 hx
  have htc'' := typed_of_configOk_sel (BI P hn host) hn (Step.preservation hh hc hs'').1
    (hsucc c'' hs'')
  obtain ⟨d', hd', -, hst⟩ := hfu htc htc''
  exact ⟨c'', hs'', hu, d', hd',
    (Transfer.transfer_backend_BI hn P host).fwd c c ts _ hc hb hr hx hst⟩

/-- **The backward half at the backend reading, away from cast redexes**: track transfer's
transfer lemma followed by `backwardNC`. -/
theorem bwdNC (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (c : Config H) (ts : List CValType) (w : Value) (hc : ConfigOk c ts) (hb : BoundedSel c)
    (hx : ¬ CastRedex c.code) (hs : backend.step (BI P hn host) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  have htc := typed_of_configOk_sel (BI P hn host) hn hc hb
  Target.backwardNC hinj hf hPs hPf c w ⟨Round5.Read.readValidS_of_bounded hc hb.1.1, hx⟩ htc
    ((Transfer.transfer_backend_BI hn P host).bwd c c ts w hc hb ⟨Bwd.ConfigEq.refl c, htc⟩ hx hs)

/-- **The round-6 target at the backend reading, away from cast redexes, proved outright.** -/
theorem wholeStepValidRNC_backend : wholeStepValidRNC backend :=
  fun _ _ hinj _ hf hh nd r =>
    ⟨_, fun c c' ts hc hb hx hsucc hs => fwdNC hinj hf hh c c' ts hc hb hx hsucc hs,
      fun c ts w hc hb hx hs => bwdNC hinj hf (Round5.BwdStep.growMaySucceed_spec nd r)
        (Round4.growMayFail_spec nd r) c ts w hc hb hx hs⟩

/-! ## Runs away from cast redexes (proved outright) -/

/-- A witness of a configuration without a cast redex has none. -/
theorem not_castRedex_witness {c d : Config H} (he : Bwd.ConfigEq c d)
    (hx : ¬ CastRedex c.code) : ¬ CastRedex d.code := fun h =>
  hx (Target.castRedex_of_codeEq h (Round4.configEq_symm he).2.2)

/-- **The forward one-step simulation along `SimRel` at the backend reading, away from cast
redexes**: `fwdRelR_of_open` without its cast branch. -/
theorem fwdRelNC (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (c d c' : Config H) (ts : List CValType) (hc : ConfigOk c ts) (hb : BoundedSel c)
    (hxc : ¬ CastRedex c.code) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁)
    (hd : SimRel (BI P hn host) hn c d) (hs : Step P host c c') :
    ∃ c'' d'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      SimRel (BI P hn host) hn c'' d'' ∧
      backend.step (BI P hn host) (configV hn d) (configV hn d'') := by
  obtain ⟨c'', hs'', hu, hresp⟩ := Target.fwdRespR_of hinj hf hs hb.1.1 hxc
  have htc'' : Typed (simEnv (BI P hn host)) hn c'' :=
    typed_of_configOk_sel _ hn (Step.preservation hh hc hs'').1 (hsucc c'' hs'')
  obtain ⟨e, he, hte, hst⟩ := hresp d hd.1 hd.2 htc''
  exact ⟨c'', e, hs'', hu, ⟨he, hte⟩, (Transfer.transfer_backend_BI hn P host).fwd c d ts _ hc
    hb hd (not_castRedex_witness hd.1 hxc) hst⟩

/-- **The backward one-step simulation along `SimRel` at the backend reading, away from cast
redexes**: `bwdRelR_of_open` without its cast branch. -/
theorem bwdRelNC (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (c d : Config H) (ts : List CValType) (w : Value) (hc : ConfigOk c ts) (hb : BoundedSel c)
    (hxc : ¬ CastRedex c.code) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁)
    (hd : SimRel (BI P hn host) hn c d) (hs : backend.step (BI P hn host) (configV hn d) w) :
    ∃ c' d', SimRel (BI P hn host) hn c' d' ∧ w = configV hn d' ∧ Step P host c c' := by
  have hx := not_castRedex_witness hd.1 hxc
  have hs₀ := (Transfer.transfer_backend_BI hn P host).bwd c d ts w hc hb hd hx hs
  have hv₀ := Round5.Read.readValidS_of_bounded hc hb.1.1
  have hv : Round5.Read.ReadValidS d := Round5.Int2.readValidS_of_configEq hd.1 hv₀
    (Round5.Multi.witnessBnd _ hn c d hv₀.bnd hd.1 hd.2)
  obtain ⟨c₂, d₂, h₁, rfl, hst⟩ := Target.backwardNC hinj hf hPs hPf d w ⟨hv, hx⟩ hd.2 hs₀
  obtain ⟨c', hst', h₂⟩ := Bwd.step_respects hst c (Round4.configEq_symm hd.1)
  have he : Bwd.ConfigEq c' d₂ := Round5.Multi.configEq_trans (Round4.configEq_symm h₂) h₁
  have htc' : Typed (simEnv (BI P hn host)) hn c' :=
    typed_of_configOk_sel _ hn (Step.preservation hh hc hst').1 (hsucc c' hst')
  exact ⟨c', d₂, ⟨he, Round5.Multi.succTyped _ hn d d₂ c' hd.2 hs₀ he htc'⟩, rfl, hst'⟩

/-- **Deterministic cast-free Core runs are runs of the backend reading, along `SimRel`.** -/
theorem stepsNC_sim (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    {c₀ d₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
    (hb : BoundedReachSel P host c₀) (hn₀ : NoCastReach P host c₀)
    (hd : SimRel (BI P hn host) hn c₀ d₀) {c : Config H} (hs : DetSteps P host c₀ c) :
    ∃ d, SimRel (BI P hn host) hn c d ∧
      RSteps backend (BI P hn host) (configV hn d₀) (configV hn d) := by
  induction hs with
  | refl => exact ⟨d₀, hd, .refl⟩
  | @tail c₁ c₂ h₁ h₂ ih =>
    obtain ⟨d₁, hr₁, hr⟩ := ih
    have hrun : Steps P host c₀ c₁ := Target.steps_of_detSteps h₁
    obtain ⟨c'', d₂, -, hu, hr₂, hst⟩ := fwdRelNC hinj hf hh c₁ d₁ c₂ ts
      (Steps.safe hh hc hrun).1 (hb c₁ hrun) (hn₀ c₁ hrun) (fun c' h' => hb c' (hrun.tail h'))
      hr₁ h₂.1
    obtain rfl := hu h₂.2
    exact ⟨d₂, hr₂, hr.tail hst⟩

/-- **Runs of the backend reading from a cast-free source are Core runs, along `SimRel`.** -/
theorem sstepsNC_sim (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    {c₀ d₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
    (hb : BoundedReachSel P host c₀) (hn₀ : NoCastReach P host c₀)
    (hd : SimRel (BI P hn host) hn c₀ d₀) {w : Value}
    (hs : RSteps backend (BI P hn host) (configV hn d₀) w) :
    ∃ c d, SimRel (BI P hn host) hn c d ∧ w = configV hn d ∧ Steps P host c₀ c := by
  induction hs with
  | refl => exact ⟨c₀, d₀, hd, rfl, .refl⟩
  | @tail w₁ w₂ _ h₂ ih =>
    obtain ⟨c₁, d₁, hr₁, rfl, hs₁⟩ := ih
    obtain ⟨c₂, d₂, hr₂, hw, hst⟩ := bwdRelNC hinj hf hh hPs hPf c₁ d₁ ts w₂
      (Steps.safe hh hc hs₁).1 (hb c₁ hs₁) (hn₀ c₁ hs₁) (fun c' h' => hb c' (hs₁.tail h')) hr₁ h₂
    exact ⟨c₂, d₂, hr₂, hw, hs₁.tail hst⟩

/-- **The multi-step corollary of `wholeStepValidRNC_backend`, proved outright**, at one
injective encoding, finite `HostOk` host and `Profile.spec nd r`, from valid sources whose runs
stay `BoundedSel` and never reach a cast redex: deterministic Core runs are runs of the backend
reading, and runs of the backend reading are Core runs, both up to `ConfigEq`. -/
theorem runsRNC_backend {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → NoCastReach (Profile.spec nd r) host c₀ →
      DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        RSteps backend (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → NoCastReach (Profile.spec nd r) host c₀ →
      RSteps backend (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) := by
  have h₀ {c₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
      (hb : BoundedReachSel (Profile.spec nd r) host c₀) :
      SimRel (BI (Profile.spec nd r) hn host) hn c₀ c₀ :=
    ⟨Bwd.ConfigEq.refl c₀, typed_of_configOk_sel _ hn hc (hb c₀ .refl)⟩
  refine ⟨fun c₀ c ts hc hb hx hs => ?_, fun c₀ ts w hc hb hx hs => ?_⟩
  · obtain ⟨d, hr, hss⟩ := stepsNC_sim hinj hf hh hc hb hx (h₀ hc hb) hs
    exact ⟨d, hr.1, hss⟩
  · obtain ⟨c, d, hr, hw, hss⟩ := sstepsNC_sim hinj hf hh (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) hc hb hx (h₀ hc hb) hs
    exact ⟨c, d, hr.1, hw, hss⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Int
