module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.ForwardResp
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.Assemble
public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi4.Thms

/-!
# Round 6: the multi-step corollary

* `castRedex_of_codeEq`: SpecTec witnesses (`ConfigEq`, call annotations only) have the same cast
  redexes, so the case split of `OpenR` can be made on the witness.
* `fwdRelR_of_open`, `bwdRelR_of_open`: the one-step simulations along `SimRel`, from every
  typed witness `d ≈ c`, under `OpenR`. Away from cast redexes they are `fwdRespR_of` and
  `backwardNC` (proved), with `Round5.Multi.succTyped` and
  `Round5.Multi.witnessBnd` for the successor witness.
* `stepsR_sim`, `sstepsR_sim`, `runsR_of_open`: the multi-step corollary. Every Core run from a
  valid source whose runs stay `BoundedSel`, in which **every step goes to Core's only
  successor** (`DetSteps`), is a run of the reading up to `ConfigEq`; and every run of the
  reading from it is the image of a Core run up to `ConfigEq`. (A run through a nondeterministic
  Core step cannot be followed in general: SpecTec may take the other successor.)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Target

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel)
open Round4Int (BI)
open Round5.Target (BoundedSel BoundedReachSel typed_of_configOk_sel)
open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd (ConfigEq CodeEq AdminEq)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Witnesses have the same cast redexes -/

/-- A value is related only to itself. -/
theorem adminEq_toAdmin {v : Val} {x : Admin} (h : AdminEq v.toAdmin x) : x = v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> cases h <;> simp_all [Admin.IsCallRef, Val.toAdmin]

/-- A cast instruction is related only to itself. -/
theorem adminEq_cast {i : Instr} {x : Admin} (hi : castInstr i = true)
    (h : AdminEq (.plain i) x) : x = .plain i := by
  cases h with
  | refl => rfl
  | call h₁ _ => cases i <;> simp_all [Admin.IsCallRef, castInstr]

/-- A label is related to a label with a related body. -/
theorem adminEq_label {n : Nat} {cont : List Instr} {b : List Admin} {x : Admin}
    (h : AdminEq (.label n cont b) x) : ∃ b', x = .label n cont b' ∧ CodeEq b b' := by
  cases h with
  | refl => exact ⟨b, rfl, Bwd.CodeEq.refl _⟩
  | call h₁ _ => simp [Admin.IsCallRef] at h₁
  | label hj => exact ⟨_, rfl, hj⟩

/-- A handler is related to a handler with a related body. -/
theorem adminEq_handler {n : Nat} {cs : List Catch} {b : List Admin} {x : Admin}
    (h : AdminEq (.handler n cs b) x) : ∃ b', x = .handler n cs b' ∧ CodeEq b b' := by
  cases h with
  | refl => exact ⟨b, rfl, Bwd.CodeEq.refl _⟩
  | call h₁ _ => simp [Admin.IsCallRef] at h₁
  | handler hj => exact ⟨_, rfl, hj⟩

/-- A frame is related to a frame with a related body. -/
theorem adminEq_frame {n : Nat} {fi : Frame} {b : List Admin} {x : Admin}
    (h : AdminEq (.frame n fi b) x) : ∃ b', x = .frame n fi b' ∧ CodeEq b b' := by
  cases h with
  | refl => exact ⟨b, rfl, Bwd.CodeEq.refl _⟩
  | call h₁ _ => simp [Admin.IsCallRef] at h₁
  | frame hj => exact ⟨_, rfl, hj⟩

/-- **A cast redex is one in every witness.** -/
theorem castRedex_of_codeEq {a : List Admin} (h : CastRedex a) :
    ∀ {b : List Admin}, CodeEq a b → CastRedex b := by
  induction h with
  | skip _ ih =>
      intro b hb
      cases hb with
      | cons ha hl => exact adminEq_toAdmin ha ▸ .skip (ih hl)
  | cast hi =>
      intro b hb
      cases hb with
      | cons ha _ => exact adminEq_cast hi ha ▸ .cast hi
  | label _ ih =>
      intro b hb
      cases hb with
      | cons ha _ =>
          exact (adminEq_label ha).elim fun _ ⟨hx, hj⟩ => hx ▸ .label (ih hj)
  | handler _ ih =>
      intro b hb
      cases hb with
      | cons ha _ =>
          exact (adminEq_handler ha).elim fun _ ⟨hx, hj⟩ => hx ▸ .handler (ih hj)
  | frame _ ih =>
      intro b hb
      cases hb with
      | cons ha _ =>
          exact (adminEq_frame ha).elim fun _ ⟨hx, hj⟩ => hx ▸ .frame (ih hj)

/-! ## The one-step simulations along `SimRel` -/

/-- **The forward one-step simulation along `SimRel`, up to Core's choice**, from `OpenR`. -/
theorem fwdRelR_of_open {Rd : Reading} (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (O : OpenR Rd hn P host) (c d c' : Config H) (ts : List CValType)
    (hc : ConfigOk c ts) (hb : BoundedSel c) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁)
    (hd : SimRel (BI P hn host) hn c d) (hs : Step P host c c') :
    ∃ c'' d'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      SimRel (BI P hn host) hn c'' d'' ∧
      Rd.step (BI P hn host) (configV hn d) (configV hn d'') := by
  by_cases hx : CastRedex d.code
  · obtain ⟨d', hd', hst⟩ := O.casts.fwd c d c' ts hc hb hsucc hd hx hs
    exact ⟨c', d', hs, fun _ => rfl, hd', hst⟩
  have hxc : ¬ CastRedex c.code := fun h => hx (castRedex_of_codeEq h hd.1.2.2)
  obtain ⟨c'', hs'', hu, hresp⟩ := fwdRespR_of hinj hf hs hb.1.1 hxc
  have htc'' : Typed (simEnv (BI P hn host)) hn c'' :=
    typed_of_configOk_sel _ hn (Step.preservation hh hc hs'').1 (hsucc c'' hs'')
  obtain ⟨e, he, hte, hst⟩ := hresp d hd.1 hd.2 htc''
  exact ⟨c'', e, hs'', hu, ⟨he, hte⟩, O.transfer.fwd c d ts _ hc hb hd hx hst⟩

/-- **The backward one-step simulation along `SimRel`**, from `OpenR`, from a source whose Core
successors are all `BoundedSel`. -/
theorem bwdRelR_of_open {Rd : Reading} (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (O : OpenR Rd hn P host) (c d : Config H)
    (ts : List CValType) (w : Value) (hc : ConfigOk c ts) (hb : BoundedSel c)
    (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁) (hd : SimRel (BI P hn host) hn c d)
    (hs : Rd.step (BI P hn host) (configV hn d) w) :
    ∃ c' d', SimRel (BI P hn host) hn c' d' ∧ w = configV hn d' ∧ Step P host c c' := by
  by_cases hx : CastRedex d.code
  · obtain ⟨c', d', he, hty, hw, hst⟩ := O.casts.bwd c d ts w hc hb hd hx hs
    have htc' : Typed (simEnv (BI P hn host)) hn c' :=
      typed_of_configOk_sel _ hn (Step.preservation hh hc hst).1 (hsucc c' hst)
    exact ⟨c', d', ⟨he, hty htc'⟩, hw, hst⟩
  have hs₀ := O.transfer.bwd c d ts w hc hb hd hx hs
  have hv₀ := Round5.Read.readValidS_of_bounded hc hb.1.1
  have hv : Round5.Read.ReadValidS d := Round5.Int2.readValidS_of_configEq hd.1 hv₀
    (Round5.Multi.witnessBnd _ hn c d hv₀.bnd hd.1 hd.2)
  obtain ⟨c₂, d₂, h₁, rfl, hst⟩ := backwardNC hinj hf hPs hPf d w ⟨hv, hx⟩ hd.2 hs₀
  obtain ⟨c', hst', h₂⟩ := Bwd.step_respects hst c (Round4.configEq_symm hd.1)
  have he : ConfigEq c' d₂ := Round5.Multi.configEq_trans (Round4.configEq_symm h₂) h₁
  have htc' : Typed (simEnv (BI P hn host)) hn c' :=
    typed_of_configOk_sel _ hn (Step.preservation hh hc hst').1 (hsucc c' hst')
  exact ⟨c', d₂, ⟨he, Round5.Multi.succTyped _ hn d d₂ c' hd.2 hs₀ he htc'⟩, rfl, hst'⟩

/-! ## Runs -/

/-- A deterministic run is a run. -/
theorem steps_of_detSteps {c₀ c : Config H} (h : DetSteps P host c₀ c) : Steps P host c₀ c := by
  induction h with
  | refl => exact .refl
  | tail _ h₂ ih => exact ih.tail h₂.1

/-- **Deterministic Core runs are runs of the reading, along `SimRel`.** -/
theorem stepsR_sim {Rd : Reading} (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (O : OpenR Rd hn P host) {c₀ d₀ : Config H} {ts : List CValType}
    (hc : ConfigOk c₀ ts) (hb : BoundedReachSel P host c₀)
    (hd : SimRel (BI P hn host) hn c₀ d₀) {c : Config H} (hs : DetSteps P host c₀ c) :
    ∃ d, SimRel (BI P hn host) hn c d ∧
      RSteps Rd (BI P hn host) (configV hn d₀) (configV hn d) := by
  induction hs with
  | refl => exact ⟨d₀, hd, .refl⟩
  | @tail c₁ c₂ h₁ h₂ ih =>
    obtain ⟨d₁, hr₁, hr⟩ := ih
    have hrun : Steps P host c₀ c₁ := steps_of_detSteps h₁
    have hok := (Steps.safe hh hc hrun).1
    obtain ⟨c'', d₂, -, hu, hr₂, hst⟩ := fwdRelR_of_open hinj hf hh O c₁ d₁ c₂ ts hok
      (hb c₁ hrun) (fun c' h' => hb c' (hrun.tail h')) hr₁ h₂.1
    obtain rfl := hu h₂.2
    exact ⟨d₂, hr₂, hr.tail hst⟩

/-- **Runs of the reading are Core runs, along `SimRel`.** -/
theorem sstepsR_sim {Rd : Reading} (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (O : OpenR Rd hn P host) {c₀ d₀ : Config H}
    {ts : List CValType} (hc : ConfigOk c₀ ts) (hb : BoundedReachSel P host c₀)
    (hd : SimRel (BI P hn host) hn c₀ d₀) {w : Value}
    (hs : RSteps Rd (BI P hn host) (configV hn d₀) w) :
    ∃ c d, SimRel (BI P hn host) hn c d ∧ w = configV hn d ∧ Steps P host c₀ c := by
  induction hs with
  | refl => exact ⟨c₀, d₀, hd, rfl, .refl⟩
  | @tail w₁ w₂ _ h₂ ih =>
    obtain ⟨c₁, d₁, hr₁, rfl, hs₁⟩ := ih
    have hok := (Steps.safe hh hc hs₁).1
    obtain ⟨c₂, d₂, hr₂, hw, hst⟩ := bwdRelR_of_open hinj hf hh hPs hPf O c₁ d₁ ts w₂ hok
      (hb c₁ hs₁) (fun c' h' => hb c' (hs₁.tail h')) hr₁ h₂
    exact ⟨c₂, d₂, hr₂, hw, hs₁.tail hst⟩

/-- **The multi-step corollary of `Task.wholeStepValidR Rd`, from `OpenR Rd`**, at one injective
encoding, finite `HostOk` host and `Profile.spec nd r`, with `B := Prims.builtins`, from valid
sources whose runs stay `BoundedSel`: deterministic Core runs are runs of the reading, and runs
of the reading are Core runs, both up to `ConfigEq`. -/
theorem runsR_of_open {Rd : Reading} {nd : Bool} {r : RelaxedChoice}
    (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (O : OpenR Rd hn (Profile.spec nd r) host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, ConfigEq c d ∧
        RSteps Rd (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ →
      RSteps Rd (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) := by
  have h₀ {c₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
      (hb : BoundedReachSel (Profile.spec nd r) host c₀) :
      SimRel (BI (Profile.spec nd r) hn host) hn c₀ c₀ :=
    ⟨Bwd.ConfigEq.refl c₀, typed_of_configOk_sel _ hn hc (hb c₀ .refl)⟩
  refine ⟨fun c₀ c ts hc hb hs => ?_, fun c₀ ts w hc hb hs => ?_⟩
  · obtain ⟨d, hr, hss⟩ := stepsR_sim hinj hf hh O hc hb (h₀ hc hb) hs
    exact ⟨d, hr.1, hss⟩
  · obtain ⟨c, d, hr, hw, hss⟩ := sstepsR_sim hinj hf hh (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) O hc hb (h₀ hc hb) hs
    exact ⟨c, d, hr.1, hw, hss⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Target
