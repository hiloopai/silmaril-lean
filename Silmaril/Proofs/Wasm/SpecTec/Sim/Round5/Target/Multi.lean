module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Target.Assemble

/-!
# Round 5: the multi-step corollaries on `FloatMissel`-free runs

Pass 2's `Round5.Int2.fwdRel_of_open2`, `bwdRel_of_partsOkS`, `multiOk2_of_open2` and
`runs_of_open2`, and `steps_sim`, `ssteps_sim`, re-run with `BoundedSel` for
`Pos.BoundedNE`, so that both configurations are typed by `typed_of_configOk_selK` and the `simd`
leaf is no longer needed:

* `fwdRelSel_of_open5`: the forward relation `FwdRelSel` from `Open5`;
* `bwdRelSel_of_partsSel`, `bwdRelSel_of_open5`: the backward relation `BwdRelSel`, under
  `Multi.SuccTyped` and `Int2.WitnessBnd` as before;
* `multiSel_of_open5`, `runsSel_of_open5`: the run corollaries, from sources whose runs stay
  `BoundedSel` (`BoundedReachSel`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Target

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel SSteps)
open Round4Int (BI)
open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd (ConfigEq)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Forward -/

/-- `Obl` from `Open5`, at an injective encoding (`Int2.obl_of_open2`). -/
theorem obl_of_open5 (hinj : Function.Injective hn) (hf : HostFinite host)
    (O : Open5 hn P host) : Fwd.Obl (BI P hn host) hn P host :=
  FwdRef.oblT (Int.typesB _) hf (FwdRef2.hostRespectsT_all _ hinj host)
    (Fwd.rest_of O.refOk (SimdTy.vectorFwd_of_ops O.vecOps)
      fun _ _ h hb => Fwd.fwd_aggregate5 (Fwd.aggTypesB_of (Int.typesB _))
        (FwdRef.newDataNumB_builtins hn host) (Fwd.initDataZeroB_builtins hn host) h hb)

/-- **The forward relation, from `Open5`**, for an injective encoding and a finite `HostOk`
host. -/
theorem fwdRelSel_of_open5 (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (O : Open5 hn P host) : FwdRelSel (BI P hn host) hn P host := by
  intro c d c' _ hc hb hd hb' hs
  have htc' := typed_of_configOk_sel (BI P hn host) hn (Step.preservation hh hc hs).1 hb'
  obtain ⟨e, he, hte, hst⟩ := Multi.fwdResp_of_step_host (Int.typesB _)
    (Int2.hostCallsFwdT hf (FwdRef2.hostRespectsT_all _ hinj host)) (obl_of_open5 hinj hf O) hs
    hb.1.1 d hd.1 hd.2 htc'
  exact ⟨e, ⟨he, hte⟩, hst⟩

/-! ## Backward -/

/-- **The backward relation, from `PartsSel`, `SuccTyped` and `WitnessBnd`**, for a `HostOk`
host (`Int2.bwdRel_of_partsOkS`). -/
theorem bwdRelSel_of_partsSel (Pa : PartsSel hn P host) (hh : HostOk host)
    (ST : Multi.SuccTyped (BI P hn host) hn) (WB : Int2.WitnessBnd (BI P hn host) hn) :
    BwdRelSel (BI P hn host) hn P host := by
  intro c d ts w hc hb hsucc hd hs
  have hv₀ := Read.readValidS_of_bounded hc hb.1.1
  have hv := Int2.readValidS_of_configEq hd.1 hv₀ (WB c d hv₀.bnd hd.1 hd.2)
  obtain ⟨c₂, d₂, h₁, rfl, hst⟩ := backward_Sel Pa d w hv hd.2 hs
  obtain ⟨c', hst', h₂⟩ := Bwd.step_respects hst c (Round4.configEq_symm hd.1)
  have he : ConfigEq c' d₂ := Multi.configEq_trans (Round4.configEq_symm h₂) h₁
  have htc' := typed_of_configOk_selK Pa.pos (Step.preservation hh hc hst').1 (hsucc c' hst')
  exact ⟨c', d₂, ⟨he, ST d d₂ c' hd.2 hs he htc'⟩, rfl, hst'⟩

/-- **The backward relation, from `Open5`, `SuccTyped` and `WitnessBnd`.** -/
theorem bwdRelSel_of_open5 (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (hh : HostOk host) (O : Open5 hn P host) (ST : Multi.SuccTyped (BI P hn host) hn)
    (WB : Int2.WitnessBnd (BI P hn host) hn) : BwdRelSel (BI P hn host) hn P host :=
  bwdRelSel_of_partsSel (partsSel_of_open5 hinj hf hPs hPf O) hh ST WB

/-! ## Runs -/

variable {B : Builtins}

/-- **Core runs are SpecTec runs, along `SimRel`** (`Multi.steps_sim` with `BoundedSel`). -/
theorem stepsSel_sim (h : FwdRelSel B hn P host) (hhost : HostOk host) {c₀ d₀ : Config H}
    {ts : List CValType} (hc : ConfigOk c₀ ts) (hb : BoundedReachSel P host c₀)
    (hd : SimRel B hn c₀ d₀) {c : Config H} (hs : Steps P host c₀ c) :
    ∃ d, SimRel B hn c d ∧ SSteps (simEnv B) (configV hn d₀) (configV hn d) := by
  induction hs with
  | refl => exact ⟨d₀, hd, .refl⟩
  | @tail c₁ c₂ h₁ h₂ ih =>
    obtain ⟨d₁, hr₁, hr⟩ := ih
    have hok := (Steps.safe hhost hc h₁).1
    obtain ⟨d₂, hr₂, hst⟩ := h c₁ d₁ c₂ ts hok (hb c₁ h₁) hr₁ (hb c₂ (h₁.tail h₂)) h₂
    exact ⟨d₂, hr₂, hr.tail hst⟩

/-- **SpecTec runs are Core runs, along `SimRel`** (`Multi.ssteps_sim` with `BoundedSel`). -/
theorem sstepsSel_sim (h : BwdRelSel B hn P host) (hhost : HostOk host) {c₀ d₀ : Config H}
    {ts : List CValType} (hc : ConfigOk c₀ ts) (hb : BoundedReachSel P host c₀)
    (hd : SimRel B hn c₀ d₀) {w : Value} (hs : SSteps (simEnv B) (configV hn d₀) w) :
    ∃ c d, SimRel B hn c d ∧ w = configV hn d ∧ Steps P host c₀ c := by
  induction hs with
  | refl => exact ⟨c₀, d₀, hd, rfl, .refl⟩
  | @tail w₁ w₂ _ h₂ ih =>
    obtain ⟨c₁, d₁, hr₁, rfl, hs₁⟩ := ih
    have hok := (Steps.safe hhost hc hs₁).1
    obtain ⟨c₂, d₂, hr₂, hw, hst⟩ := h c₁ d₁ ts w₂ hok (hb c₁ hs₁)
      (fun c' h' => hb c' (hs₁.tail h')) hr₁ h₂
    exact ⟨c₂, d₂, hr₂, hw, hs₁.tail hst⟩

/-- **`MultiSel` from the leaves `Open5`**, with `B := Prims.builtins`. Vacuous as stated
(`not_open5_spec`). -/
theorem multiSel_of_open5
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open5 hn (Profile.spec nd r) host) :
    MultiSel := fun H hn hinj host hfin hok nd r =>
  have O := h H hn hinj host hfin hok nd r
  ⟨_, fwdRelSel_of_open5 hinj hfin hok O,
    bwdRelSel_of_open5 hinj hfin (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r)
      hok O⟩

/-- **The run corollaries of `Task.wholeStepValidSel`, from `Open5`**, at one injective
encoding, finite `HostOk` host and `Profile.spec nd r`, with `B := Prims.builtins`
(`Int2.runs_of_open2` with `BoundedReachSel` for `Multi.BoundedReachNE`). -/
theorem runsSel_of_open5 {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) (O : Open5 hn (Profile.spec nd r) host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → Steps (Profile.spec nd r) host c₀ c →
      ∃ d, ConfigEq c d ∧
        SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) (configV hn d)) ∧
    (Multi.SuccTyped (BI (Profile.spec nd r) hn host) hn →
      Int2.WitnessBnd (BI (Profile.spec nd r) hn host) hn →
      ∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ →
      SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) w →
      ∃ c d, ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) := by
  have h₀ {c₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
      (hb : BoundedReachSel (Profile.spec nd r) host c₀) :
      SimRel (BI (Profile.spec nd r) hn host) hn c₀ c₀ :=
    ⟨Bwd.ConfigEq.refl c₀, typed_of_configOk_sel _ hn hc (hb c₀ .refl)⟩
  refine ⟨fun c₀ c ts hc hb hs => ?_, fun ST WB c₀ ts w hc hb hs => ?_⟩
  · obtain ⟨d, hr, hss⟩ := stepsSel_sim (fwdRelSel_of_open5 hinj hf hh O) hh hc hb (h₀ hc hb) hs
    exact ⟨d, hr.1, hss⟩
  · have hB := bwdRelSel_of_open5 hinj hf (BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) hh O ST WB
    obtain ⟨c, d, hr, hw, hss⟩ := sstepsSel_sim hB hh hc hb (h₀ hc hb) hs
    exact ⟨c, d, hr.1, hw, hss⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Target
