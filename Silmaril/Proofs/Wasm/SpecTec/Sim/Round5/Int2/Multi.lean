module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Int2.Assemble
public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi.Thms

/-!
# Round 5, pass-2 integration: the multi-step corollary from `Open2`

Track multi proved the run corollaries from pass 1's `Int.Open`, which can never hold
(`Round5.FwdRef.not_open_all`). This file proves them again from `Open2`.

* `hostCallsFwdT`: the host `call_ref` rules forward from `HostRespectsT`.
* `obl_of_open2`, `fwdRel_of_open2`: the forward relation `Multi.FwdRel`, through
  `Multi.fwdResp_of_step_host`.
* `codeSeg_of_eq`, `readValidS_of_configEq`: `ReadValidS` carries over along
  `ConfigEq` when the witness's code is bounded.
* `bwdRel_of_partsOkS`, `bwdRel_of_open2`: the backward relation under `SuccTyped` and
  `WitnessBnd`.
* `multiOk2_of_open2`, `runs_of_open2`: the run corollaries.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Int2

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel SSteps)
open Round4Int (BI)
open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd (AdminEq CodeEq ConfigEq)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Forward -/

/-- The host `call_ref` rules forward, from `HostRespectsT`. -/
theorem hostCallsFwdT (hf : HostFinite host)
    (hr : FwdRef.HostRespectsT (simEnv (BI P hn host)) hn host) :
    Multi.HostCallsFwd (BI P hn host) hn host :=
  ⟨fun hc hfa hex hlen hcode hh hd =>
      FwdRef.fwd_callRefHostT (Int.typesB _) hf hr hc hfa hex hlen hcode hh hd,
    fun hc hfa hex hlen hcode hh hd =>
      FwdRef.fwd_callRefHostDivT (Int.typesB _) hf hr hc hfa hex hlen hcode hh hd⟩

/-- `Obl` from `Open2` (as in `FwdRef.forward_validT`). -/
theorem obl_of_open2 (hf : HostFinite host) (O : Open2 hn P host) :
    Fwd.Obl (BI P hn host) hn P host :=
  FwdRef.oblT (Int.typesB _) hf O.hostRespects (Fwd.rest_of O.refOk O.vector
    fun _ _ h hb => Fwd.fwd_aggregate5 (Fwd.aggTypesB_of (Int.typesB _))
      (FwdRef.newDataNumB_builtins hn host) (Fwd.initDataZeroB_builtins hn host) h hb)

/-- **The forward relation, from `Open2`**, for a finite `HostOk` host. -/
theorem fwdRel_of_open2 (hf : HostFinite host) (hh : HostOk host) (O : Open2 hn P host) :
    Multi.FwdRel (BI P hn host) hn P host := by
  intro c d c' _ hc hb hd hb' hs
  have K := Pos.posTypingNE_of_simd O.simd hn
  have htc' := Pos.typed_of_configOk_ne K (Step.preservation hh hc hs).1 hb'
  obtain ⟨e, he, hte, hst⟩ := Multi.fwdResp_of_step_host (Int.typesB _)
    (hostCallsFwdT hf O.hostRespects) (obl_of_open2 hf O) hs hb.1 d hd.1 hd.2 htc'
  exact ⟨e, ⟨he, hte⟩, hst⟩

/-! ## `ReadValidS` along `ConfigEq` -/

mutual
/-- The segment conditions transfer along `AdminEq`. -/
theorem adminSeg_of_eq {s : Store H} :
    ∀ {f : Frame} {a b : Admin}, AdminEq a b → Round5.Read.adminSeg s f a →
      Round5.Read.adminSeg s f b
  | _, _, _, .refl _, h => h
  | _, _, _, .call _ hb, _ => by
    rcases Bwd.isCallRef_cases hb with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> trivial
  | _, _, _, .label h₁, h => codeSeg_of_eq h₁ h
  | _, _, _, .handler h₁, h => codeSeg_of_eq h₁ h
  | _, _, _, .frame h₁, h => codeSeg_of_eq h₁ h

/-- The segment conditions transfer along `CodeEq`. -/
theorem codeSeg_of_eq {s : Store H} :
    ∀ {f : Frame} {l j : List Admin}, CodeEq l j → Round5.Read.codeSeg s f l →
      Round5.Read.codeSeg s f j
  | _, _, _, .nil, h => h
  | _, _, _, .cons ha hl, h => ⟨adminSeg_of_eq ha h.1, codeSeg_of_eq hl h.2⟩
end

/-- **`ReadValidS` transfers along `ConfigEq`** to a witness with bounded code. -/
theorem readValidS_of_configEq {c d : Config H} (h : ConfigEq c d)
    (hv : Round5.Read.ReadValidS c) (hb : Round4.AdminsBnd d.code) :
    Round5.Read.ReadValidS d := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', code'⟩ := d
  obtain ⟨hs, hf, hc⟩ := h
  cases hs
  cases hf
  have hr := Multi.readValidR_of_configEq (c := ⟨s, f, code⟩) (d := ⟨s, f, code'⟩) ⟨rfl, rfl, hc⟩
    hv.r
  exact ⟨hr, codeSeg_of_eq hc hv.seg, hb, hv.frame⟩

/-! ## Backward -/

/-- **The backward relation, from `PartsOkS`, `SuccTyped` and `WitnessBnd`**, for a `HostOk`
host. -/
theorem bwdRel_of_partsOkS (Pa : Round5.Read.PartsOkS hn P host) (hh : HostOk host)
    (ST : Multi.SuccTyped (BI P hn host) hn) (WB : WitnessBnd (BI P hn host) hn) :
    Multi.BwdRel (BI P hn host) hn P host := by
  intro c d ts w hc hb hsucc hd hs
  have hv₀ := Round5.Read.readValidS_of_bounded hc hb.1
  have hv := readValidS_of_configEq hd.1 hv₀ (WB c d hv₀.bnd hd.1 hd.2)
  obtain ⟨c₂, d₂, h₁, rfl, hst⟩ := Round5.Read.backward_S Pa d w hv hd.2 hs
  obtain ⟨c', hst', h₂⟩ := Bwd.step_respects hst c (Round4.configEq_symm hd.1)
  have he : ConfigEq c' d₂ := Multi.configEq_trans (Round4.configEq_symm h₂) h₁
  have htc' := Pos.typed_of_configOk_ne Pa.pos (Step.preservation hh hc hst').1 (hsucc c' hst')
  exact ⟨c', d₂, ⟨he, ST d d₂ c' hd.2 hs he htc'⟩, rfl, hst'⟩

/-- **The backward relation, from `Open2`, `SuccTyped` and `WitnessBnd`**, for a finite
`HostOk` host in a profile where growth may both succeed and fail. -/
theorem bwdRel_of_open2 (hf : HostFinite host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (hh : HostOk host) (O : Open2 hn P host)
    (ST : Multi.SuccTyped (BI P hn host) hn) (WB : WitnessBnd (BI P hn host) hn) :
    Multi.BwdRel (BI P hn host) hn P host :=
  bwdRel_of_partsOkS (partsOkS_of_open2 hf hPs hPf O) hh ST WB

/-! ## Runs -/

/-- **`MultiOk2` from the leaves still open after round 5, pass 2**, with
`B := Prims.builtins`. -/
theorem multiOk2_of_open2
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open2 hn (Profile.spec nd r) host) :
    MultiOk2 := fun H hn hinj host hfin hok nd r =>
  have O := h H hn hinj host hfin hok nd r
  ⟨_, fwdRel_of_open2 hfin hok O,
    bwdRel_of_open2 hfin (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r) hok O⟩

/-- **The run corollaries of the restated target, from `Open2`**, at one finite `HostOk` host
and `Profile.spec nd r`, with `B := Prims.builtins`. Start from a valid source whose runs stay
bounded and export-free. Every Core run is then matched by a SpecTec run from the source's
image, up to `ConfigEq`. Under `SuccTyped` and `WitnessBnd`, every SpecTec run from the image is
matched by a Core run. -/
theorem runs_of_open2 {nd : Bool} {r : RelaxedChoice} (hf : HostFinite host) (hh : HostOk host)
    (O : Open2 hn (Profile.spec nd r) host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      Multi.BoundedReachNE (Profile.spec nd r) host c₀ → Steps (Profile.spec nd r) host c₀ c →
      ∃ d, ConfigEq c d ∧
        SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) (configV hn d)) ∧
    (Multi.SuccTyped (BI (Profile.spec nd r) hn host) hn →
      WitnessBnd (BI (Profile.spec nd r) hn host) hn →
      ∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      Multi.BoundedReachNE (Profile.spec nd r) host c₀ →
      SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) w →
      ∃ c d, ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) := by
  have K := Pos.posTypingNE_of_simd O.simd hn
  have h₀ {c₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
      (hb : Multi.BoundedReachNE (Profile.spec nd r) host c₀) :
      SimRel (BI (Profile.spec nd r) hn host) hn c₀ c₀ :=
    ⟨Bwd.ConfigEq.refl c₀, Pos.typed_of_configOk_ne K hc (hb c₀ .refl)⟩
  refine ⟨fun c₀ c ts hc hb hs => ?_, fun ST WB c₀ ts w hc hb hs => ?_⟩
  · obtain ⟨d, hr, hss⟩ := Multi.steps_sim (fwdRel_of_open2 hf hh O) hh hc hb (h₀ hc hb) hs
    exact ⟨d, hr.1, hss⟩
  · have hB := bwdRel_of_open2 hf (BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) hh O ST WB
    obtain ⟨c, d, hr, hw, hss⟩ := Multi.ssteps_sim hB hh hc hb (h₀ hc hb) hs
    exact ⟨c, d, hr.1, hw, hss⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Int2
