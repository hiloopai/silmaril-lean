module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi.Respect
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi.Eq
public import Silmaril.Wasm.SpecTec.Sim.Round4.Thms

/-!
# Round 5: the composable one-step simulations and runs

* `fwdRel_of_obl`, `fwdRel_of_open`: the forward relation `FwdRel` for the concrete `B`, from
  `fwdResp_of_step` (SpecTec respects `ConfigEq`) and Core's preservation: the Core successor
  of a valid source is valid, so it is typed (`typed_of_configOk_ne`) when bounded
  and export-free.
* `bwdRel_of_open`: the backward relation, under `SuccTyped`. `backward_R` applies
  at the witness `d` (its `ReadValidR` transfers along `ConfigEq`, `readValidR_of_configEq`),
  giving a Core step from `d`; Core's `Bwd.step_respects` moves it to `c`.
* `steps_sim`, `ssteps_sim`, `vals_iff`: round 4's run corollaries along the new relations
  (Core runs are SpecTec runs and conversely, and the observable values agree), for `HostOk`
  hosts and sources whose runs stay bounded and export-free (`BoundedReachNE`).
* `multiOk_of_open`: `MultiOk` from round 5's open leaves `Int.Open`; `runs_of_open`: the run
  corollaries themselves, at one host, from `Int.Open` (and `SuccTyped` for the backward one).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Multi

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel SSteps)
open Round4Int (BI)
open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd (ConfigEq)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## One step -/

/-- `Obl` from the open leaves (as in `Int.partsOkR_of_open`). -/
theorem obl_of_open (hf : HostFinite host) (O : Int.Open hn P host) :
    Fwd.Obl (BI P hn host) hn P host :=
  Fwd.obl_of (Int.typesB _) hf O.hostRespects (Fwd.rest_of O.refOk O.vector
    fun _ _ h hb => Fwd.fwd_aggregate5 (Fwd.aggTypesB_of (Int.typesB _)) O.newDataNum
      (Fwd.initDataZeroB_builtins hn host) h hb)

/-- **The forward relation, from `Obl`**, for a finite `HostOk` host respecting the encoding. -/
theorem fwdRel_of_obl (TB : Fwd.TypesB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : Prims.HostRespects hn host) (O : Fwd.Obl (BI P hn host) hn P host)
    (K : Pos.PosTypingNE (BI P hn host) hn) (hh : HostOk host) :
    FwdRel (BI P hn host) hn P host := by
  intro c d c' _ hc hb hd hb' hs
  have htc' := Pos.typed_of_configOk_ne K (Step.preservation hh hc hs).1 hb'
  obtain ⟨e, he, hte, hst⟩ := fwdResp_of_step TB hf hr O hs hb.1 d hd.1 hd.2 htc'
  exact ⟨e, ⟨he, hte⟩, hst⟩

/-- **The forward relation, from the open leaves.** -/
theorem fwdRel_of_open (hf : HostFinite host) (hh : HostOk host) (O : Int.Open hn P host) :
    FwdRel (BI P hn host) hn P host :=
  fwdRel_of_obl (Int.typesB _) hf O.hostRespects (obl_of_open hf O)
    (Pos.posTypingNE_of_simd O.simd hn) hh

/-- **The backward relation, from `PartsOkR` and `SuccTyped`**, for a `HostOk` host. -/
theorem bwdRel_of_partsOkR (Pa : Int.PartsOkR hn P host) (hh : HostOk host)
    (ST : SuccTyped (BI P hn host) hn) : BwdRel (BI P hn host) hn P host := by
  intro c d ts w hc hb hsucc hd hs
  have hv := readValidR_of_configEq hd.1 (Round5.Bwd.readValidR_of_bounded hc hb.1)
  obtain ⟨c₂, d₂, h₁, rfl, hst⟩ := Round5.Bwd.backward_R Pa.hostSteps Pa.rem d w hv hd.2 hs
  obtain ⟨c', hst', h₂⟩ := Bwd.step_respects hst c (Round4.configEq_symm hd.1)
  have he : ConfigEq c' d₂ := configEq_trans (Round4.configEq_symm h₂) h₁
  have htc' := Pos.typed_of_configOk_ne Pa.pos (Step.preservation hh hc hst').1 (hsucc c' hst')
  exact ⟨c', d₂, ⟨he, ST d d₂ c' hd.2 hs he htc'⟩, rfl, hst'⟩

/-- **The backward relation, from the open leaves and `SuccTyped`**, for a finite `HostOk` host
in a profile where growth may both succeed and fail. -/
theorem bwdRel_of_open (hf : HostFinite host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (hh : HostOk host) (O : Int.Open hn P host)
    (ST : SuccTyped (BI P hn host) hn) : BwdRel (BI P hn host) hn P host :=
  bwdRel_of_partsOkR (Int.partsOkR_of_open hf hPs hPf O) hh ST

/-! ## Runs -/

variable {B : Builtins}

/-- **Core runs are SpecTec runs, along `SimRel`.** -/
theorem steps_sim (h : FwdRel B hn P host) (hhost : HostOk host) {c₀ d₀ : Config H}
    {ts : List CValType} (hc : ConfigOk c₀ ts) (hb : BoundedReachNE P host c₀)
    (hd : SimRel B hn c₀ d₀) {c : Config H} (hs : Steps P host c₀ c) :
    ∃ d, SimRel B hn c d ∧ SSteps (simEnv B) (configV hn d₀) (configV hn d) := by
  induction hs with
  | refl => exact ⟨d₀, hd, .refl⟩
  | @tail c₁ c₂ h₁ h₂ ih =>
    obtain ⟨d₁, hr₁, hr⟩ := ih
    have hok := (Steps.safe hhost hc h₁).1
    obtain ⟨d₂, hr₂, hst⟩ := h c₁ d₁ c₂ ts hok (hb c₁ h₁) hr₁ (hb c₂ (h₁.tail h₂)) h₂
    exact ⟨d₂, hr₂, hr.tail hst⟩

/-- **SpecTec runs are Core runs, along `SimRel`.** -/
theorem ssteps_sim (h : BwdRel B hn P host) (hhost : HostOk host) {c₀ d₀ : Config H}
    {ts : List CValType} (hc : ConfigOk c₀ ts) (hb : BoundedReachNE P host c₀)
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

/-- **Observable values agree.** From a valid, typed source whose runs stay bounded and
export-free, Core reaches the values `vs` with a state whose image is that of `s; f` iff SpecTec
reaches the image of `s; f; vs`. -/
theorem vals_iff (hF : FwdRel B hn P host) (hB : BwdRel B hn P host) (hhost : HostOk host)
    {c₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts) (hb : BoundedReachNE P host c₀)
    (ht : Typed (simEnv B) hn c₀) (s : Store H) (f : Frame) (vs : List Val) :
    (∃ s' f', Steps P host c₀ ⟨s', f', vals vs⟩ ∧ stateV hn s' f' = stateV hn s f) ↔
      SSteps (simEnv B) (configV hn c₀) (configV hn ⟨s, f, vals vs⟩) := by
  have h₀ : SimRel B hn c₀ c₀ := ⟨Bwd.ConfigEq.refl c₀, ht⟩
  constructor
  · rintro ⟨s', f', hs, hst⟩
    obtain ⟨d, hr, hss⟩ := steps_sim hF hhost hc hb h₀ hs
    rw [Round4.simRel_deep (Bwd.codeDeep_vals vs) hr] at hss
    have e : configV hn ⟨s', f', vals vs⟩ = configV hn ⟨s, f, vals vs⟩ := by
      simp only [configV, hst]
    exact e ▸ hss
  · intro hs
    obtain ⟨c, d, hr, he, hss⟩ := ssteps_sim hB hhost hc hb h₀ hs
    obtain ⟨sd, fd, cd⟩ := d
    have he' : stateV hn s f = stateV hn sd fd ∧ adminsToV (vals vs) = adminsToV cd := by
      simpa [configV] using he
    obtain rfl := Round4.eq_vals_of_image B he'.2.symm
    obtain rfl := Bwd.cfgEq_deep (Bwd.codeDeep_vals vs) (Round4.configEq_symm hr.1)
    exact ⟨sd, fd, hss, he'.1.symm⟩

/-! ## Every host -/

/-- **`MultiOk` from the leaves still open after round 5, pass 1**, with `B := Prims.builtins`. -/
theorem multiOk_of_open
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Int.Open hn (Profile.spec nd r) host) :
    MultiOk := fun H hn hinj host hfin hok nd r =>
  have O := h H hn hinj host hfin hok nd r
  ⟨_, fwdRel_of_open hfin hok O,
    bwdRel_of_open hfin (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r) hok O⟩

/-- **The run corollaries of the restated target, from the open leaves**, at one finite `HostOk`
host and `Profile.spec nd r`, with `B := Prims.builtins`: from a valid source whose runs stay
bounded and export-free, every Core run is matched by a SpecTec run from the source's image up
to `ConfigEq`, and, under `SuccTyped`, every SpecTec run from the image is matched by a Core
run. -/
theorem runs_of_open {nd : Bool} {r : RelaxedChoice} (hf : HostFinite host) (hh : HostOk host)
    (O : Int.Open hn (Profile.spec nd r) host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachNE (Profile.spec nd r) host c₀ → Steps (Profile.spec nd r) host c₀ c →
      ∃ d, ConfigEq c d ∧
        SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) (configV hn d)) ∧
    (SuccTyped (BI (Profile.spec nd r) hn host) hn →
      ∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachNE (Profile.spec nd r) host c₀ →
      SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) w →
      ∃ c d, ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) := by
  have K := Pos.posTypingNE_of_simd O.simd hn
  have h₀ {c₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
      (hb : BoundedReachNE (Profile.spec nd r) host c₀) :
      SimRel (BI (Profile.spec nd r) hn host) hn c₀ c₀ :=
    ⟨Bwd.ConfigEq.refl c₀, Pos.typed_of_configOk_ne K hc (hb c₀ .refl)⟩
  refine ⟨fun c₀ c ts hc hb hs => ?_, fun ST c₀ ts w hc hb hs => ?_⟩
  · obtain ⟨d, hr, hss⟩ := steps_sim (fwdRel_of_open hf hh O) hh hc hb (h₀ hc hb) hs
    exact ⟨d, hr.1, hss⟩
  · have hB := bwdRel_of_open hf (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r)
      hh O ST
    obtain ⟨c, d, hr, hw, hss⟩ := ssteps_sim hB hh hc hb (h₀ hc hb) hs
    exact ⟨c, d, hr.1, hw, hss⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Multi
