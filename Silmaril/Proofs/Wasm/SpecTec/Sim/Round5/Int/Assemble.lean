module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5Bwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms

/-!
# Round 5, pass-1 integration: the restated target from the tracks' pieces

* `typesB`: `Fwd.TypesB` holds in every `simEnv B`, from `tyT_tyV`.
* `oneStepOk_of_partsOkR`, `wholeStepValidOk_of_partsOkR`: `Round5.Task.wholeStepValidOk`
  from `PartsOkR` (track pos's assembly, with `backward_R` for the backward half).
* `partsOkR_of_partsOk`: `Pos.PartsOk` gives `PartsOkR`, so `PartsOkR` asks no more.
* `partsOkR_of_open`, `wholeStepValidOk_of_open`: `PartsOkR` from the open leaves `Open`, with
  every piece the four tracks proved (`posTypingNE_of_simd`, `forward_valid_final`,
  `hostStepsV_of_hostInv`, `remStep`, `remPure_of_open`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Int

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`TypesB` holds in every `simEnv B`**: the images of bounded types are typed
(`tyT_tyV`). -/
theorem typesB (B : Builtins) : Fwd.TypesB (simEnv B) where
  deftype d h := Pos.typedV_deftype d h
  comptype ct h := Pos.tyT_tyV ct h
  final b := Pos.typedV_finalV b
  typeuses us h := by
    obtain ⟨l, hl, hall⟩ := Pos.tyT_tyV (B := B) us h
    rw [hl]
    exact typedV_list_iff.2 fun u hu => (hall u hu).1
  valtypes ts h := typedV_list_iff.2 fun u hu =>
    (Pos.tyT_list_of ts (Pos.tyT_tyV (B := B) ts h) u hu).1
  storagetype zt h := Pos.tyT_tyV zt h

/-- **The restated one-step simulation, from `PartsOkR`**, for a `HostOk` host. -/
theorem oneStepOk_of_partsOkR (Pa : PartsOkR hn P host) (hh : HostOk host) :
    (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Pos.BoundedNE c →
      Pos.BoundedNE c' → Step P host c c' → ∃ d', Bwd.ConfigEq c' d' ∧
        SStep (simEnv (BI P hn host)) (configV hn c) (configV hn d')) ∧
    (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → Pos.BoundedNE c →
      SStep (simEnv (BI P hn host)) (configV hn c) w →
      ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c') :=
  ⟨fun c c' ts hc hb hb' hs =>
      Pa.fwd c c' ⟨⟨⟨ts, hc⟩, hb.1⟩, hb.2⟩ hb.1.store (Pos.typed_of_configOk_ne Pa.pos hc hb)
        (Pos.typed_of_configOk_ne Pa.pos (Step.preservation hh hc hs).1 hb') hs,
    fun c _ w hc hb hs =>
      Bwd.backward_R Pa.hostSteps Pa.rem c w (Bwd.readValidR_of_bounded hc hb.1)
        (Pos.typed_of_configOk_ne Pa.pos hc hb) hs⟩

/-- **`Round5.Task.wholeStepValidOk`, from `PartsOkR`** at every injective encoding, finite
`HostOk` host and `Profile.spec nd r`, with `B := Prims.builtins`. -/
theorem wholeStepValidOk_of_partsOkR
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), PartsOkR hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk := fun H hn hinj host hfin hok nd r =>
  ⟨_, oneStepOk_of_partsOkR (h H hn hinj host hfin hok nd r) hok⟩

/-- `Pos.PartsOk` gives `PartsOkR`: `PartsOkR` asks no more than track pos's reduction (which
is unsatisfiable through `RemainingV`, `Round5.Bwd.not_remainingV`). -/
theorem partsOkR_of_partsOk (Pa : Pos.PartsOk hn P host) : PartsOkR hn P host where
  pos := Pa.pos
  fwd := Pa.fwd
  hostSteps i hi c w hv hc hf := Pa.fam.step i (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide) c w hv hc hf
  rem := ⟨fun i h₀ h₁ h₂ s f is w hv hc hf => Pa.rem.pure i h₀ h₁ h₂ s f is w hv.read hc hf,
    fun i h₀ h₁ h₂ _ c w hv hc hf => Pa.rem.read i h₀ h₁ h₂ c w hv.read hc hf,
    fun i h6 h₀ h₁ c w hv hc hf => Pa.rem.step i h6 h₀ h₁ c w hv.read hc hf⟩

/-- **`PartsOkR` from the open leaves**, for a finite host, in a profile where growth may both
succeed and fail. -/
theorem partsOkR_of_open (hf : HostFinite host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (O : Open hn P host) : PartsOkR hn P host where
  pos := Pos.posTypingNE_of_simd O.simd hn
  fwd := R4Fwd.Forward.mono (fun _ h => h.1)
    (Fwd.forward_valid_final (typesB _) O.refOk hf O.hostRespects O.vector O.newDataNum)
  hostSteps := Bwd.hostStepsV_of_hostInv (Integrate.hostInv_concrete hf O.hostRespects)
  rem := ⟨fun i h₀ h₁ h₂ s f is w hv hc hf =>
      BwdStep.remPure_of_open O.vecAgree O.pureOpen i h₀ h₁ h₂ s f is w hv.read hc hf,
    O.read,
    fun i h6 h₀ h₁ c w hv hc hf => BwdStep.remStep hPs hPf i h6 h₀ h₁ c w hv.read hc hf⟩

/-- **`Round5.Task.wholeStepValidOk` from the leaves still open after pass 1**, at every
injective encoding, finite `HostOk` host and `Profile.spec nd r`. -/
theorem wholeStepValidOk_of_open
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk :=
  wholeStepValidOk_of_partsOkR fun H hn hinj host hfin hok nd r =>
    partsOkR_of_open hfin (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r)
      (h H hn hinj host hfin hok nd r)

end Silmaril.Wasm.SpecTec.Sim.Round5.Int
