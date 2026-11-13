module

public import Silmaril.Wasm.Unified.Versions.Run.Defs
public import Silmaril.Wasm.Atlas.Variant.Thms
public import Silmaril.Wasm.Atlas.Core.Thms

/-!
# Step-relation variants: refinement

* `model30_eq`: the core's Core 3.0 model is `modelR (Step P host)`;
* `Refines`: a preorder (`refl`, `trans`), stable under reducts (`Refines.reduct`), reflecting
  universal sentences (`Refines.sat_univ`) and preserving existential ones
  (`Refines.sat_exist`);
* `modelR_mono`: more steps, more observations. Instances: **Core 3.0 refines the loose
  model** (`core_refines_loose`), **profile refinement** (`core_refines_profile`, from
  `Silmaril.Wasm.Atlas.Core.StepLE`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The core's Core 3.0 model is the model of `Step P host`. -/
theorem model30_eq (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : model30 P host s f okc = modelR (Step P host) s f okc := rfl

/-! ## Refinement -/

section Refines

variable {In B : Type} {K K' : FSig}

theorem Refines.refl (M : Model In B K) : Refines M M := fun _ => subset_rfl

theorem Refines.trans {M N O : Model In B K} (h₁ : Refines M N) (h₂ : Refines N O) :
    Refines M O := fun x => (h₁ x).trans (h₂ x)

/-- Refinement is stable under reducts. -/
theorem Refines.reduct {M N : Model In B K'} (σ : K ⟶ K') (h : Refines M N) :
    Refines (M.reduct σ) (N.reduct σ) := by
  rintro ⟨c, i⟩
  rw [Model.obs_reduct, Model.obs_reduct]
  exact h _

/-- **Refinement reflects universal sentences.** -/
theorem Refines.sat_univ {M N : Model In B K} (h : Refines M N) {φ : Sen In B K}
    (hu : φ.Universal) (hN : Sat N φ) : Sat M φ :=
  BSen.sat_of_subset_univ h hu hN

/-- **Refinement preserves existential sentences.** -/
theorem Refines.sat_exist {M N : Model In B K} (h : Refines M N) {φ : Sen In B K}
    (he : φ.Existential) (hM : Sat M φ) : Sat N φ :=
  BSen.sat_of_subset_exist h he hM

end Refines

/-- **More steps, more observations.** -/
theorem modelR_mono {R R' : Config H → Config H → Prop} (h : ∀ c c', R c c' → R' c c')
    (s : Store H) (f : Frame) (okc : List Instr → Prop) :
    Refines (modelR R s f okc) (modelR R' s f okc) := by
  rintro ⟨c, vs⟩ b ⟨hok, is, hD, hc, hb⟩
  exact ⟨hok, is, hD, hc, Variant.behavioursR_mono h _ hb⟩

/-- **Core 3.0 refines the loose model.** -/
theorem core_refines_loose (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : Refines (model30 P host s f okc) (looseR P host s f okc) :=
  modelR_mono (fun _ _ hs => Variant.base_le hs) s f okc

/-- **Profile refinement** of Core 3.0. -/
theorem core_refines_profile {P' P : Profile} (h : Core.StepLE P' P H) (host : HostSemantics H)
    (s : Store H) (f : Frame) (okc : List Instr → Prop) :
    Refines (model30 P' host s f okc) (model30 P host s f okc) :=
  modelR_mono (h host) s f okc

end Silmaril.Wasm.Unified.Versions
