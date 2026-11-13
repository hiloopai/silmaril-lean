module

public import Silmaril.Wasm.Unified.Versions.Defs
public import Silmaril.Wasm.Unified.Versions.FX.Thms
public import Silmaril.Wasm.Atlas.Wasmi.Thms

/-!
# The version embeddings as signature and model morphisms; the Atlas as a sub-diagram

**The embeddings.** Each embedding of `Silmaril.Wasm.Models` is a signature inclusion of the
unified institution together with a relation of models at corresponding points: the reduct of
the model at the image point is (or is refined by) the model at the point.

* `v10Emb_reduct`: `v10Emb` (1.0 → 2.0) over `n10 ⊆ n20`, an equation;
* `v20Emb_reduct`: `v20Emb` (2.0 → `core|v20`) over `n20 = n20`, an equation;
* `lime1Emb_reduct`: `lime1Emb` (Lime1 → `core|v30`) over `nLime1 ⊆ nsig v30`, an equation;
* `coreEmb_reduct`: `coreEmb` (`core|S` → `core|T`, `S ≤ T`), an equation;
* `fxEmb_refines`: `fxEmb` (`core|v30` → CoreFX) over `nsig v30 ⊆ sigFX`, a refinement
  (Core's observations are among the observations of the WasmFX reduct;
  `Versions.FX.core_refines_fx`).

With the satisfaction condition (`Silmaril.Wasm.Unified.sat_map_iff`) the equations transfer
**every sentence** (`v10_sat_iff`, `lime1_sat_iff`) and the refinement transfers universal
sentences (`fx_sat_univ`). At the code level the version embeddings are therefore equalities,
while at the call level, where the own semantics of 1.0, 2.0 and Lime1 is compared with Core,
they are inclusions (direction `sub`): the models here run every version's code with Core 3.0,
so the inclusions of the own semantics are not visible in them (see
`docs/projects/wasm-wasi.md`).

**The Atlas.** `Presents.comp`, `PresentsLE.comp`: presentations compose along composites of
transitions, so a path of presented transitions is presented by the composite inclusion
(`restrict_path_presents`); `Presents.sat_iff` and `PresentsLE.sat_univ` transfer sentences.
Presented transitions: `v10_presents`, `v20_presents`, `lime1_presents`, `restrict_presents`;
up to refinement: `fx_presentsLE`, `profile_presentsLE` (profiles), `loose_presentsLE`
(Core → loose).

**Open** (`Task.wasmi_refines_loose`): the code-level counterpart of
`Silmaril.Wasm.Atlas.Wasmi.toLooseUniv` (wasmi refines the loose model).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas Silmaril.Wasm.Models
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Presentations compose and transfer sentences -/

section Present

variable {A B C : Chart.{0, 0}} {PA : Presented A} {PB : Presented B} {PC : Presented C}

/-- **Presentations compose** along composites of transitions. -/
theorem Presents.comp {T : Transition A B} {U : Transition B C} {h₁ : FSig.Sub PA.K PB.K}
    {h₂ : FSig.Sub PB.K PC.K} (hT : Presents PA PB T h₁) (hU : Presents PB PC U h₂) :
    Presents PA PC (T.comp U) (h₁.trans h₂) := by
  intro p hp
  show (PC.model (U.pt (T.pt p))).reduct (FSig.incl (h₁.trans h₂)) = PA.model p
  rw [← FSig.incl_comp h₁ h₂, Model.reduct_comp, hU _ (T.dom_pt p hp), hT p hp]

/-- Presentations up to refinement compose. -/
theorem PresentsLE.comp {T : Transition A B} {U : Transition B C} {h₁ : FSig.Sub PA.K PB.K}
    {h₂ : FSig.Sub PB.K PC.K} (hT : PresentsLE PA PB T h₁) (hU : PresentsLE PB PC U h₂) :
    PresentsLE PA PC (T.comp U) (h₁.trans h₂) := by
  intro p hp
  have hU' := (hU _ (T.dom_pt p hp)).reduct (FSig.incl h₁)
  rw [← Model.reduct_comp, FSig.incl_comp] at hU'
  exact (hT p hp).trans hU'

/-- A presentation is a presentation up to refinement. -/
theorem Presents.toLE {T : Transition A B} {h : FSig.Sub PA.K PB.K} (hT : Presents PA PB T h) :
    PresentsLE PA PB T h := fun p hp => hT p hp ▸ Refines.refl _

/-- **Transfer along a presented transition**: the model of the image point satisfies the
translation of `φ` iff the model of the point satisfies `φ`. -/
theorem Presents.sat_iff {T : Transition A B} {h : FSig.Sub PA.K PB.K} (hT : Presents PA PB T h)
    {p : A.Pt} (hp : A.dom p) (φ : Sen UIn UObs PA.K) :
    Sat (PB.model (T.pt p)) (φ.map (FSig.incl h)) ↔ Sat (PA.model p) φ := by
  rw [sat_map_iff, hT p hp]

/-- Transfer of universal sentences along a transition presented up to refinement. -/
theorem PresentsLE.sat_univ {T : Transition A B} {h : FSig.Sub PA.K PB.K}
    (hT : PresentsLE PA PB T h) {p : A.Pt} (hp : A.dom p) {φ : Sen UIn UObs PA.K}
    (hu : φ.Universal) (hs : Sat (PB.model (T.pt p)) (φ.map (FSig.incl h))) :
    Sat (PA.model p) φ :=
  (hT p hp).sat_univ hu ((sat_map_iff _ _ _).mp hs)

end Present

/-! ## The embeddings -/

variable (f : Frame) (okc : List Instr → Prop)

/-- **`v10Emb` in the unified institution**: the inclusion `n10 ⊆ n20` and the reduct of the
2.0 model at the image point. -/
theorem v10Emb_reduct (p : V10.Pt H) :
    (v20At Profile.spec f okc ((V10.v10Emb H).pt p)).reduct (FSig.incl nsub_10_20) =
      v10At f okc p := rfl

/-- **`v20Emb` in the unified institution** (same signature). -/
theorem v20Emb_reduct (P : Profile) (p : V2Core.Pt H) :
    coreSAt v20 P f okc ((V2Core.v20Emb P H).pt p) = v20At P f okc p := rfl

/-- **`lime1Emb` in the unified institution**: the inclusion `nLime1 ⊆ nsig v30`. -/
theorem lime1Emb_reduct (p : Lime1Core.Pt H) :
    (coreSAt v30 Profile.spec f okc ((Lime1Core.lime1Emb H).pt p)).reduct
      (FSig.incl nsub_lime1_30) = lime1At f okc p := rfl

/-- **`coreEmb` in the unified institution**: the inclusion `nsig S ⊆ nsig T`. -/
theorem coreEmb_reduct (P : Profile) {S T : FeatureSet} (h : S ≤ T) (x : Core.Pt H) :
    (coreSAt T P f okc ((coreEmb P H h).pt x)).reduct (FSig.incl (nsig_sub h)) =
      coreSAt S P f okc x := rfl

/-- The inclusion of the 3.0 feature signature in WasmFX. -/
theorem nsub_30_FX : FSig.Sub (nsig v30) sigFX := (nsig_sub30 v30).trans sub30FX

/-- **`fxEmb` in the unified institution**: the inclusion `nsig v30 ⊆ sigFX`; Core 3.0 refines
the reduct of WasmFX at the image point (no FX functions), when FX validation accepts the
embedding of Core-valid code. -/
theorem fxEmb_refines (P : Profile) (okcFX : List FX.InstrFX → Prop)
    (hok : ∀ is, okc is → okcFX (is.map FX.InstrFX.core)) (x : Core.Pt H) :
    Refines (coreSAt v30 P f okc x)
      ((fxModelAt P f okcFX ((FX.fxEmb P H).pt x)).reduct (FSig.incl nsub_30_FX)) :=
  (core_refines_fx P x.2 x.1 f okc okcFX hok).reduct (FSig.incl (nsig_sub30 v30))

/-- Transfer along `v10Emb`: every sentence. -/
theorem v10_sat_iff (p : V10.Pt H) (φ : Sen UIn UObs n10) :
    Sat (v20At Profile.spec f okc ((V10.v10Emb H).pt p)) (φ.map (FSig.incl nsub_10_20)) ↔
      Sat (v10At f okc p) φ := by
  rw [sat_map_iff, v10Emb_reduct]

/-- Transfer along `lime1Emb`: every sentence. -/
theorem lime1_sat_iff (p : Lime1Core.Pt H) (φ : Sen UIn UObs nLime1) :
    Sat (coreSAt v30 Profile.spec f okc ((Lime1Core.lime1Emb H).pt p))
        (φ.map (FSig.incl nsub_lime1_30)) ↔ Sat (lime1At f okc p) φ := by
  rw [sat_map_iff, lime1Emb_reduct]

/-- Transfer along `fxEmb`: universal sentences of WasmFX hold in Core 3.0. -/
theorem fx_sat_univ (P : Profile) (okcFX : List FX.InstrFX → Prop)
    (hok : ∀ is, okc is → okcFX (is.map FX.InstrFX.core)) (x : Core.Pt H)
    {φ : Sen UIn UObs (nsig v30)} (hu : φ.Universal)
    (h : Sat (fxModelAt P f okcFX ((FX.fxEmb P H).pt x)) (φ.map (FSig.incl nsub_30_FX))) :
    Sat (coreSAt v30 P f okc x) φ :=
  (fxEmb_refines f okc P okcFX hok x).sat_univ hu ((sat_map_iff _ _ _).mp h)

/-! ## The Atlas transitions are presented -/

theorem v10_presents : Presents (pV10 (H := H) f okc) (pV20 f okc) (V10.v10Trans H) nsub_10_20 :=
  fun _ _ => rfl

theorem v20_presents (P : Profile) :
    Presents (pV20own (H := H) P f okc) (pCoreV v20 P f okc) (V2Core.v20Trans P H)
      (FSig.Sub.refl _) :=
  fun _ _ => rfl

theorem lime1_presents :
    Presents (pLime1 (H := H) f okc) (pCoreV v30 Profile.spec f okc) (Lime1Core.lime1Trans H)
      nsub_lime1_30 :=
  fun _ _ => rfl

theorem fx_presentsLE (P : Profile) (okcFX : List FX.InstrFX → Prop)
    (hok : ∀ is, okc is → okcFX (is.map FX.InstrFX.core)) :
    PresentsLE (pCoreM (H := H) v30 P f okc) (pFX P f okcFX) (FX.fxTrans P H) nsub_30_FX :=
  fun x _ => fxEmb_refines f okc P okcFX hok x

theorem restrict_presents (P : Profile) {S T : FeatureSet} (h : S ≤ T) :
    Presents (pCoreR (H := H) S P f okc) (pCoreR T P f okc) (restrict P H h) (nsig_sub h) :=
  fun _ _ => rfl

/-- A path of restrictions is presented by the composite inclusion. -/
theorem restrict_path_presents (P : Profile) {S T U : FeatureSet} (h : S ≤ T) (h' : T ≤ U) :
    Presents (pCoreR (H := H) S P f okc) (pCoreR U P f okc)
      ((restrict P H h).comp (restrict P H h')) ((nsig_sub h).trans (nsig_sub h')) :=
  (restrict_presents f okc P h).comp (restrict_presents f okc P h')

theorem profile_presentsLE {P' P : Profile} (h : Core.StepLE P' P H) :
    PresentsLE (pCore P' f okc) (pCore P f okc) (Core.profileUniv h) (FSig.Sub.refl _) :=
  fun x _ => core_refines_profile h x.2 x.1 f okc

theorem loose_presentsLE (P : Profile) :
    PresentsLE (pCore (H := H) P f okc) (pLoose P f okc) (Wasmi.coreToLooseUniv P H)
      (FSig.Sub.refl _) :=
  fun x _ => core_refines_loose P x.2 x.1 f okc

/-! ## Open -/

/-- **Open target**: wasmi refines the loose model at the code level on the wasmi signature, for
hosts parametric in function code (the code-level counterpart of
`Silmaril.Wasm.Atlas.Wasmi.toLooseUniv`). -/
def Task.wasmi_refines_loose : Prop :=
  ∀ (H : Type) (P : Profile) (f : Frame) (okc : List Instr → Prop) (x : Core.Pt H),
    Silmaril.Wasm.Execution.Core.Sim.HostParametric x.2 →
    Refines (wasmiModelAt P f okc x)
      ((looseModelAt P f okc x).reduct (FSig.incl (nsig_sub30 wasmi200)))

end Silmaril.Wasm.Unified.Versions
