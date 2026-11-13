module

public import Silmaril.Wasm.Unified.Component.Inst.Defs
public import Silmaril.Wasm.Unified.Component.Wrap.Thms

/-!
# The comorphism onto calls of the wrapping component

`Silmaril.Wasm.Unified.Component.toComp` sends a core sentence about a call `(c, p)` to the
sentence about export `0` of the one-export **core module** of `c`. With the converse of
`obs_core_subset_wrap` (`obs_wrap`, `Silmaril.Wasm.Unified.Component.Wrap`) the same works for the
**component** wrapping that module:

* `CProg.uses_wrap`: the trivial wrapper uses no adapters, so it is a program of every component
  signature (in particular of `coreOnly`);
* `coreCallW`, `coreSenW`: a core call as a call of export `0` of the wrapped one-export module,
  and core sentences as sentences about such calls; `coreSenW_sat` (from `obs_wrap_single`);
* `mapComp_wrap`: renaming opcodes commutes with wrapping, so `coreSenW_map`;
* **`toCompW : Inst.CoHom (inst Payload (Option Payload)) cinst`**: the comorphism with the same
  signature functor (`coreToCSig`) and model translation (the identity) as `toComp`, landing on
  calls of components.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm.Atlas
open Silmaril.Wasm.Component Silmaril.Wasm.Unified

variable {S S' : FSig}

/-- **The trivial wrapper uses no adapters.** -/
theorem CProg.uses_wrap (K : CMSig) (m : UMod S) :
    (CProg.comp (Silmaril.Wasm.Institution.Components.wrap m)).Uses K := by
  have h : ∀ im ∈ (CProg.comp (Silmaril.Wasm.Institution.Components.wrap m)).impls,
      im.chain = [] := by
    simp [CProg.impls, Silmaril.Wasm.Institution.Components.wrap, compImpls, nodesImpls, nodeImpls]
    rintro im (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩) <;> rfl
  intro im him a ha
  have ha' : a ∈ ([] : List Adapter) := h im him ▸ ha
  exact absurd ha' List.not_mem_nil

/-- Renaming opcodes commutes with wrapping. -/
theorem mapComp_wrap (σ : S ⟶ S') (m : UMod S) :
    mapComp σ (Silmaril.Wasm.Institution.Components.wrap m) =
      Silmaril.Wasm.Institution.Components.wrap (m.map σ) := by
  simp only [Silmaril.Wasm.Institution.Components.wrap, mapComp, mapNodes, mapNode]
  rfl

/-- A core call as a call of export `0` of the wrapped one-export module. -/
def coreCallW (x : Call Payload S) : CCall (coreToCSig.obj S) :=
  (⟨.comp (Silmaril.Wasm.Institution.Components.wrap (UMod.single x.1)), CProg.uses_wrap _ _⟩, 0,
    x.2)

/-- Core sentences as sentences about calls of wrapping components. -/
def coreSenW (φ : Sen Payload (Option Payload) S) : CSen (coreToCSig.obj S) :=
  .beh (φ.rename coreCallW)

theorem coreSenW_sat (M : PModel S) (φ : Sen Payload (Option Payload) S) :
    CSat (T := coreToCSig.obj S) M (coreSenW φ) ↔ Sat M φ :=
  (BSen.sat_rename _ _ φ).trans
    (BSen.sat_congr (obs := fun c => obs M ((coreCallW c).1.1, (coreCallW c).2))
      (obs' := M.obs) (fun x => obs_wrap_single M x.1 x.2) φ)

/-- The corridor of the comorphism at a signature. -/
def toCompWCorridor (S : FSig) :
    (institution Payload (Option Payload)).obj S ⟶ cinstitution.obj (coreToCSig.obj S) :=
  ⟨coreSenW, 𝟭 _, fun M φ => coreSenW_sat M φ⟩

theorem coreCallW_map (σ : S ⟶ S') (x : Call Payload S) :
    CCall.map (coreToCSig.map σ) (coreCallW x) = coreCallW (Call.map σ x) := by
  refine Prod.ext (Subtype.ext ?_) rfl
  show CProg.comp (mapComp σ (Silmaril.Wasm.Institution.Components.wrap (UMod.single x.1))) =
    CProg.comp (Silmaril.Wasm.Institution.Components.wrap (UMod.single (Call.map σ x).1))
  rw [mapComp_wrap]
  rfl

theorem coreSenW_map (σ : S ⟶ S') (φ : Sen Payload (Option Payload) S) :
    coreSenW (φ.map σ) = (coreSenW φ).map (coreToCSig.map σ) := by
  rw [coreSenW, coreSenW, CSen.map, Sen.map, BSen.rename_rename, BSen.rename_rename]
  exact congrArg (fun g => CSen.beh (BSen.rename g φ))
    (funext fun x => (coreCallW_map σ x).symm)

/-- **The comorphism onto calls of wrapping components.** -/
def toCompW : Inst.CoHom (inst Payload (Option Payload)) cinst where
  Φ := coreToCSig
  ρ :=
    { app := toCompWCorridor
      naturality := fun {_ _} σ => Room.hom_ext (funext fun φ => coreSenW_map σ φ)
        (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)) }

end Silmaril.Wasm.Unified.Component
