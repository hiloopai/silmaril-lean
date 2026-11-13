module

public import Silmaril.Wasm.Unified.Component.Inst.Defs
public import Silmaril.Logic.Institution.Borrowing

/-!
# The unified component institution: borrowing from the core

* `toComp_modelExpansive`: the model translation of `toComp` is the identity, so the comorphism
  is model-expansive.
* `toComp_entails_iff`: **borrowing**: a core sentence follows from core hypotheses iff its
  component translation follows from theirs in the component institution
  (`Inst.CoHom.entails_iff`).
* `sat_feat_iff`: including CM features (`(𝟙 S, K ≤ K')`) does not change satisfaction.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm.Unified
open Silmaril.Wasm.Component (Payload)

/-- The comorphism from the core is model-expansive. -/
theorem toComp_modelExpansive : toComp.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- **Borrowing along `toComp`.** -/
theorem toComp_entails_iff (S : FSig) (Γ : Set (Sen Payload (Option Payload) S))
    (φ : Sen Payload (Option Payload) S) :
    ((institution Payload (Option Payload)).obj S).Entails Γ φ ↔
      (cinstitution.obj (coreToCSig.obj S)).Entails (coreSen '' Γ) (coreSen φ) :=
  toComp.entails_iff toComp_modelExpansive S Γ φ

/-- Including CM features keeps satisfaction. -/
theorem sat_feat_iff {S : FSig} {K K' : CMSig} (h : K ≤ K') (M : PModel S)
    (φ : CSen (S, K)) : CSat (T := (S, K')) M (φ.map ((𝟙 S, homOfLE h) : (S, K) ⟶ (S, K'))) ↔
      CSat (T := (S, K)) M φ :=
  (sat_map_iff ((𝟙 S, homOfLE h) : (S, K) ⟶ (S, K')) M φ).trans (by rw [Model.reduct_id])

end Silmaril.Wasm.Unified.Component
