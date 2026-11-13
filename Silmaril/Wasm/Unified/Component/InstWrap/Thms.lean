module

public import Silmaril.Wasm.Unified.Component.InstWrap.Defs
public import Silmaril.Wasm.Unified.Component.Inst.Thms

/-!
# The comorphism onto calls of the wrapping component: borrowing

* `toCompW_modelExpansive`, **`toCompW_entails_iff`**: as for `toComp`, the model translation is
  the identity, so a core sentence follows from core hypotheses iff its translation about the
  wrapping components follows from theirs (`Inst.CoHom.entails_iff`).
* `coreSenW_iff_coreSen`: the two translations hold in the same models: a sentence about calls of
  the wrapping components holds iff the sentence about calls of the core modules does.
* `toCompW_obj`, `toCompW_mod`: `toCompW` and `toComp` have the same signature functor and the
  same model translation; they differ only in the sentences.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm.Unified
open Silmaril.Wasm.Component (Payload)

/-- The comorphism onto wrapping components is model-expansive. -/
theorem toCompW_modelExpansive : toCompW.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- **Borrowing along `toCompW`.** -/
theorem toCompW_entails_iff (S : FSig) (Γ : Set (Sen Payload (Option Payload) S))
    (φ : Sen Payload (Option Payload) S) :
    ((institution Payload (Option Payload)).obj S).Entails Γ φ ↔
      (cinstitution.obj (coreToCSig.obj S)).Entails (coreSenW '' Γ) (coreSenW φ) :=
  toCompW.entails_iff toCompW_modelExpansive S Γ φ

/-- **The two translations hold in the same models.** -/
theorem coreSenW_iff_coreSen {S : FSig} (M : PModel S) (φ : Sen Payload (Option Payload) S) :
    CSat (T := coreToCSig.obj S) M (coreSenW φ) ↔ CSat (T := coreToCSig.obj S) M (coreSen φ) :=
  (coreSenW_sat M φ).trans (coreSen_sat M φ).symm

/-- `toCompW` and `toComp` have the same signature functor. -/
theorem toCompW_obj (S : FSig) : toCompW.Φ.obj S = toComp.Φ.obj S := rfl

/-- `toCompW` and `toComp` have the same model translation (the identity). -/
theorem toCompW_mod (S : FSig) : (toCompW.ρ.app S).mod = (toComp.ρ.app S).mod := rfl

end Silmaril.Wasm.Unified.Component
