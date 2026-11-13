module

public import Silmaril.Wasm.Resource.CompTable.Defs
public import Silmaril.Wasm.Resource.Component.Thms
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# The component handle sentences on `refSem`: proofs

`refSem` (`Silmaril.Wasm.Spec.Component.Ref`) observes one export call on a fresh instance: its
traces are the prefixes of `[call j a, ret j b]`. On such traces the component handle
sentences hold for a trivial reason, whatever the component:

* `refTraces_compProvider`, `refSem_compProvider`: `compProviderSpec new drop` (a call is never
  an `alloc`, so after it the provider state is `some []` or the environment is blamed, and the
  return's `alloc` is fresh);
* `refTraces_nud`, `refSem_noUseAfterDrop`: `nudProto d` and `noUseAfterDrop d` (nothing was
  dropped before the only call).

These are **vacuity** results: they record that `refSem` cannot distinguish a component that
reuses a live representation, or a client that uses a dropped one, from a correct one.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

theorem compProviderEv_call_ne_alloc {X : CIface} (new drop : X.Exp) (j : X.Exp) (a : List RVal)
    (r : ℕ) : compProviderEv new drop (Event.call j a) ≠ .alloc r := by
  rcases a with _ | ⟨v, _ | ⟨w, a⟩⟩
  · simp [compProviderEv]
  · cases v <;> simp [compProviderEv]
    split <;> simp
  · simp [compProviderEv]

theorem handleStep_provider_nil {e : HEv ℕ} (he : ∀ r, e ≠ .alloc r) :
    handleStep .provider (some []) e = some none ∨ handleStep .provider (some []) e = some (some []) := by
  cases e with
  | alloc r => exact absurd rfl (he r)
  | use r => simp [handleStep, fault]
  | free r => simp [handleStep, fault]
  | skip => exact .inr rfl

theorem handleStep_provider_nil_isSome (e : HEv ℕ) : (handleStep .provider (some []) e).isSome := by
  cases e <;> simp [handleStep, fault]

theorem refTraces_compProvider (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ)
    {X : CIface} (p : RefProg E X) (new drop : X.Exp) {t : List (CEvent X)}
    (ht : t ∈ refTraces prof h σ0 p) : (compProviderSpec new drop).Accepts t := by
  have hcall : ∀ j a, (compProviderSpec new drop).step (some []) (Event.call j a) = some none ∨
      (compProviderSpec new drop).step (some []) (Event.call j a) = some (some []) :=
    fun j a => handleStep_provider_nil (compProviderEv_call_ne_alloc new drop j a)
  show ((compProviderSpec new drop).run (some []) t).isSome
  rcases ht with rfl | ⟨j, a, rfl⟩ | ⟨j, a, b, -, rfl⟩
  · rfl
  · rcases hcall j a with e | e <;> simp [e]
  · have h2 : ∀ q, (compProviderSpec new drop).step (some []) (Event.call j a) = some q →
        ((compProviderSpec new drop).step q (Event.ret j b)).isSome := by
      rintro q hq
      rcases hcall j a with e | e <;> rw [e] at hq <;> cases hq
      · rfl
      · exact handleStep_provider_nil_isSome _
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (by rcases hcall j a with e | e <;> simp [e] :
      ((compProviderSpec new drop).step (some []) (Event.call j a)).isSome)
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 (h2 q hq)
    simp [hq, hq']

theorem refTraces_nud (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ)
    {X : CIface} (p : RefProg E X) (d : X.Exp) {t : List (CEvent X)}
    (ht : t ∈ refTraces prof h σ0 p) : (nudProto d).Accepts t := by
  rcases ht with rfl | ⟨j, a, rfl⟩ | ⟨j, a, b, -, rfl⟩
  · rfl
  · simp [Protocol.Accepts, Protocol.run, nudProto, nudStep]
  · simp [Protocol.Accepts, Protocol.run, nudProto, nudStep]

/-- `compProviderSpec` holds of every reference component in `refSem`, vacuously. -/
theorem refSem_compProvider (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ)
    {X : CIface} (p : RefProg E X) (new drop : X.Exp) :
    Models (protoLogic CFn (List RVal) Component.Outcome (Option (List ℕ))) (refSem prof h σ0) p
      (compProviderSpec new drop) :=
  (models_protoLogic_iff _ _ _).2 fun _ ht => refTraces_compProvider prof h σ0 p new drop ht

/-- `noUseAfterDrop` holds of every reference component in `refSem`, vacuously. -/
theorem refSem_noUseAfterDrop (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ)
    (σ0 : σ) {X : CIface} (p : RefProg E X) (d : X.Exp) :
    Models noUseAfterDrop (refSem prof h σ0) p d :=
  (models_noUseAfterDrop_iff _ _ _).2 <|
    (models_protoLogic_iff _ _ _).2 fun _ ht => refTraces_nud prof h σ0 p d ht

end Silmaril.Wasm.Resource
