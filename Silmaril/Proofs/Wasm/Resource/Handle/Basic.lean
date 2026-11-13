module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Wasm.Resource.Link.Defs
public import Silmaril.Proofs.Wasm.Resource.Link.Basic
public import Silmaril.Wasm.Spec.Basic.Defs

/-!
# Handle protocols: blame, neutrality and the provider link

* Blame: in the client orientation only `use`/`free` events can be rejected, in the provider
  orientation only `alloc` events (`handleStep_client_ne_none`, `handleStep_provider_ne_none`);
  environment events are never rejected, so the Wasm sentences read on moves are `OTotal`
  (`clientSpec_oTotal`, `providerSpec_oTotal`, `obSpec_oTotal`).
* `providerSpec_importNeutral`: import events do not move the provider protocol.
* `provider_models`: the provider verification condition gives the provider sentence over
  `wasmSem P`, every profile.
* `clientSpec_of_neverCall`: a program that never calls `use` and `free` is a safe client
  (whatever its allocations).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {Hd : Type} [DecidableEq Hd]

/-! ## Blame -/

theorem handleStep_client_alloc (q : Option (List Hd)) (h : Hd) :
    handleStep .client q (.alloc h) ≠ none := by
  rcases q with _ | L
  · simp [handleStep]
  · simp only [handleStep]; split <;> simp [fault]

theorem handleStep_skip (r : Role) (q : Option (List Hd)) : handleStep r q .skip = some q := by
  rcases q with _ | L <;> rfl

theorem handleStep_provider_use (q : Option (List Hd)) (h : Hd) :
    handleStep .provider q (.use h) ≠ none := by
  rcases q with _ | L
  · simp [handleStep]
  · simp only [handleStep]; split <;> simp [fault]

theorem handleStep_provider_free (q : Option (List Hd)) (h : Hd) :
    handleStep .provider q (.free h) ≠ none := by
  rcases q with _ | L
  · simp [handleStep]
  · simp only [handleStep]; split <;> simp [fault]

theorem allocOf_cases (b : Behaviour Val) : (∃ h, HEv.allocOf b = .alloc h) ∨ HEv.allocOf b = .skip := by
  unfold HEv.allocOf; split <;> simp

theorem useOf_cases (a : List Val) : (∃ h, HEv.useOf a = .use h) ∨ HEv.useOf a = .skip := by
  unfold HEv.useOf; split <;> simp

theorem freeOf_cases (a : List Val) : (∃ h, HEv.freeOf a = .free h) ∨ HEv.freeOf a = .skip := by
  unfold HEv.freeOf; split <;> simp

/-! ## Wasm sentences read on moves -/

section
variable {X : WIface}

/-- Environment moves never break the client sentence. -/
theorem clientSpec_oTotal (ia iu if_ : X.Imp) :
    OTotal ((clientSpec ia iu if_).comap
      (moveEvent : Move (ifaceSig X.imports) (ifaceSig X.exports) → WEvent X)) := by
  intro q o ho
  rcases o with (e | ⟨e, w⟩) | (f | ⟨f, w⟩)
  · exact ho.elim
  · show (handleStep .client q (clientEv ia iu if_ (.inl (evOf (.ans e w))))).isSome
    rw [Option.isSome_iff_ne_none]
    simp only [evOf, clientEv]
    split
    · rcases allocOf_cases (Answer.toBehaviour w) with ⟨h, hh⟩ | hh <;> rw [hh]
      · exact handleStep_client_alloc q h
      · rw [handleStep_skip]; simp
    · rw [handleStep_skip]; simp
  · show (handleStep .client q (clientEv ia iu if_ (.inr (evOf (.ask f))))).isSome
    simp only [clientEv, handleStep_skip, Option.isSome_some]
  · exact ho.elim

/-- Environment moves never break the provider sentence. -/
theorem providerSpec_oTotal (ja ju jf : X.Exp) :
    OTotal ((providerSpec ja ju jf).comap
      (moveEvent : Move (ifaceSig X.imports) (ifaceSig X.exports) → WEvent X)) := by
  intro q o ho
  rcases o with (e | ⟨e, w⟩) | (f | ⟨f, w⟩)
  · exact ho.elim
  · show (handleStep .provider q (providerEv ja ju jf (.inl (evOf (.ans e w))))).isSome
    simp only [providerEv, handleStep_skip, Option.isSome_some]
  · show (handleStep .provider q (providerEv ja ju jf (.inr (evOf (.ask f))))).isSome
    rw [Option.isSome_iff_ne_none]
    simp only [evOf, providerEv]
    split
    · rcases useOf_cases f.2.1 with ⟨h, hh⟩ | hh <;> rw [hh]
      · exact handleStep_provider_use q h
      · rw [handleStep_skip]; simp
    · split
      · rcases freeOf_cases f.2.1 with ⟨h, hh⟩ | hh <;> rw [hh]
        · exact handleStep_provider_free q h
        · rw [handleStep_skip]; simp
      · rw [handleStep_skip]; simp
  · exact ho.elim

/-- Import events do not move the provider sentence. -/
theorem providerSpec_importNeutral (ja ju jf : X.Exp) :
    ImportNeutral (I := (⟨X.imports, X.exports, [], {}⟩ : ScalarInstance))
      ((providerSpec ja ju jf).comap
        (moveEvent : Move (ifaceSig X.imports) (ifaceSig X.exports) → WEvent X)) :=
  ⟨fun q _ => handleStep_skip .provider q, fun q _ _ => handleStep_skip .provider q⟩

/-- **Provider soundness for the handle sentence** (every profile): the provider verification
condition with an invariant holding initially gives the provider sentence. -/
theorem provider_models {P : Profile} (p : WasmProg X) (ja ju jf : X.Exp)
    {Inv : Option (List Val) → Store Nat → Prop}
    (hm : ProvSat p.inst ((providerSpec ja ju jf).comap moveEvent) Inv P)
    (hs : Inv (some []) p.store) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P) p
      (providerSpec ja ju jf) :=
  models_of_plays p _ (provider_sound hm
    ⟨fun q _ => handleStep_skip .provider q, fun q _ _ => handleStep_skip .provider q⟩
    (providerSpec_oTotal ja ju jf) hs)

end

/-! ## Clients that never use or free -/

/-- The client protocol accepts every word without `use` and `free` events. -/
theorem handle_client_accepts (t : List (HEv Hd))
    (ht : ∀ e ∈ t, (∃ h, e = .alloc h) ∨ e = .skip) :
    ∀ q, (∃ q', (handleProto Hd .client).run q t = some q') := by
  induction t with
  | nil => exact fun q => ⟨q, rfl⟩
  | cons e t ih =>
    intro q
    have hrest := ih fun e' he' => ht e' (List.mem_cons_of_mem _ he')
    rcases ht e List.mem_cons_self with ⟨h, rfl⟩ | rfl
    · obtain ⟨q₁, hq₁⟩ := Option.ne_none_iff_exists'.1 (handleStep_client_alloc q h)
      obtain ⟨q₂, hq₂⟩ := hrest q₁
      exact ⟨q₂, by simp only [Protocol.run_cons, handleProto]; rw [hq₁]; exact hq₂⟩
    · obtain ⟨q₂, hq₂⟩ := hrest q
      exact ⟨q₂, by simp only [Protocol.run_cons, handleProto]; rw [handleStep_skip]; exact hq₂⟩

/-- **A program that never calls `use` or `free` is a safe client**, in any semantics. -/
theorem clientSpec_of_neverCall {Ty : Type} {Sem : Semantics Ty (List Val) (Behaviour Val)}
    {X : Iface Ty} (p : Sem.Prog X) (ia iu if_ : X.Imp)
    (hu : Models (neverCall Ty (List Val) (Behaviour Val)) Sem p iu)
    (hf : Models (neverCall Ty (List Val) (Behaviour Val)) Sem p if_) :
    Models (protoLogic Ty (List Val) (Behaviour Val) (Option (List Val))) Sem p
      (clientSpec ia iu if_) := by
  rw [models_iff] at hu hf
  rw [models_protoLogic_iff]
  intro t ht
  rw [clientSpec, Protocol.accepts_comap, Protocol.accepts_iff_exists]
  refine handle_client_accepts _ (fun e he => ?_) _
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  rcases x with (⟨i, a⟩ | ⟨i, b⟩) | (⟨j, a⟩ | ⟨j, b⟩)
  · have hiu : i ≠ iu := fun h => hu t ht a (h ▸ hx)
    have hif : i ≠ if_ := fun h => hf t ht a (h ▸ hx)
    simp [clientEv, hiu, hif]
  · simp only [clientEv]
    split
    · rcases allocOf_cases b with ⟨h, hh⟩ | hh <;> rw [hh]
      · exact .inl ⟨h, rfl⟩
      · exact .inr rfl
    · exact .inr rfl
  · exact .inr rfl
  · exact .inr rfl

end Silmaril.Wasm.Resource
