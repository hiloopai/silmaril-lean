module

public import Silmaril.Wasm.Game.Linking.Thms
import Silmaril.Proofs.Wasm.Game.Linking.StoreReverse

/-!
# Linked = shared at the level of stores

The play-level equation of step A (`Setup.linked_plays_eq_shared_of`) hides stores. These are
its store-level forms, for silmaril-lean's linker relation `StoreRelation.Related` between a
shared store (provider and consumer instantiated separately in one store) and a linked store,
at **every** profile:

* `Setup.sc_related_sl`: the initial shared and linked stores are related;
* `linker_invokeOk_reverse`: a typed invocation in the linked store is typed in a related
  shared store;
* `linker_steps_reflect`: a host-free Core run of an invocation in the linked store reaching a
  result is matched by a host-free run of the same invocation in a related, well-typed shared
  store, reaching the same result in a related store (from `reachReverse_all`);
* `linker_target_eq`: the linked store is determined by the related shared store and its
  function instances;
* `invoke_steps_storeOk`: host-free runs of a typed invocation keep the store typed.

Proofs: `Silmaril.Proofs.Wasm.Game.Linking.StoreReverse`. New theorems.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Linking

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC

/-- The initial shared and linked stores are related by the linker relation. -/
theorem Setup.sc_related_sl (S : Setup) : StoreRelation.Related S.sc S.sl :=
  S.related

/-- A typed invocation in the linked store is typed in a related shared store. -/
theorem linker_invokeOk_reverse {s s' : Store Nat} (hrel : StoreRelation.Related s s') {a : Nat}
    {vs : List Val} (hok : InvokeOk s' a vs) : InvokeOk s a vs :=
  Silmaril.Proofs.Wasm.Game.Linking.Store.invokeOk_reverse hrel hok

/-- Host-free runs of a typed invocation keep the store typed. -/
theorem invoke_steps_storeOk {P : Profile} {s : Store Nat} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hok : InvokeOk s a vs) {d : Config Nat}
    (h : Steps P (Det.noHost (H := Nat)) (invoke s a vs) d) : StoreOk d.store :=
  Silmaril.Proofs.Wasm.Game.Linking.Store.steps_storeOk hs hok h

/-- **Reverse simulation of finished invocations, store form, every profile.** -/
theorem linker_steps_reflect {P : Profile} {s s' : Store Nat} (hrel : StoreRelation.Related s s')
    (hs : StoreOk s) {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) {d' : Config Nat}
    {r : Result} (run : Steps P (Det.noHost (H := Nat)) (invoke s' a vs) d')
    (hd : d'.code = r.toAdmin) :
    ∃ d, Steps P (Det.noHost (H := Nat)) (invoke s a vs) d ∧ d.code = r.toAdmin ∧
      StoreRelation.Related d.store d'.store :=
  Silmaril.Proofs.Wasm.Game.Linking.Store.steps_reflect hrel hs hok run hd

/-- **The linked store is determined by the shared store and its function instances.** -/
theorem linker_target_eq {s₁ s₂ s₁' s₂' : Store Nat} (h₁ : StoreRelation.Related s₁ s₁')
    (h₂ : StoreRelation.Related s₂ s₂') (hs : s₁ = s₂) (hf : s₁'.funcs = s₂'.funcs) :
    s₁' = s₂' :=
  Silmaril.Proofs.Wasm.Game.Linking.Store.Related.target_eq h₁ h₂ hs hf

end Silmaril.Wasm.Game.Linking
