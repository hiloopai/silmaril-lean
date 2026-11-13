module

public import Silmaril.Proofs.Wasm.Game.Linking.Shared
public import Silmaril.Proofs.Wasm.Game.Linking.Reverse

/-!
# Linked = shared at the level of stores (M3 step A, store form)

The play-level statement `Setup.linked_plays_eq_shared_of` hides stores. For determinism of the
linked store (`Silmaril.Wasm.Det.Link`) the store relation itself is needed:

* `invokeOk_reverse`: a typed invocation in the linked store is typed in a related shared
  store (`StoreRelation.Related.valOk_iff`);
* `steps_reflect`: a host-free Core run of an invocation in the linked store reaching a result
  is matched by a host-free run of the same invocation in a related, well-typed shared store,
  reaching the same result in a related store (`reachReverse_all`, every profile);
* `Related.target_eq`: the linked store is determined by the shared store and its function
  instances (`StoreRelation.Related` equates every other field);
* `steps_storeOk`, `steps_funcs`: host-free runs from a typed configuration keep the store
  typed and the function instances.

New (no source file).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Linking.Store

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Link.GC

/-- A typed invocation in the target of the linker relation is typed in the source. -/
theorem invokeOk_reverse {s s' : Store Nat} (hrel : StoreRelation.Related s s') {a : Nat}
    {vs : List Val} (hok : InvokeOk s' a vs) : InvokeOk s a vs := by
  obtain ⟨fi', ps, rs, hfi', hexp, hvs⟩ := hok
  obtain ⟨fi, hfi, hrf⟩ := hrel.function_lookup_reverse hfi'
  refine ⟨fi, ps, rs, hfi, ?_, hvs.imp fun v t hv => (hrel.valOk_iff v t).mpr hv⟩
  rw [hrf.type_eq]
  exact hexp

/-- Host-free runs from a typed configuration keep it typed. -/
theorem steps_configOk {P : Profile} {c d : Config Nat} {ts : List CValType} (hc : ConfigOk c ts)
    (h : Steps P (Det.noHost (H := Nat)) c d) : ConfigOk d ts := by
  induction h with
  | refl => exact hc
  | tail _ hst ih => exact (Step.preservation divHost_ok ih (Step.of_noHost SingleThreaded.divHost hst)).1

/-- Host-free runs of a typed invocation keep the store typed. -/
theorem steps_storeOk {P : Profile} {s : Store Nat} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) {d : Config Nat} (h : Steps P (Det.noHost (H := Nat)) (invoke s a vs) d) :
    StoreOk d.store := by
  obtain ⟨-, -, rs, -, -, hc⟩ := invoke_ok hs hok
  exact ConfigOk.storeOk (steps_configOk hc h)

/-- **Reverse simulation of finished invocations, store form (every profile).** A host-free run
of an invocation in the linked store `s'` reaching the result `r` is matched by a host-free run
of the same invocation in a related typed shared store `s`, reaching `r` in a related store. -/
theorem steps_reflect {P : Profile} {s s' : Store Nat} (hrel : StoreRelation.Related s s')
    (hs : StoreOk s) {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) {d' : Config Nat}
    {r : Result} (run : Steps P (Det.noHost (H := Nat)) (invoke s' a vs) d')
    (hd : d'.code = r.toAdmin) :
    ∃ d, Steps P (Det.noHost (H := Nat)) (invoke s a vs) d ∧ d.code = r.toAdmin ∧
      StoreRelation.Related d.store d'.store := by
  obtain ⟨fi, ps, rs, hfi, -, typed⟩ := invoke_ok hs hok
  have matching : Simulation.Matching .same ((Thread.pending a vs).config s)
      ((Thread.pending a vs).config s') := Simulation.Matching.invoke hrel hfi vs
  obtain ⟨s₁', t₁', run', rfl⟩ := reach_of_steps (s := s') (t := .pending a vs) run
  obtain ⟨⟨s₁, t₁⟩, run₁, final, hm⟩ :=
    reachReverse_all P (x := (s, .pending a vs)) (x' := (s', .pending a vs)) (ts := rs.toList)
      typed matching run' hd
  refine ⟨t₁.config s₁, Reach.steps run₁, final, ?_⟩
  have hst := hm.stores
  rw [Thread.config_store, Thread.config_store] at hst
  rw [Thread.config_store, Thread.config_store]
  exact hst

/-- **The linked store is determined by the shared store and its functions.** -/
theorem Related.target_eq {s₁ s₂ s₁' s₂' : Store Nat} (h₁ : StoreRelation.Related s₁ s₁')
    (h₂ : StoreRelation.Related s₂ s₂') (hs : s₁ = s₂) (hf : s₁'.funcs = s₂'.funcs) :
    s₁' = s₂' := by
  subst hs
  obtain ⟨⟨t₁, g₁, m₁, tb₁, d₁, e₁, st₁, ar₁, ex₁⟩, -⟩ := h₁
  obtain ⟨⟨t₂, g₂, m₂, tb₂, d₂, e₂, st₂, ar₂, ex₂⟩, -⟩ := h₂
  cases s₁'
  cases s₂'
  simp_all

end Silmaril.Proofs.Wasm.Game.Linking.Store
