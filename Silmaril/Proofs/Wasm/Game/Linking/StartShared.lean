module

public import Silmaril.Proofs.Wasm.Game.Linking.Main
public import Silmaril.Proofs.Wasm.Game.Linking.Split.Start

/-!
# Static linking at reached stores, and start invocations

The equations of M3 (`Silmaril.Proofs.Wasm.Game.Linking.Main`) are stated at the stores produced
by instantiation. Their proofs only use the invariants `Persistent` (linked and shared stores)
and `Split.IdleT` (shared, provider and consumer stores), which also hold after the start
functions have run. This module restates them at any stores satisfying the invariants, for
every profile:

* `linked_plays_at`: linked = shared at persistent stores (step A);
* `shared_objPlays_at`: shared = provider object interacting with the consumer, at idle
  related stores (step B);
* `linked_objPlays_at`: their combination;
* `start_transfer`, `start_reflect`: a start invocation (`$invoke(a, [])`) runs alike in the
  shared and the linked world, to the same result, keeping `Persistent`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Linking.Setup

open Silmaril.Games Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.Linking
  Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC

variable (S : Setup)

/-- Host-free runs keep the functions of the store. -/
theorem reach_funcs {P : Profile} {x y : Store Nat × Thread} (h : Reach P x y) :
    y.1.funcs = x.1.funcs := by
  induction h with
  | refl => rfl
  | @tail b c _ hst ih =>
    obtain ⟨s₁, t₁⟩ := b
    obtain ⟨s₂, t₂⟩ := c
    exact (InternalP.funcs_prefix hst).trans ih

/-- Start types depend on the functions only. -/
theorem startTyped_of_funcs {s s' : Store Nat} {a : Nat} (h : StartTyped s a)
    (hf : s'.funcs = s.funcs) : StartTyped s' a := by
  obtain ⟨fi, hfi, hty⟩ := h
  exact ⟨fi, hf ▸ hfi, hty⟩

/-- The shared store after a host-free run of a typed start invocation is well formed. -/
theorem wellFormed_after_start {P : Profile} {s s₁ : Store Nat} {a : Nat} {t₁ : Thread}
    (hw : S.sharedI.WellFormed s) (ha : StartTyped s a)
    (run : Reach P (s, .pending a []) (s₁, t₁)) : S.sharedI.WellFormed s₁ := by
  have typed : ThreadOk s (.pending a []) (Split.resC startType) := Split.start_typed hw ha
  have hok : StoreOk s₁ := (reachableP_typed run hw.storeOk typed).1
  exact hw.of_funcs hok (reach_funcs run)

/-- **Start invocations transfer** from the shared to the linked world (every profile). -/
theorem start_transfer {P : Profile} {s s' : Store Nat} (hs : S.Persistent s s') {a : Nat}
    (ha : StartTyped s a) {s₁ : Store Nat} {t₁ : Thread} {r : Result}
    (run : Reach P (s, .pending a []) (s₁, t₁)) (final : ResultAt s₁ t₁ r) :
    ∃ s₁' t₁', Reach P (s', .pending a []) (s₁', t₁') ∧ ResultAt s₁' t₁' r ∧
      S.Persistent s₁ s₁' := by
  have typed : ThreadOk s (.pending a []) (Split.resC startType) := Split.start_typed hs.2 ha
  obtain ⟨fi, hfi, -⟩ := id ha
  have matching : Simulation.Matching .same ((Thread.pending a []).config s)
      ((Thread.pending a []).config s') := Simulation.Matching.invoke hs.1 hfi []
  obtain ⟨⟨s₁', t₁'⟩, run', hm⟩ :=
    reach_simulation (x' := (s', .pending a [])) (ts := Split.resC startType) run typed matching
  have hst : StoreRelation.Related s₁ s₁' := by
    have h := hm.stores
    rwa [Thread.config_store, Thread.config_store] at h
  exact ⟨s₁', t₁', run', resultAt_matching final hm, hst, S.wellFormed_after_start hs.2 ha run⟩

/-- **Start invocations reflect** from the linked to the shared world (every profile). -/
theorem start_reflect {P : Profile} {s s' : Store Nat} (hs : S.Persistent s s') {a : Nat}
    (ha : StartTyped s a) {s₁' : Store Nat} {t₁' : Thread} {r : Result}
    (run' : Reach P (s', .pending a []) (s₁', t₁')) (final' : ResultAt s₁' t₁' r) :
    ∃ s₁ t₁, Reach P (s, .pending a []) (s₁, t₁) ∧ ResultAt s₁ t₁ r ∧
      S.Persistent s₁ s₁' := by
  have typed : ThreadOk s (.pending a []) (Split.resC startType) := Split.start_typed hs.2 ha
  obtain ⟨fi, hfi, -⟩ := id ha
  have matching : Simulation.Matching .same ((Thread.pending a []).config s)
      ((Thread.pending a []).config s') := Simulation.Matching.invoke hs.1 hfi []
  obtain ⟨⟨s₁, t₁⟩, run, final, hm⟩ :=
    reachReverse_all P (x := (s, .pending a [])) (x' := (s', .pending a []))
      (ts := Split.resC startType) typed matching run' final'
  have hst : StoreRelation.Related s₁ s₁' := by
    have h := hm.stores
    rwa [Thread.config_store, Thread.config_store] at h
  exact ⟨s₁, t₁, run, final, hst, S.wellFormed_after_start hs.2 ha run⟩

/-- **(A) at persistent stores**, every profile. -/
theorem linked_plays_at {P : Profile} {σ l : Store Nat} (hp : S.Persistent σ l) :
    S.linkedI.plays P l = S.sharedI.plays P σ :=
  Set.ext fun p => ⟨S.plays_reflect (reachReverse_all P) p hp, S.plays_transfer p hp⟩

/-- **(B) at idle related stores**, every profile. -/
theorem shared_objPlays_at (hS : S.Scalar) (St : Split.Static S) {P : Profile}
    {σ π κ : Store Nat} (hI : Split.IdleT St σ π κ) :
    S.sharedI.objPlays P σ =
      interact (S.providerI.objPlays P π) (S.consumerI.plays P κ) := by
  apply Set.Subset.antisymm
  · rintro t ⟨ps, ⟨qs, hps⟩, rfl⟩
    obtain ⟨pc, pp, qc', qp', hpc, hpp, hproj, hpf⟩ :=
      Split.sub_core St hS P hps (Split.GInvT.idle hI)
    exact ⟨pc, ⟨qc', hpc⟩, ⟨pp, ⟨qp', hpp⟩, hproj.symm⟩, hpf⟩
  · rintro t ⟨pc, ⟨qc, hc⟩, ⟨pp, ⟨qp, hp⟩, hpp⟩, rfl⟩
    obtain ⟨ps, qs, hps, hpf⟩ := Split.sup_core St P hc hp hpp.symm (Split.GInv.idle hI.1)
    exact ⟨ps, ⟨qs, hps⟩, hpf⟩

/-- **(A) + (B) at reached stores**, every profile: the linked module at `l` is the provider
object at `π` interacting with the consumer at `κ`, whenever the shared store `σ` is persistent
with `l` and idle related to `π` and `κ`. -/
theorem linked_objPlays_at (hS : S.Scalar) (St : Split.Static S) {P : Profile}
    {σ π κ l : Store Nat} (hI : Split.IdleT St σ π κ) (hp : S.Persistent σ l) :
    S.linkedI.objPlays P l =
      interact (S.providerI.objPlays P π) (S.consumerI.plays P κ) := by
  rw [← S.shared_objPlays_at hS St hI]
  unfold ScalarInstance.objPlays
  rw [S.linked_plays_at hp]
  rfl

/-- **(A) + (B), `⊇`, at reached stores**, every profile: only `Idle` is needed. -/
theorem interact_subset_linked_at (St : Split.Static S) {P : Profile} {σ π κ l : Store Nat}
    (hI : Split.Idle St σ π κ) (hp : S.Persistent σ l) :
    interact (S.providerI.objPlays P π) (S.consumerI.plays P κ) ⊆ S.linkedI.objPlays P l := by
  rintro t ⟨pc, ⟨qc, hc⟩, ⟨pp, ⟨qp, hpp'⟩, hpp⟩, rfl⟩
  obtain ⟨ps, qs, hps, hpf⟩ := Split.sup_core St P hc hpp' hpp.symm (Split.GInv.idle hI)
  exact ⟨ps, S.plays_transfer ps hp ⟨qs, hps⟩, hpf⟩

/-- The consumer's frame is the same in the stub and the shared world. -/
theorem fcs_eq_fc : S.fcs = S.fc := by
  have h' : instantiateOnce? (withFuncs (stubOut S.base.funcs.length S.stubs S.sp).funcs S.sp)
      S.consumer (Preparation.imports
        (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat))) =
        some (S.scs, S.fcs, none) := S.stubInst
  exact (Silmaril.Proofs.Wasm.Game.Linking.instantiateOnce?_withFuncs _ (by simp [stubOut])
    S.assembly.consumerProfile S.sharedInst h').1

end Silmaril.Wasm.Game.Linking.Setup
