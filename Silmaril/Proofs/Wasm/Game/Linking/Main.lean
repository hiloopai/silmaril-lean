module

public import Silmaril.Proofs.Wasm.Game.Linking.Shared
public import Silmaril.Proofs.Wasm.Game.Linking.Split.Init
public import Silmaril.Proofs.Wasm.Game.Linking.Reverse

/-!
# Static linking is composition: proofs

* (B) `shared_objPlays_eq_split`: the shared world decomposes into the
  provider object interacting with the consumer's plays, for every profile
  (`⊇`: `split_subset_shared`; `⊆`: the run of the shared world is followed by
  the joint machine, `Split.run_to_result`).
* `link_is_interact` = (A) + (B), the old statement (`link_is_composition` of
  the private development).
* `linked_eq_comp`: its categorical form, `σ_linked = σ_provider ≫ σ_consumer`
  in `Silmaril.Games`, through `mem_comp_noEv_iff` (composition with a component
  whose lower signature `ifaceSig []` has no events) and the fact that plays
  of closed instances are determined by their upper projections.
* Every profile: `comp_le_linked` (`σ_provider ≫ σ_consumer ≤ σ_linked`),
  and equality `linked_eq_comp_of` from the two reverse simulations
  `ReachReverse P` (linked to shared, `reachReverse_all`) and `SplitReflects P`
  (shared to split, `splitReflects`), both proved for every profile; hence
  `link_is_interact` and `linked_eq_comp` for every profile.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Linking.Setup

open Silmaril.Games Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable (S : Setup)

/-- **(B), `⊇`, every profile.** The provider object interacting with the consumer's plays
plays only plays of the shared world. -/
theorem split_subset_shared (hS : S.Scalar) (P : Profile) :
    interact (S.providerI.objPlays P S.sp) (S.consumerI.plays P S.scs) ⊆
      S.sharedI.objPlays P S.sc :=
  (Silmaril.Proofs.Wasm.Game.Linking.Split.static_nonempty S hS).elim fun St =>
    Silmaril.Proofs.Wasm.Game.Linking.Split.interact_subset St P

/-- The reverse inclusion of (B) under the profile `P`: every play of the shared world is
played by the consumer against the provider object (`splitReflects`, every profile). -/
def SplitReflects (P : Profile) : Prop :=
  S.sharedI.objPlays P S.sc ⊆ interact (S.providerI.objPlays P S.sp) (S.consumerI.plays P S.scs)

/-- **(B)** The shared world decomposes into the provider object and the consumer's plays,
for every profile. -/
theorem shared_objPlays_eq_split (hS : S.Scalar) (P : Profile) :
    S.sharedI.objPlays P S.sc =
      interact (S.providerI.objPlays P S.sp) (S.consumerI.plays P S.scs) :=
  (Silmaril.Proofs.Wasm.Game.Linking.Split.static_nonempty S hS).elim fun St =>
    Silmaril.Proofs.Wasm.Game.Linking.Split.shared_eq_interact St hS P

/-- `SplitReflects` holds in every profile. -/
theorem splitReflects (hS : S.Scalar) (P : Profile) : S.SplitReflects P :=
  (S.shared_objPlays_eq_split hS P).le

/-- `SplitReflects` in the deterministic profiles. -/
theorem splitReflects_profile (hS : S.Scalar) (o : GrowOracle) : S.SplitReflects (profile o) :=
  S.splitReflects hS (profile o)

/-- (A) + (B), `⊇`, every profile: the provider object interacting with the consumer's plays
plays only plays of the linked module. -/
theorem interact_subset_linked (hS : S.Scalar) (P : Profile) :
    interact (S.providerI.objPlays P S.sp) (S.consumerI.plays P S.scs) ⊆
      S.linkedI.objPlays P S.sl :=
  (S.split_subset_shared hS P).trans (S.shared_objPlays_subset_linked hS P)

/-- (A) + (B), every profile, given the two reverse simulations. -/
theorem link_is_interact_of (hS : S.Scalar) {P : Profile} (hrev : ReachReverse P)
    (hsplit : S.SplitReflects P) :
    S.linkedI.objPlays P S.sl =
      interact (S.providerI.objPlays P S.sp) (S.consumerI.plays P S.scs) :=
  (S.linked_objPlays_eq_shared_of hS hrev).trans
    ((S.split_subset_shared hS P).antisymm' hsplit)

/-- (A) + (B): the linked module, as an object over its exports, is the provider object
interacting with the consumer's plays, for every profile. -/
theorem link_is_interact (hS : S.Scalar) (P : Profile) :
    S.linkedI.objPlays P S.sl =
      interact (S.providerI.objPlays P S.sp) (S.consumerI.plays P S.scs) :=
  S.link_is_interact_of hS (reachReverse_all P) (S.splitReflects hS P)

theorem noEv_nil (a : Ev (ifaceSig [])) : False := by
  rcases a with e | ⟨e, -⟩ <;> exact Fin.elim0 e.1

/-- A play of the linked module (closed: no imports) is determined by its upper projection. -/
theorem mem_linked_iff (P : Profile) (p : List (Move S.linkedI.E S.linkedI.F)) :
    p ∈ S.linkedI.strategy P S.sl ↔ upper p ∈ S.linkedI.objPlays P S.sl := by
  rw [Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_strategy_iff,
    Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_plays_iff_objPlays (I := S.linkedI) rfl]

/-- A play of the composite of the provider's and the consumer's strategies is a play whose
upper projection is an interaction of the provider object with the consumer's plays. -/
theorem mem_comp_iff_interact (P : Profile)
    (p : List (Move S.linkedI.E S.linkedI.F)) :
    p ∈ (S.providerI.strategy P S.sp).comp (S.consumerI.strategy P S.scs) ↔
      upper p ∈ interact (S.providerI.objPlays P S.sp) (S.consumerI.plays P S.scs) := by
  refine (mem_comp_noEv_iff noEv_nil).trans ?_
  have hprov : ∀ t : List (Move S.providerI.F S.consumerI.F),
      (lower t).map .inr ∈ S.providerI.strategy P S.sp ↔ lower t ∈ S.providerI.objPlays P S.sp :=
    fun t => (Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_strategy_iff).trans
      ((Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_plays_iff_objPlays (I := S.providerI) rfl).trans
        (by rw [upper_map_inr]))
  constructor
  · rintro ⟨t, ht, hl, rfl⟩
    exact ⟨t, Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_strategy_iff.1 ht, (hprov t).1 hl,
      (upper_map_inr _).symm⟩
  · rintro ⟨t, ht, hl, hu⟩
    refine ⟨t, Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_strategy_iff.2 ht, (hprov t).2 hl, ?_⟩
    rw [Silmaril.Proofs.Wasm.Game.ScalarInstance.eq_map_upper (I := S.linkedI) rfl p, ← hu]
    rfl

/-- **M3, `≤`, every profile.** The composite of the provider's and the consumer's strategies
refines the strategy of the statically linked module: every play of the composite is a play
of the linked module. -/
theorem comp_le_linked (hS : S.Scalar) (P : Profile) :
    (S.providerI.strategy P S.sp).comp (S.consumerI.strategy P S.scs) ≤
      S.linkedI.strategy P S.sl := fun p hp =>
  (S.mem_linked_iff P p).2 (S.interact_subset_linked hS P ((S.mem_comp_iff_interact P p).1 hp))

/-- **M3, every profile, given the two reverse simulations.** -/
theorem linked_eq_comp_of (hS : S.Scalar) {P : Profile} (hrev : ReachReverse P)
    (hsplit : S.SplitReflects P) :
    S.linkedI.strategy P S.sl = (S.providerI.strategy P S.sp).comp (S.consumerI.strategy P S.scs) := by
  ext p
  refine (S.mem_linked_iff P p).trans (Iff.trans ?_ (S.mem_comp_iff_interact P p).symm)
  rw [S.link_is_interact_of hS hrev hsplit]
  exact Iff.rfl

/-- **M3, categorical form**, every profile. The strategy of the statically linked module is
the composition of the provider's and the consumer's strategies; the provider's store
persists across the consumer's calls. -/
theorem linked_eq_comp (hS : S.Scalar) (P : Profile) :
    S.linkedI.strategy P S.sl = (S.providerI.strategy P S.sp).comp (S.consumerI.strategy P S.scs) :=
  S.linked_eq_comp_of hS (reachReverse_all P) (S.splitReflects hS P)

end Silmaril.Wasm.Game.Linking.Setup
