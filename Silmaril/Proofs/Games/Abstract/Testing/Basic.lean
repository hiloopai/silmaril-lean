module

public import Silmaril.Games.Abstract.Testing.Defs
public import Silmaril.Games.Abstract.Game.Thms

/-!
# Contexts and tests: proofs

Soundness of trace inclusion for may-testing, full abstraction under
definability, the single-play tests are complete, and testing through a game
morphism compares pulled-back models.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.Testing

open Silmaril.Games.Abstract

universe u v w

variable {G : Game.{u}}

theorem le_of_le (X : Tests.{u, v} G) {T U : TraceModel G} (h : T ≤ U) : X.Le T U :=
  fun _ ⟨s, hs, hT⟩ => ⟨s, hs, h hT⟩

theorem le_iff_of_complete {X : Tests.{u, v} G} (hX : X.Complete) {T U : TraceModel G} :
    X.Le T U ↔ T ≤ U := by
  refine ⟨fun h s hs => ?_, le_of_le X⟩
  obtain ⟨c, hc⟩ := hX s (T.closed.legal hs)
  exact (hc U).1 (h c ((hc T).2 hs))

theorem equiv_iff_of_complete {X : Tests.{u, v} G} (hX : X.Complete) {T U : TraceModel G} :
    X.Equiv T U ↔ T = U := by
  rw [Tests.Equiv, le_iff_of_complete hX, le_iff_of_complete hX]
  exact ⟨fun ⟨h₁, h₂⟩ => le_antisymm h₁ h₂, fun h => ⟨h.le, h.ge⟩⟩

theorem single_complete : (Tests.single G).Complete := fun s hs =>
  ⟨⟨s, hs⟩, fun _ => ⟨fun ⟨_, ht, hT⟩ => by rw [Set.mem_singleton_iff.1 ht] at hT; exact hT,
    fun hT => ⟨s, rfl, hT⟩⟩⟩

variable {H : Game.{w}}

theorem passes_through_iff {X : Tests.{u, v} G} (f : G.Hom H) (c : X.Ctx) (T : TraceModel H) :
    (X.through f).Passes c T ↔ X.Passes c (TraceModel.comap f T) := by
  constructor
  · rintro ⟨_, ⟨s, hs, hl, rfl⟩, hT⟩
    exact ⟨s, hs, hl, hT⟩
  · rintro ⟨s, hs, hl, hT⟩
    exact ⟨_, ⟨s, hs, hl, rfl⟩, hT⟩

theorem equiv_through_iff {X : Tests.{u, v} G} (hX : X.Complete) (f : G.Hom H)
    {T U : TraceModel H} :
    (X.through f).Equiv T U ↔ TraceModel.comap f T = TraceModel.comap f U := by
  have : ∀ T U : TraceModel H,
      (X.through f).Le T U ↔ X.Le (TraceModel.comap f T) (TraceModel.comap f U) :=
    fun T U => forall_congr' fun (c : X.Ctx) => by
      rw [passes_through_iff f c T, passes_through_iff f c U]
  rw [Tests.Equiv, this, this, ← Tests.Equiv, equiv_iff_of_complete hX]

end Silmaril.Proofs.Games.Abstract.Testing
