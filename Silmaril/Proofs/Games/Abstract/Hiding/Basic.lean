module

public import Silmaril.Games.Abstract.Hiding.Defs
public import Silmaril.Games.Abstract.Game.Thms

/-!
# Partial game morphisms: proofs

Hiding is left adjoint to pulling back, and pulling back along a total
morphism is `comap`.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.Hiding

open Silmaril.Games.Abstract Silmaril.Games.Abstract.TraceModel

universe u v

variable {G : Game.{u}} {H : Game.{v}}

theorem gc_hide_pull (f : G.PHom H) : GaloisConnection (hide f) (pull f) := by
  intro T U
  constructor
  · intro h s hs
    exact ⟨T.closed.legal hs, h (subset_generate ⟨s, hs, rfl⟩ (f.legal (T.closed.legal hs)))⟩
  · intro h
    refine generate_le_iff.2 ?_
    rintro _ ⟨s, hs, rfl⟩ -
    exact (h hs).2

theorem filterMap_some_map {α β : Type*} (g : α → β) (s : List α) :
    s.filterMap (fun m => some (g m)) = s.map g := by
  induction s <;> simp_all

theorem pull_toPHom (f : G.Hom H) (T : TraceModel H) : pull f.toPHom T = comap f T := by
  ext s
  change s ∈ G.Legal ∧ s.filterMap (fun m => some (f.map m)) ∈ T ↔ s ∈ G.Legal ∧ s.map f.map ∈ T
  rw [filterMap_some_map]

end Silmaril.Proofs.Games.Abstract.Hiding
