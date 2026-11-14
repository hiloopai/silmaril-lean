module

public import Silmaril.Games.Abstract.Game.Defs
public import Silmaril.Proofs.Games.Abstract.Game.Lattice
public import Mathlib.Data.List.Basic

/-!
# Pushforward along an embedding of games: proofs

A model is closed under legal runs of Opponent moves; along a morphism that is
injective on moves and reflects Opponent polarity, `comap` retracts `map`.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.Game

open Silmaril.Games.Abstract Silmaril.Games.Abstract.TraceModel

universe u v

variable {G : Game.{u}} {H : Game.{v}}

theorem append_mem_of_isO {T : TraceModel G} {s w : List G.Move} (hs : s ∈ T)
    (hw : ∀ o ∈ w, G.IsO o) (hl : s ++ w ∈ G.Legal) : s ++ w ∈ T := by
  induction w using List.reverseRecOn with
  | nil => simpa using hs
  | append_singleton w o ih =>
    have hl' : s ++ w ∈ G.Legal := G.legal_of_prefix hl (by simp)
    have := T.closed.receptive (ih (fun o h => hw o (by simp [h])) hl')
      (by simpa using hl) (hw o (by simp))
    simpa using this

theorem prefix_of_map_prefix {α β : Type*} {f : α → β} (hf : Function.Injective f)
    {s t : List α} (h : s.map f <+: t.map f) : s <+: t := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨a, b, rfl, ha, -⟩ := List.map_eq_append_iff.1 hr.symm
  exact ⟨b, by rw [List.map_injective_iff.2 hf ha]⟩

theorem comap_map_eq (f : G.Hom H) (hf : Function.Injective f.map)
    (hO : ∀ m, H.IsO (f.map m) → G.IsO m) (T : TraceModel G) : comap f (map f T) = T := by
  apply le_antisymm
  · rintro s ⟨hs, -, u, hu, p₀, w, he, hp₀, hw⟩
    obtain ⟨s₀, s₁, rfl, rfl, rfl⟩ := List.map_eq_append_iff.1 he
    have h₀ : s₀ ∈ T := by
      rcases hu with rfl | ⟨⟨t, ht, rfl⟩, -⟩
      · obtain h := List.prefix_nil.1 hp₀
        rw [List.map_eq_nil_iff.1 h]
        exact T.closed.nil_mem
      · exact T.closed.of_prefix ht (prefix_of_map_prefix hf hp₀)
    exact append_mem_of_isO h₀ (fun o ho => hO o (hw _ (List.mem_map_of_mem ho))) hs
  · exact (gc_map_comap f).le_u_l T

end Silmaril.Proofs.Games.Abstract.Game
