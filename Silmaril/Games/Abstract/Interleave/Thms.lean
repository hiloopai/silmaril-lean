module

public import Silmaril.Games.Abstract.Interleave.Defs
public import Silmaril.Games.Abstract.Game.Thms

/-!
# Interleaved tasks: the synchronous submodel embeds

* `comap_single_map`, `single_map_injective`, `single_map_le_iff`: a model of
  one task embeds into the models of interleaved tasks, reflecting
  refinement.
* `exists_not_single`: with two distinct tasks and a Proponent move that can
  open a play, the asynchronous top model is not the image of any synchronous
  model. The asynchronous models are strictly richer.
-/

public section

namespace Silmaril.Games.Abstract

universe u

variable {G : Game.{u}} {ι : Type u} [DecidableEq ι]

namespace TraceModel

theorem single_injective (i : ι) : Function.Injective (Game.Hom.single (G := G) i).map :=
  fun _ _ h => (Prod.mk.inj h).2

/-- One task's model is recovered from its image. -/
theorem comap_single_map (i : ι) (T : TraceModel G) :
    comap (Game.Hom.single i) (map (Game.Hom.single (ι := ι) i) T) = T :=
  comap_map_eq _ (single_injective i) (fun _ h => h) T

/-- The synchronous submodel embeds. -/
theorem single_map_injective (i : ι) :
    Function.Injective (map (Game.Hom.single (G := G) (ι := ι) i)) :=
  map_injective _ (single_injective i) fun _ h => h

/-- The embedding reflects refinement. -/
theorem single_map_le_iff (i : ι) {T U : TraceModel G} :
    map (Game.Hom.single (ι := ι) i) T ≤ map (Game.Hom.single i) U ↔ T ≤ U :=
  map_le_map_iff _ (single_injective i) fun _ h => h

/-- With two tasks, the asynchronous models are strictly richer. -/
theorem exists_not_single {i j : ι} (hij : i ≠ j) {m : G.Move} (hm : [m] ∈ G.Legal)
    (hP : ¬ G.IsO m) : ∀ T : TraceModel G, map (Game.Hom.single (ι := ι) i) T ≠ ⊤ := by
  intro T h
  have hl : [(j, m)] ∈ (G.interleave ι).Legal := by
    intro k
    by_cases hk : j = k
    · subst hk; simpa [Game.taskProj] using hm
    · simpa [Game.taskProj, hk] using G.nil_legal
  have : [(j, m)] ∈ map (Game.Hom.single (ι := ι) i) T := h ▸ mem_top.2 hl
  obtain ⟨-, u, hu, p₀, w, he, hp₀, hw⟩ := this
  rcases p₀ with _ | ⟨x, p₀⟩
  · simp only [List.nil_append] at he
    exact hP (hw (j, m) (he ▸ List.mem_singleton_self _))
  · simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    rcases hu with rfl | ⟨⟨t, -, rfl⟩, -⟩
    · simp at hp₀
    · rcases t with _ | ⟨y, t⟩
      · simp at hp₀
      · simp only [List.map_cons, List.cons_prefix_cons] at hp₀
        exact hij (congrArg Prod.fst hp₀.1).symm

end TraceModel

end Silmaril.Games.Abstract
