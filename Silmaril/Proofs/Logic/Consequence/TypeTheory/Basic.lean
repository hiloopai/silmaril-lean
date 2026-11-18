module

public import Silmaril.Logic.Consequence.Defs
public import Silmaril.Logic.Consequence.Structural.Defs
public import Silmaril.Logic.Consequence.TypeTheory.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Soundness.Thms

/-! Proofs for `Silmaril.Logic.Consequence.TypeTheory.Thms`: pulling a list-premise system back
along a map of formulas keeps identity, weakening and cut. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.TypeTheory

open Silmaril.Consequence

universe u v

theorem closed_pullback_map {C : Type u} {D : Type v} (f : C → D) {S : System (List D) D}
    (h : Structural.Closed Structural.tarskiRules S) :
    Structural.Closed Structural.tarskiRules (S.pullback (List.map f) f) where
  refl _ _ _ hc := h.refl trivial (List.mem_map_of_mem hc)
  weak _ _ _ hsub d := h.weak (fun _ hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact List.mem_map_of_mem (hsub hy)) d
  cut _ ps c hps hc := by
    have e₁ : (ps.map fun p => (p.1.map f, f p.2)).map Prod.snd = (ps.map Prod.snd).map f := by
      simp [List.map_map, Function.comp_def]
    have e₂ : (ps.map fun p => (p.1.map f, f p.2)).flatMap Prod.fst =
        (ps.flatMap Prod.fst).map f := by
      simp [List.flatMap_map, List.map_flatMap]
    have := h.cut trivial (ps := ps.map fun p => (p.1.map f, f p.2)) (c := f c)
      (fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact hps q hq)
      (e₁ ▸ hc)
    show S _ _
    rw [← e₂]
    exact this

open Silmaril.Logic.TypeTheory Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Logic.SetTheory

/-- With a tower of `levels` universes, bounded MLTT does not derive `⊢ 0 : 𝟘` from no
hypotheses. -/
theorem bounded_empty_consistent (levels : ℕ) [HasFiniteTower.{u} levels] :
    (Silmaril.Consequence.TypeTheory.boundedDerives.{u} levels).ConsistentWrt
      (Finite.emptySentence levels) [] := by
  intro h
  have hd : ECtx.JEqB levels (Subtype.val '' {x | x ∈ ([] : List (Finite.Sentence levels))})
      .nil .empty .zero .zero := h
  have hc : ECtx.JEqB levels ∅ .nil .empty .zero .zero := by simpa using hd
  exact ECtx.JEqB.no_closed_empty (HasFiniteTower.tower.{u} levels) hc

end Silmaril.Proofs.Logic.Consequence.TypeTheory
