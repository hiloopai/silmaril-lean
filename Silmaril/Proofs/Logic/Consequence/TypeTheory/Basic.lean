module

public import Silmaril.Logic.Consequence.Defs
public import Silmaril.Logic.Consequence.Structural.Defs

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

end Silmaril.Proofs.Logic.Consequence.TypeTheory
