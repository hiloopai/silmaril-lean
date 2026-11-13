module

public import Silmaril.Wasm.Logic.Strategy.Defs

/-!
# Specifications as strategies: composition

`ag_zip`: the interaction of an assume/guarantee correct play of `E ↠ F` (for `I`
and `M`) with one of `F ↠ G` (for `M` and `S`) is assume/guarantee correct for
`I` and `S`. The proof is an induction on the interaction (`Silmaril.Games.Zip`):
each hidden `F` event is a Proponent move of exactly one of the two plays, whose
guarantee is the other's assumption. Hence `agStrat_comp`: composing the
assume/guarantee strategies refines the composed one, and with
`Silmaril.Games.Strategy.comp_mono`, linked components that meet their specifications
meet the composed specification (`comp_refines`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Strategy

open Silmaril.Games

universe u

variable {E F G : Sig.{u}} {I : ISpec E} {M : ISpec F} {S : ISpec G}

/-- A visible lower event of the left play. -/
theorem ag_left {e : Ev E} {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (ih : AG I M s → AG M S t → AG I S p) (hs : AG I M (.inl e :: s)) (ht : AG M S t) :
    AG I S (.inl e :: p) := by
  rcases e with m | ⟨m, n⟩
  · obtain ⟨hg, hs'⟩ := hs.2 trivial
    exact ⟨fun h => h.elim, fun _ => ⟨hg, ih hs' ht⟩⟩
  · exact ⟨fun _ hg => ih (hs.1 trivial hg) ht, fun h => h.elim⟩

/-- A visible upper event of the right play. -/
theorem ag_right {e : Ev G} {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (ih : AG I M s → AG M S t → AG I S p) (hs : AG I M s) (ht : AG M S (.inr e :: t)) :
    AG I S (.inr e :: p) := by
  rcases e with m | ⟨m, n⟩
  · exact ⟨fun _ hg => ih hs (ht.1 trivial hg), fun h => h.elim⟩
  · obtain ⟨hg, ht'⟩ := ht.2 trivial
    exact ⟨fun h => h.elim, fun _ => ⟨hg, ih hs ht'⟩⟩

/-- A hidden event: a Proponent move of exactly one side. -/
theorem ag_sync {e : Ev F} {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (ih : AG I M s → AG M S t → AG I S p) (hs : AG I M (.inr e :: s)) (ht : AG M S (.inl e :: t)) :
    AG I S p := by
  rcases e with m | ⟨m, n⟩
  · obtain ⟨hg, ht'⟩ := ht.2 trivial
    exact ih (hs.1 trivial hg) ht'
  · obtain ⟨hg, hs'⟩ := hs.2 trivial
    exact ih hs' (ht.1 trivial hg)

/-- **Assume/guarantee composition** of plays. -/
theorem ag_zip {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (hz : Zip s t p) : AG I M s → AG M S t → AG I S p := by
  induction hz with
  | nil => exact fun _ _ => trivial
  | left a _ ih => exact fun hs ht => ag_left ih hs ht
  | right c _ ih => exact fun hs ht => ag_right ih hs ht
  | sync b _ ih => exact fun hs ht => ag_sync ih hs ht

/-- **Composition of specification strategies.** -/
theorem agStrat_comp : (agStrat I M).comp (agStrat M S) ≤ agStrat I S :=
  fun _ ⟨_, ⟨hls, hs⟩, _, ⟨hlt, ht⟩, hz⟩ => ⟨Strategy.legal_of_zip hls hlt hz, ag_zip hz hs ht⟩

/-- **Linked components meet the composed specification.** -/
theorem comp_refines {σ : Strategy E F} {τ : Strategy F G} (hσ : σ ≤ agStrat I M)
    (hτ : τ ≤ agStrat M S) : σ.comp τ ≤ agStrat I S :=
  (Strategy.comp_mono hσ hτ).trans agStrat_comp

end Silmaril.Wasm.Logic.Strategy
