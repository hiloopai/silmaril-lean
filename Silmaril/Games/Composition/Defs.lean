module

public import Silmaril.Games.Strategy.Defs
public import Silmaril.Games.Zip.Thms
import Silmaril.Proofs.Games.Composition.Legal
import Silmaril.Proofs.Games.Composition.Copycat

/-!
# Composition and copycat

* `σ.comp τ : Strategy E G` for `σ : Strategy E F` and `τ : Strategy F G`
  (diagrammatic order, as Mathlib's `≫`): `τ` implements `G` by calling `F`,
  whose calls `σ` serves by calling `E`. Its plays are the visible traces of
  the interactions (`Zip`) of a play of `σ` with a play of `τ`; the `F`-moves
  are hidden.
* `Strategy.id E : Strategy E E` is copycat: it forwards each question from
  the right to the left and each answer from the left to the right. Its plays
  are the prefixes of `Ev.double w` for alternating `w`.

Legality, prefix closure and receptiveness of the composite are proved in
`Silmaril.Proofs.Games.Composition.Legal`; those of copycat in
`Silmaril.Proofs.Games.Composition.Copycat`. The laws (unit, associativity,
monotonicity) are in `Silmaril.Games.Composition.Thms`.
-/

@[expose] public section

namespace Silmaril.Games

universe u

namespace Strategy

variable {E F G : Sig.{u}}

/-- The interaction of legal plays is legal. -/
theorem legal_of_zip {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (hs : Legal s) (ht : Legal t) (h : Zip s t p) : Legal p :=
  Silmaril.Proofs.Games.Composition.legal_of_zip hs ht h

/-- An Opponent move after an interaction can be absorbed by one of the two
strategies. -/
theorem receptive_of_zip (σ : Strategy E F) (τ : Strategy F G) {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (hs : s ∈ σ) (ht : t ∈ τ) (h : Zip s t p)
    {x y : Pos E G} {o : Move E G} (hx : Path .idle p x) (hxy : Step x o y) (ho : o.IsO) :
    ∃ s' ∈ σ, ∃ t' ∈ τ, Zip s' t' (p ++ [o]) :=
  Silmaril.Proofs.Games.Composition.receptive_of_zip σ τ hs ht h hx hxy ho

/-- Prefixes of copycat plays are legal. -/
theorem _root_.Silmaril.Games.Ev.legal_of_prefix_double {w : List (Ev E)} (hw : Ev.Alternating w)
    {c : List (Move E E)} (hc : c <+: Ev.double w) : Legal c :=
  Silmaril.Proofs.Games.Composition.legal_of_prefix_double hw hc

/-- Copycat plays are receptive. -/
theorem _root_.Silmaril.Games.Ev.receptive_double {w : List (Ev E)} (hw : Ev.Alternating w)
    {c : List (Move E E)} (hc : c <+: Ev.double w) {x y : Pos E E} {o : Move E E}
    (hx : Path .idle c x) (hxy : Step x o y) (ho : o.IsO) :
    ∃ w', Ev.Alternating w' ∧ c ++ [o] <+: Ev.double w' :=
  Silmaril.Proofs.Games.Composition.receptive_double hw hc hx hxy ho

/-- Composition `σ.comp τ` (first `σ`, then `τ`): `τ : F ↠ G` runs on top of
`σ : E ↠ F`, the interactions at `F` are hidden. -/
def comp (σ : Strategy E F) (τ : Strategy F G) : Strategy E G where
  plays := {p | ∃ s ∈ σ, ∃ t ∈ τ, Zip s t p}
  nil_mem := ⟨[], σ.nil_mem, [], τ.nil_mem, .nil⟩
  legal := fun ⟨_, hs, _, ht, h⟩ =>
    legal_of_zip (σ.legal hs) (τ.legal ht) h
  of_prefix := fun ⟨_, hs, _, ht, h⟩ hq => by
    obtain ⟨s', t', hs', ht', h'⟩ := h.of_prefix hq
    exact ⟨s', σ.of_prefix hs hs', t', τ.of_prefix ht ht', h'⟩
  receptive := fun ⟨_, hs, _, ht, h⟩ hx hxy ho =>
    receptive_of_zip σ τ hs ht h hx hxy ho

/-- The plays of a composite are the visible parts of interactions. -/
theorem mem_comp {σ : Strategy E F} {τ : Strategy F G} {p : List (Move E G)} :
    p ∈ σ.comp τ ↔ ∃ s ∈ σ, ∃ t ∈ τ, Zip s t p := Iff.rfl

/-- The copycat strategy: the identity on `E`. -/
protected def id (E : Sig.{u}) : Strategy E E where
  plays := {c | ∃ w, Ev.Alternating w ∧ c <+: Ev.double w}
  nil_mem := ⟨[], .nil, List.nil_prefix⟩
  legal := fun ⟨_, hw, hc⟩ => Ev.legal_of_prefix_double hw hc
  of_prefix := fun ⟨w, hw, hc⟩ h => ⟨w, hw, h.trans hc⟩
  receptive := fun ⟨_, hw, hc⟩ hx hxy ho =>
    Ev.receptive_double hw hc hx hxy ho

/-- The plays of copycat. -/
theorem mem_id {c : List (Move E E)} :
    c ∈ Strategy.id E ↔ ∃ w, Ev.Alternating w ∧ c <+: Ev.double w := Iff.rfl

end Strategy

end Silmaril.Games
