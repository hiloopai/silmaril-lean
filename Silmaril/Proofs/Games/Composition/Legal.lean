module

public import Silmaril.Games.Strategy.Defs
public import Silmaril.Games.Zip.Thms

/-!
# Composition preserves legality and receptiveness

The interaction of a legal play of `E ↠ F` with a legal play of `F ↠ G` is a
legal play of `E ↠ G`. The proof tracks the three automaton positions along
the interaction; `Compat` lists the four reachable combinations (both idle;
the upper component running; the lower component running on behalf of the
upper one; the lower component waiting for its environment).

Used by `Silmaril.Games.Composition.Defs`.
-/

public section

namespace Silmaril.Proofs.Games.Composition

open Silmaril.Games

universe u

variable {E F G : Sig.{u}}

/-- The reachable combinations of positions during an interaction. -/
inductive Compat : Pos E F → Pos F G → Pos E G → Prop
  | idle : Compat .idle .idle .idle
  | run (g : G.Op) : Compat .idle (.run g) (.run g)
  | call (g : G.Op) (f : F.Op) : Compat (.run f) (.wait g f) (.run g)
  | wait (g : G.Op) (f : F.Op) (e : E.Op) : Compat (.wait f e) (.wait g f) (.wait g e)

theorem zip_path {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∀ {a b c a' b'}, Compat a b c → Path a s a' → Path b t b' →
      ∃ c', Path c p c' ∧ Compat a' b' c' := by
  induction h with
  | nil =>
    intro a b c a' b' hc hs ht
    cases hs; cases ht
    exact ⟨c, .nil _, hc⟩
  | @left s t p x _ ih =>
    show ∀ {a b c a' b'}, Compat a b c → Path a (.inl x :: s) a' → Path b t b' →
      ∃ c', Path c (.inl x :: p) c' ∧ Compat a' b' c'
    intro a b c a' b' hc hs ht
    cases hs with
    | cons hst hs =>
      cases hst <;> cases hc
      · obtain ⟨c', hp, hc'⟩ := ih (Compat.wait _ _ _) hs ht
        exact ⟨c', .cons (.call _ _) hp, hc'⟩
      · obtain ⟨c', hp, hc'⟩ := ih (Compat.call _ _) hs ht
        exact ⟨c', .cons (.reply _ _ _) hp, hc'⟩
  | @right s t p y _ ih =>
    show ∀ {a b c a' b'}, Compat a b c → Path a s a' → Path b (.inr y :: t) b' →
      ∃ c', Path c (.inr y :: p) c' ∧ Compat a' b' c'
    intro a b c a' b' hc hs ht
    cases ht with
    | cons hst ht =>
      cases hst <;> cases hc
      · obtain ⟨c', hp, hc'⟩ := ih (Compat.run _) hs ht
        exact ⟨c', .cons (.ask _) hp, hc'⟩
      · obtain ⟨c', hp, hc'⟩ := ih Compat.idle hs ht
        exact ⟨c', .cons (.ret _ _) hp, hc'⟩
  | @sync s t p z _ ih =>
    show ∀ {a b c a' b'}, Compat a b c → Path a (.inr z :: s) a' → Path b (.inl z :: t) b' →
      ∃ c', Path c p c' ∧ Compat a' b' c'
    intro a b c a' b' hc hs ht
    cases hs with
    | cons hs₁ hs =>
      cases ht with
      | cons ht₁ ht =>
        cases hs₁ <;> cases ht₁ <;> cases hc
        · exact ih (Compat.call _ _) hs ht
        · exact ih (Compat.run _) hs ht

theorem legal_of_zip {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (hs : Legal s) (ht : Legal t) (h : Zip s t p) : Legal p := by
  obtain ⟨_, hs⟩ := hs
  obtain ⟨_, ht⟩ := ht
  obtain ⟨c, hp, -⟩ := zip_path h Compat.idle hs ht
  exact ⟨c, hp⟩

theorem receptive_of_zip (σ : Strategy E F) (τ : Strategy F G) {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (hs : s ∈ σ) (ht : t ∈ τ) (h : Zip s t p)
    {x y : Pos E G} {o : Move E G} (hx : Path .idle p x) (hxy : Step x o y) (ho : o.IsO) :
    ∃ s' ∈ σ, ∃ t' ∈ τ, Zip s' t' (p ++ [o]) := by
  obtain ⟨a, ha⟩ := σ.legal hs
  obtain ⟨b, hb⟩ := τ.legal ht
  obtain ⟨c, hc, hcomp⟩ := zip_path h Compat.idle ha hb
  cases hx.det hc
  cases hxy with
  | ask g =>
    cases hcomp
    exact ⟨s, hs, _, τ.receptive ht hb (.ask g) trivial, h.append_right _⟩
  | reply g e n =>
    cases hcomp
    exact ⟨_, σ.receptive hs ha (.reply _ e n) trivial, t, ht, h.append_left _⟩
  | call => exact ho.elim
  | ret => exact ho.elim

end Silmaril.Proofs.Games.Composition
