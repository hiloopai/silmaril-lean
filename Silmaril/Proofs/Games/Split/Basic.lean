module

public import Silmaril.Games.Split.Defs
public import Silmaril.Games.Play.Thms

/-!
# Splitting a play: proofs

Proofs for `Silmaril.Games.Split.Thms`.
-/

public section

namespace Silmaril.Proofs.Games.Split

open Silmaril.Games Silmaril.Games.Split

universe u

variable {E F₁ F₂ : Sig.{u}}

theorem halves_prefix {p q : List (Move E (F₁ ⊕ₛ F₂))} (h : q <+: p) (b : Bool) :
    (halves b q).1 <+: (halves b p).1 ∧ (halves b q).2 <+: (halves b p).2 := by
  induction p generalizing q b with
  | nil =>
    rw [List.prefix_nil] at h
    subst h
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | cons x p ih =>
    rcases List.prefix_cons_iff.1 h with rfl | ⟨q', rfl, h'⟩
    · exact ⟨List.nil_prefix, List.nil_prefix⟩
    rcases x with e | (q | ⟨q, r⟩)
    · cases b with
      | false => exact ⟨List.cons_prefix_cons.2 ⟨rfl, (ih h' _).1⟩, (ih h' _).2⟩
      | true => exact ⟨(ih h' _).1, List.cons_prefix_cons.2 ⟨rfl, (ih h' _).2⟩⟩
    · rcases q with q | q
      · exact ⟨List.cons_prefix_cons.2 ⟨rfl, (ih h' _).1⟩, (ih h' _).2⟩
      · exact ⟨(ih h' _).1, List.cons_prefix_cons.2 ⟨rfl, (ih h' _).2⟩⟩
    · rcases q with q | q
      · exact ⟨List.cons_prefix_cons.2 ⟨rfl, (ih h' _).1⟩, (ih h' _).2⟩
      · exact ⟨(ih h' _).1, List.cons_prefix_cons.2 ⟨rfl, (ih h' _).2⟩⟩

theorem halves_path {x y : Pos E (F₁ ⊕ₛ F₂)} {p : List (Move E (F₁ ⊕ₛ F₂))} (h : Path x p y) :
    ∀ {b x₁ x₂}, Rel x b x₁ x₂ → ∃ y₁ y₂, Path x₁ (halves b p).1 y₁ ∧
      Path x₂ (halves b p).2 y₂ ∧ Rel y (side b p) y₁ y₂ := by
  induction h with
  | nil => intro b x₁ x₂ hr; exact ⟨x₁, x₂, .nil _, .nil _, hr⟩
  | @cons a c d o s st _ ih =>
    show ∀ {b x₁ x₂}, Rel a b x₁ x₂ → ∃ y₁ y₂, Path x₁ (halves b (o :: s)).1 y₁ ∧
      Path x₂ (halves b (o :: s)).2 y₂ ∧ Rel d (side b (o :: s)) y₁ y₂
    intro b x₁ x₂ hr
    cases st with
    | ask q =>
      cases hr
      rcases q with q | q
      · obtain ⟨y₁, y₂, h₁, h₂, hr⟩ := ih (Rel.runL q)
        exact ⟨y₁, y₂, .cons (.ask q) h₁, h₂, hr⟩
      · obtain ⟨y₁, y₂, h₁, h₂, hr⟩ := ih (Rel.runR q)
        exact ⟨y₁, y₂, h₁, .cons (.ask q) h₂, hr⟩
    | call q m =>
      cases hr with
      | runL q =>
        obtain ⟨y₁, y₂, h₁, h₂, hr⟩ := ih (Rel.waitL q m)
        exact ⟨y₁, y₂, .cons (.call q m) h₁, h₂, hr⟩
      | runR q =>
        obtain ⟨y₁, y₂, h₁, h₂, hr⟩ := ih (Rel.waitR q m)
        exact ⟨y₁, y₂, h₁, .cons (.call q m) h₂, hr⟩
    | reply q m n =>
      cases hr with
      | waitL q m =>
        obtain ⟨y₁, y₂, h₁, h₂, hr⟩ := ih (Rel.runL q)
        exact ⟨y₁, y₂, .cons (.reply q m n) h₁, h₂, hr⟩
      | waitR q m =>
        obtain ⟨y₁, y₂, h₁, h₂, hr⟩ := ih (Rel.runR q)
        exact ⟨y₁, y₂, h₁, .cons (.reply q m n) h₂, hr⟩
    | ret q r =>
      cases hr with
      | runL q =>
        obtain ⟨y₁, y₂, h₁, h₂, hr⟩ := ih (Rel.idle false)
        exact ⟨y₁, y₂, .cons (.ret q r) h₁, h₂, hr⟩
      | runR q =>
        obtain ⟨y₁, y₂, h₁, h₂, hr⟩ := ih (Rel.idle true)
        exact ⟨y₁, y₂, h₁, .cons (.ret q r) h₂, hr⟩

/-- Appending a lower move appends it to the current side; appending an upper
move appends it to its own side. -/
theorem halves_concat (b : Bool) (p : List (Move E (F₁ ⊕ₛ F₂))) (o : Move E (F₁ ⊕ₛ F₂)) :
    (halves b (p ++ [o])).1 = (halves b p).1 ++ (halves (side b p) [o]).1 ∧
    (halves b (p ++ [o])).2 = (halves b p).2 ++ (halves (side b p) [o]).2 := by
  induction p generalizing b with
  | nil => simp [halves, side]
  | cons x p ih =>
    rcases x with e | (q | ⟨q, r⟩)
    · cases b <;> simp [halves, side, ih]
    · rcases q with q | q <;> simp [halves, side, ih]
    · rcases q with q | q <;> simp [halves, side, ih]

end Silmaril.Proofs.Games.Split
