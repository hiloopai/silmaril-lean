module

public import Silmaril.Games.Play.Defs

/-!
# Splitting a play of `E ↠ F₁ ⊕ₛ F₂`

A play of a component offering both `F₁` and `F₂` splits into a play of
`E ↠ F₁` and a play of `E ↠ F₂`: each round, with the calls to `E` made
during it, goes to the side of its question. `Split.side b s` is the side of
the round in progress after `s`, starting from side `b`. This is the
projection behind `Strategy.pair` (`Silmaril.Games.Pair.Defs`).
-/

@[expose] public section

namespace Silmaril.Games.Split

universe u

variable {E F₁ F₂ : Sig.{u}}

/-- Split a play; `b` is the side of the current round (`false`: `F₁`,
`true`: `F₂`). -/
def halves : Bool → List (Move E (F₁ ⊕ₛ F₂)) → List (Move E F₁) × List (Move E F₂)
  | _, [] => ([], [])
  | false, .inl e :: s => ((.inl e :: (halves false s).1), (halves false s).2)
  | true, .inl e :: s => ((halves true s).1, .inl e :: (halves true s).2)
  | _, .inr (.ask (.inl q)) :: s => (.inr (.ask q) :: (halves false s).1, (halves false s).2)
  | _, .inr (.ask (.inr q)) :: s => ((halves true s).1, .inr (.ask q) :: (halves true s).2)
  | b, .inr (.ans (.inl q) r) :: s => (.inr (.ans q r) :: (halves b s).1, (halves b s).2)
  | b, .inr (.ans (.inr q) r) :: s => ((halves b s).1, .inr (.ans q r) :: (halves b s).2)

/-- The side of the current round after a play. -/
def side : Bool → List (Move E (F₁ ⊕ₛ F₂)) → Bool
  | b, [] => b
  | _, .inr (.ask (.inl _)) :: s => side false s
  | _, .inr (.ask (.inr _)) :: s => side true s
  | b, _ :: s => side b s

/-- How the position of a play of `E ↠ F₁ ⊕ₛ F₂` relates to the current side
and the positions of its two halves. -/
inductive Rel : Pos E (F₁ ⊕ₛ F₂) → Bool → Pos E F₁ → Pos E F₂ → Prop
  | idle (b : Bool) : Rel .idle b .idle .idle
  | runL (q : F₁.Op) : Rel (.run (.inl q)) false (.run q) .idle
  | runR (q : F₂.Op) : Rel (.run (.inr q)) true .idle (.run q)
  | waitL (q : F₁.Op) (m : E.Op) : Rel (.wait (.inl q) m) false (.wait q m) .idle
  | waitR (q : F₂.Op) (m : E.Op) : Rel (.wait (.inr q) m) true .idle (.wait q m)


/-! ## Facts the pairing of strategies needs

`Silmaril.Games.Strategy.pair` (`Silmaril.Games.Pair.Defs`) needs these in its proof
fields: splitting is monotone for prefixes, preserves paths (tracking positions
with `Rel`), and appending one move appends it to one half.
-/

/-- The halves of a prefix are prefixes of the halves. -/
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

/-- The halves of a path are paths, between related positions. -/
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

end Silmaril.Games.Split

