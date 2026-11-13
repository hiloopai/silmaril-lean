module

public import Silmaril.Prelude.Defs

/-!
# Parallel interaction with hiding

`Zip s t p` says that the trace `s` over `α ⊕ β` and the trace `t` over
`β ⊕ γ` interact to produce the visible trace `p` over `α ⊕ γ`: the two traces
are interleaved, every `β`-event of `s` (on its right) synchronises with the
same event of `t` (on its left), and the synchronised events are hidden.

This is the composition of the trace model, stated once for arbitrary
alphabets. It knows nothing about games: `Silmaril.Games.Strategy.comp` applies
it to `Move E F = Ev E ⊕ Ev F` and `Move F G = Ev F ⊕ Ev G`. Because `Zip` is
generic, associativity of composition is a fact about interleavings alone
(`Silmaril.Games.Zip.assoc`), proved without reference to legality.
-/

@[expose] public section

namespace Silmaril.Games

universe u v w

/-- `Zip s t p`: `s` and `t` synchronise on their shared alphabet `β`, leaving
`p` visible. -/
inductive Zip {α : Type u} {β : Type v} {γ : Type w} :
    List (α ⊕ β) → List (β ⊕ γ) → List (α ⊕ γ) → Prop
  /-- Both traces are empty. -/
  | nil : Zip [] [] []
  /-- The left trace makes a visible move. -/
  | left {s t p} (a : α) : Zip s t p → Zip (.inl a :: s) t (.inl a :: p)
  /-- The right trace makes a visible move. -/
  | right {s t p} (c : γ) : Zip s t p → Zip s (.inr c :: t) (.inr c :: p)
  /-- Both traces perform the shared event `b`, which is hidden. -/
  | sync {s t p} (b : β) : Zip s t p → Zip (.inr b :: s) (.inl b :: t) p

/-! ## Facts the strategy definitions need

`Silmaril.Games.Strategy.comp` (`Silmaril.Games.Composition.Defs`) needs these in its
proof fields; the other facts about `Zip` are in `Silmaril.Games.Zip.Thms`.
-/

namespace Zip

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Append a visible move of the left trace. -/
theorem append_left {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (a : α) : Zip (s ++ [.inl a]) t (p ++ [.inl a]) := by
  induction h with
  | nil => exact .left a .nil
  | left a' _ ih => exact .left a' ih
  | right c _ ih => exact .right c ih
  | sync b _ ih => exact .sync b ih

/-- Append a visible move of the right trace. -/
theorem append_right {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (c : γ) : Zip s (t ++ [.inr c]) (p ++ [.inr c]) := by
  induction h with
  | nil => exact .right c .nil
  | left a _ ih => exact .left a ih
  | right c' _ ih => exact .right c' ih
  | sync b _ ih => exact .sync b ih

/-- Every prefix of the visible trace comes from prefixes of the two traces. -/
theorem of_prefix {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p q : List (α ⊕ γ)}
    (h : Zip s t p) (hq : q <+: p) : ∃ s' t', s' <+: s ∧ t' <+: t ∧ Zip s' t' q := by
  induction h generalizing q with
  | nil =>
    rw [List.prefix_nil] at hq
    subst hq
    exact ⟨[], [], List.nil_prefix, List.nil_prefix, .nil⟩
  | left a _ ih =>
    rcases List.prefix_cons_iff.1 hq with rfl | ⟨q', rfl, hq'⟩
    · exact ⟨[], [], List.nil_prefix, List.nil_prefix, .nil⟩
    · obtain ⟨s', t', hs, ht, h⟩ := ih hq'
      exact ⟨_, t', List.cons_prefix_cons.2 ⟨rfl, hs⟩, ht, .left a h⟩
  | right c _ ih =>
    rcases List.prefix_cons_iff.1 hq with rfl | ⟨q', rfl, hq'⟩
    · exact ⟨[], [], List.nil_prefix, List.nil_prefix, .nil⟩
    · obtain ⟨s', t', hs, ht, h⟩ := ih hq'
      exact ⟨s', _, hs, List.cons_prefix_cons.2 ⟨rfl, ht⟩, .right c h⟩
  | sync b _ ih =>
    obtain ⟨s', t', hs, ht, h⟩ := ih hq
    exact ⟨_, _, List.cons_prefix_cons.2 ⟨rfl, hs⟩, List.cons_prefix_cons.2 ⟨rfl, ht⟩,
      .sync b h⟩

end Zip

end Silmaril.Games
