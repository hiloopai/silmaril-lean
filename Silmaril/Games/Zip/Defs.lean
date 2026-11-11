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

end Silmaril.Games
