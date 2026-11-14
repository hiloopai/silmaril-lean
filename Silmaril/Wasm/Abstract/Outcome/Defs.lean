module

public import Silmaril.Games.Abstract.Outcome.Defs
public import Silmaril.Wasm.Behaviour.Relations

/-!
# Wasm call behaviours as outcome tags

A whole Wasm call ends in one of the outcomes of `Silmaril.Wasm.Behaviour`:
returned values, a trap, an uncaught exception, or divergence. `toTag` reads
it as an outcome tag of `Silmaril.Games.Abstract.Outcome`, with result type
`List V ⊕ ULift Nat` (values, or the address of an uncaught exception).

This defines the two equivalences of Wasm calls asked for, on behaviour sets
of a nondeterministic semantics (for example
`Silmaril.Wasm.Behaviour.Semantics.V3.behaviours`):

* `TagEquiv s t`: equal tags, so trap and divergence are distinguished;
* `CoarseEquiv s t`: equal tags after `collapse`, so trap ≈ divergence.

`Silmaril.Wasm.Abstract.Outcome.Thms` proves that they are exactly the
existing `Behaviours.Equiv Eq` and `Behaviours.Equiv TrapDiv`. Whole-call
behaviours carry no import/export trace. The trace-level versions are the
generic `OMachine` notions. Applying them to an instance needs a machine whose
silent steps are the host-free reduction steps: the scalar instance
machine of `Silmaril.Wasm.Abstract.Instance` folds host-free runs into its
visible moves, so there a diverging call and a stuck one both just never
answer.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games.Abstract

universe u

/-- A call behaviour as an outcome tag. -/
def toTag {V : Type u} : Behaviour V → Tag (List V ⊕ ULift.{u} Nat)
  | .returns vs => .ret (.inl vs)
  | .throws a => .ret (.inr (ULift.up a))
  | .traps => .trap
  | .diverges => .div

/-- Equal tags: trap and divergence distinguished. -/
def TagEquiv {V : Type u} (s t : Set (Behaviour V)) : Prop := toTag '' s = toTag '' t

/-- Equal tags up to trap ≈ divergence. -/
def CoarseEquiv {V : Type u} (s t : Set (Behaviour V)) : Prop :=
  (fun b => (toTag b).collapse) '' s = (fun b => (toTag b).collapse) '' t

end Silmaril.Wasm.Abstract
