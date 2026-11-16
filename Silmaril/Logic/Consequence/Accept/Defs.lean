module

public import Silmaril.Logic.Consequence.Defs
public import Silmaril.Semantics.Accept.Defs

/-!
# Acceptors as consequence systems

A language (`Set α`, as in `Silmaril.Accept`) can sit on either coordinate of a system
`System Ax C`, and be read with a fixed partner or with every partner. That gives four lifts,
each the **least** system with its property (`Thms`, the `…_le_iff` lemmas):

| lift | language on | judgements | reading |
|---|---|---|---|
| `liftAxFF L ff` | contexts, `L : Set Ax` | `a ⊢ ff` for `a ∈ L` | an accepted context is refuted (proves the bottom `ff`) |
| `liftTTC tt L` | conclusions, `L : Set C` | `tt ⊢ c` for `c ∈ L` | an accepted conclusion follows from the empty/true context `tt` |
| `liftAxAll L` | contexts, `L : Set Ax` | `a ⊢ c` for `a ∈ L`, every `c` | an accepted context proves everything (is inconsistent) |
| `liftCAll L` | conclusions, `L : Set C` | `a ⊢ c` for `c ∈ L`, every `a` | an accepted conclusion follows from every context |

The language is recovered from each lift (`Thms`): exactly for `liftAxFF`, `liftTTC` and
`liftCAll`; for `liftAxAll` only when `C` is nonempty, because with no conclusions every context
proves everything.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v

variable {Ax : Type u} {C : Type v}

/-- An accepted context proves the bottom conclusion `ff`, and nothing else is proved. -/
def liftAxFF (L : Set Ax) (ff : C) : System Ax C := fun a c => a ∈ L ∧ c = ff

/-- An accepted conclusion follows from the true context `tt`, and nothing else is proved. -/
def liftTTC (tt : Ax) (L : Set C) : System Ax C := fun a c => a = tt ∧ c ∈ L

/-- An accepted context proves every conclusion. -/
def liftAxAll (L : Set Ax) : System Ax C := fun a _ => a ∈ L

/-- An accepted conclusion follows from every context. -/
def liftCAll (L : Set C) : System Ax C := fun _ c => c ∈ L

end Silmaril.Consequence
