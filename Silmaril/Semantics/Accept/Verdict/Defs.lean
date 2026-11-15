module

public import Silmaril.Semantics.Accept.Defs

/-!
# Combined verdicts: some execution accepts and no execution rejects

Components and modules can signal both *accept* and *reject*. Their combined language is

  `acceptsSafely run acc rej = acceptsSome run acc ∩ neverRejects run rej`:

some execution of `a` reaches an accepting outcome, and no execution of `a` reaches a
rejecting outcome. Both quantifiers range over the **same** set of executions `run a`. When
executions depend on an environment, take `run` over one environment class (`envRun r E`)
and use that same `run` for both quantifiers. Accepting under one class while never rejecting
under another is a different property, and this file does not define it.

## Accept and reject may overlap

`acc` and `rej` are independent predicates on outcomes, and nothing here assumes they are
disjoint. An outcome in `conflicts acc rej = acc ∩ rej` is both accepting and rejecting, for
example when one import is used for both verdicts or when a run calls both. An input with a
conflicting outcome is never in the combined language (`Thms`). Acceptance in the combined
language is always witnessed by an outcome in `acc \ rej`. `conflictInputs run acc rej` is the
set of inputs with some conflicting outcome.

## Not monotone in the executions

Restricting the executions (fewer outcomes, for example a smaller environment class or trace
refinement) can remove acceptance, since `acceptsSome` shrinks, and can also remove
rejection, since `neverRejects` grows. So the combined language is in general neither
monotone nor antitone under inclusion of runners; `Thms` gives counterexamples in both
directions and the conditions under which inclusion is preserved.

The Wasm instance with distinguished `accept`/`reject` imports is
`Silmaril.Wasm.Game.Accept.acceptedNotRejected`, owned by the Wasm development.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w

variable {α : Type u} {ω : Type v}

/-- Some execution accepts and no execution rejects (one runner for both quantifiers). -/
def acceptsSafely (run : α → Set ω) (acc rej : Set ω) : Set α :=
  acceptsSome run acc ∩ neverRejects run rej

/-- Outcomes that are both accepting and rejecting. -/
def conflicts (acc rej : Set ω) : Set ω := acc ∩ rej

/-- Inputs with some conflicting outcome. -/
def conflictInputs (run : α → Set ω) (acc rej : Set ω) : Set α :=
  rejectsSome run (conflicts acc rej)

/-- The executions of an input over an environment class: the union over `e ∈ E`. -/
def envRun {ε : Type w} (r : ε → α → Set ω) (E : Set ε) : α → Set ω :=
  fun a => {o | ∃ e ∈ E, o ∈ r e a}

end Silmaril.Accept
