module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Set.Sigma
public import Silmaril.Semantics.Accept.Defs

/-!
# Acceptance through relations, partial functions, total maps and indices

Programs that transform values before a language is checked come in three shapes, from most
to least general:

* relations `α -|> β` (Mathlib's `SetRel α β = Set (α × β)`, scoped notation here): a
  nondeterministic program, possibly with no output for some inputs;
* partial functions `α → Option β`: at most one output (`none` = no output, for example a
  failed decode or a trap);
* total maps `α → β`: exactly one output.

A language `L : Set β` on outputs pulls back along each of them in two ways, and the
quantifier matters exactly when an input has no output or several:

* `pullSome R L` (Mathlib's `SetRel.preimage`): *some* output lies in `L`;
* `pullAll R L` (Mathlib's `SetRel.core`): *every* output lies in `L` (vacuous with none).

Rejection uses the dual quantifiers: an input is rejected along `R` by `rej` when some output
is in `rej` (`pullSome R rej`), and *never rejected* when no output is (`pullAll R rejᶜ`).
`Thms` relates these to `acceptsSome`/`neverRejects` of `Silmaril.Semantics.Accept.Defs`
through `outcomes R`.

## Indexed value sets

An indexed value set gives one language per index: `L : ∀ i, Set (A i)` (`IndexedLang A`).

* `eraseSigma L : Set (Σ i, A i)`: forget the index into the dependent pair, losing nothing
  (an order isomorphism, `Thms`).
* For a common carrier (`L : ι → Set α`), erasing the index loses it, and there are two
  choices: `eraseSome L = ⋃ i, L i` (accepted at *some* index) and `eraseAll L = ⋂ i, L i`
  (accepted at *every* index). A value is rejected by `eraseSome L` iff it is rejected at
  *every* index, and rejected by `eraseAll L` iff it is rejected at *some* index (`Thms`).
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w

/-- Nondeterministic programs from `α` to `β`: Mathlib's relations `SetRel α β`. -/
scoped infixr:25 " -|> " => SetRel

open scoped SetRel

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The outputs of `a` along `R`, as a runner for `acceptsSome` and its siblings. -/
def outcomes (R : α -|> β) : α → Set β := fun a => {b | (a, b) ∈ R}

/-- Existential pullback: inputs with some output in `L`. -/
abbrev pullSome (R : α -|> β) (L : Set β) : Set α := R.preimage L

/-- Universal pullback: inputs all of whose outputs are in `L` (vacuous with no output). -/
abbrev pullAll (R : α -|> β) (L : Set β) : Set α := R.core L

/-- The relation of a partial function: `a` relates to `b` iff `f a = some b`. -/
def ofPartial (f : α → Option β) : α -|> β := {p | f p.1 = some p.2}

/-- The relation of a total map (Mathlib's `Function.graph`). -/
abbrev ofTotal (f : α → β) : α -|> β := Function.graph f

/-- Kleisli composition of partial functions: run `f`, then `g` on its output. -/
def partialComp (f : α → Option β) (g : β → Option γ) : α → Option γ := fun a => (f a).bind g

/-- The domain of a partial function: inputs with an output. -/
def pdom (f : α → Option β) : Set α := {a | (f a).isSome}

/-! ## Indexed value sets -/

/-- One language per index. -/
abbrev IndexedLang {ι : Type u} (A : ι → Type v) : Type (max u v) := ∀ i, Set (A i)

/-- Erase the index into dependent pairs: `⟨i, a⟩ ∈ eraseSigma L ↔ a ∈ L i`. -/
def eraseSigma {ι : Type u} {A : ι → Type v} (L : IndexedLang A) : Set (Σ i, A i) :=
  Set.univ.sigma L

/-- Recover the per-index languages of a set of dependent pairs. -/
def fiberLang {ι : Type u} {A : ι → Type v} (M : Set (Σ i, A i)) : IndexedLang A :=
  fun i => {a | ⟨i, a⟩ ∈ M}

/-- Erase the index over a common carrier, existentially: accepted at some index. -/
def eraseSome {ι : Type u} (L : ι → Set α) : Set α := ⋃ i, L i

/-- Erase the index over a common carrier, universally: accepted at every index. -/
def eraseAll {ι : Type u} (L : ι → Set α) : Set α := ⋂ i, L i

end Silmaril.Accept
