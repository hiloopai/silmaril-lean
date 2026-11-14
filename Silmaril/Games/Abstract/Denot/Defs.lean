module

public import Silmaril.Games.Abstract.Game.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.WithTop
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal

/-!
# Partial denotations: orientation of "undefined"

A semantics of programs `α` (byte strings, say) into trace models of `G` may be
partial: some programs get no behaviour from this model (an unsupported
feature, an input outside the modelled fragment). Two readings, both complete
lattices pointwise:

* **`WithTop`** (`Denot α G := α → WithTop (TraceModel G)`). An undefined
  program is `⊤`, which means *no claim*, strictly above every defined model,
  including the chaotic model `⊤ : TraceModel G` that allows every legal play.
  The order is pointwise: `d ≤ e` iff `e` is undefined wherever `d` is, and,
  where both are defined, `e` allows at least the plays of `d`. So `e` is less
  defined or larger, and refinement goes downwards. An implementation `d`
  refines a specification `e` when `d ≤ e`, which holds trivially at
  programs the specification leaves undefined. Making a partial semantics
  more defined moves it *down*.
* **Lower sets** (`LowerSet (TraceModel G)`). A program denotes the set of
  trace models it may have, closed under refinement (the Hoare-style
  powerdomain of models). A defined model `T` is read as `Iic T`, and
  undefined as `⊤ = univ`. This reading identifies "undefined" with the
  chaotic model, since `Iic ⊤ = univ`. `toLower` maps the first reading onto
  the second, monotonically. It is injective on defined values and collapses
  exactly undefined with chaos (`Silmaril.Games.Abstract.Denot.Thms`).

**Undefined is not invalid.** Bytes that fail to decode or validate have a
*defined* behaviour: rejection at startup. In the phased game
(`Silmaril.Games.Abstract.Startup`), that is the model where startup fails.
Only programs outside the modelled fragment are `⊤`.

**Realizable against abstract behaviours.** `realizable d` is the set of models
some program actually denotes. Abstract results about `TraceModel G` (the
lattice, linking, contexts) range over all models, realizable or not.
Definability hypotheses (`Silmaril.Games.Abstract.Testing`) are where the
difference matters.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u v

/-- A partial denotation: programs to trace models, `⊤` for "no claim". -/
abbrev Denot (α : Type v) (G : Game.{u}) : Type (max u v) := α → WithTop (TraceModel G)

namespace Denot

variable {α : Type v} {G : Game.{u}}

/-- A partial map, undefined read as `⊤`. -/
def ofPartial (f : α → Option (TraceModel G)) : Denot α G := fun a =>
  match f a with
  | none => ⊤
  | some T => (T : WithTop (TraceModel G))

/-- The lower-set reading of a possibly undefined model: a defined model is the
set of its refinements, undefined is every model. -/
def toLower : WithTop (TraceModel G) → LowerSet (TraceModel G)
  | ⊤ => ⊤
  | (T : TraceModel G) => LowerSet.Iic T

/-- The models some program denotes. -/
def realizable (d : Denot α G) : Set (TraceModel G) := {T | ∃ a, d a = (T : WithTop _)}

end Denot

end Silmaril.Games.Abstract
