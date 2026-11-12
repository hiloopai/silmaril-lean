module

public import Init

/-!
# Stream transformers: the specification layer

A **stream transformer** `Tr σ α β` is a Mealy machine with an end-of-stream flush and an early
stop: a state space `σ`, an initial state `init`, a step `step : σ → α → σ × List β` that consumes
one input item and emits a (possibly empty) batch of output items, a `flush` that emits the
remaining output when the input ends, and a predicate `done` on states after which the
transformer reads no more input (for `take`, and generally for a component that drops its
readable end early).

This is the functional specification that the component-level transformers of
`Silmaril.Wasm.Component.Streams.Proc` implement over the Component Model stream built-ins
(`Silmaril.Wasm.Component.Async`). Its meaning on a finite input `xs`:

* `T.runP xs`: the output emitted **so far**, after the items `xs` and before the end of the
  input is known (a prefix of the output of every extension of `xs`: `runP_mono`);
* `T.run xs`: the whole output when the input ends after `xs` (the flush appended);
* `T.used s xs`: how many items of `xs` the transformer reads (it stops at `done`).

On an infinite input the output is the limit of the `runP` of its prefixes, which are
monotone (`runP_mono`); we work with the finite approximations throughout (the usual Kahn
semantics of a deterministic stream process), so no coinductive type is needed for the
statements.

## Transformers

`id`, `map f`, `filter p`, `filterMap f`, `flatMap f`, `take n`, `tee` (one input, both outputs
tagged `false`/`true` in order) and sequential composition `T.comp U` (the outputs of `T` are
the inputs of `U`; written `T ⟫ U`).

## Equivalence

`T ≈ U` (`Tr.Equiv`): the same output so far after every finite input and the same whole
output at the end of every finite input. This is the observational equivalence of transformers
as stream functions (it does not compare how much input they read; `used` does). The final-output
equivalence `Tr.EquivF` compares `run` only.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams

/-- **A stream transformer** with state space `σ`: a Mealy machine with a flush at the end of
the input and an early stop. -/
structure Tr (σ α β : Type) where
  /-- The initial state. -/
  init : σ
  /-- Consume one item and emit a batch of outputs. -/
  step : σ → α → σ × List β
  /-- The outputs emitted when the input ends. -/
  flush : σ → List β := fun _ => []
  /-- After a `done` state the transformer reads no more input. -/
  done : σ → Bool := fun _ => false

namespace Tr

variable {σ τ ρ α β γ δ : Type}

/-- Feed a list of items from a state: the final state and the outputs (items after a `done`
state are not read). -/
def feed (T : Tr σ α β) : σ → List α → σ × List β
  | s, [] => (s, [])
  | s, x :: xs =>
    if T.done s then (s, [])
    else
      let p := T.step s x
      let q := T.feed p.1 xs
      (q.1, p.2 ++ q.2)

/-- The output emitted so far after the input `xs` (end of input not yet known). -/
def runP (T : Tr σ α β) (xs : List α) : List β := (T.feed T.init xs).2

/-- The whole output when the input is exactly `xs`. -/
def run (T : Tr σ α β) (xs : List α) : List β :=
  let p := T.feed T.init xs
  p.2 ++ T.flush p.1

/-- How many items of `xs` the transformer reads from `s`. -/
def used (T : Tr σ α β) : σ → List α → Nat
  | _, [] => 0
  | s, x :: xs => if T.done s then 0 else T.used (T.step s x).1 xs + 1

/-- **Sequential composition**: the outputs of `T` are fed to `U`. It stops reading when either
part is done; at the end of the input, `T`'s flush is fed to `U`, then `U` flushes. -/
def comp (T : Tr σ α β) (U : Tr τ β γ) : Tr (σ × τ) α γ where
  init := (T.init, U.init)
  step s x :=
    let p := T.step s.1 x
    let q := U.feed s.2 p.2
    ((p.1, q.1), q.2)
  flush s :=
    let q := U.feed s.2 (T.flush s.1)
    q.2 ++ U.flush q.1
  done s := T.done s.1 || U.done s.2

@[inherit_doc] scoped infixl:60 " ⟫ " => Tr.comp

/-- The identity transformer. -/
def id : Tr Unit α α where
  init := ()
  step _ x := ((), [x])

/-- Apply `f` to every item. -/
def map (f : α → β) : Tr Unit α β where
  init := ()
  step _ x := ((), [f x])

/-- Keep the items satisfying `p`. -/
def filter (p : α → Bool) : Tr Unit α α where
  init := ()
  step _ x := ((), if p x then [x] else [])

/-- Map and filter in one: keep `y` for every item with `f x = some y`. -/
def filterMap (f : α → Option β) : Tr Unit α β where
  init := ()
  step _ x := ((), (f x).toList)

/-- Replace every item by a list of items. -/
def flatMap (f : α → List β) : Tr Unit α β where
  init := ()
  step _ x := ((), f x)

/-- The first `n` items; reads exactly `min n |xs|` items. -/
def take (n : Nat) : Tr Nat α α where
  init := n
  step k x := (k - 1, [x])
  done k := k == 0

/-- **Tee**: every item goes to both outputs, the output tagged `false` first. -/
def tee : Tr Unit α (Bool × α) where
  init := ()
  step _ x := ((), [(false, x), (true, x)])

/-- The items of one output of a tagged stream. -/
def chan (b : Bool) (ys : List (Bool × β)) : List β :=
  ys.filterMap fun p => if p.1 = b then some p.2 else none

/-- **Observational equivalence** of transformers (of any state spaces): the same output so far
after every finite input, and the same whole output at its end. -/
def Equiv (T : Tr σ α β) (U : Tr τ α β) : Prop :=
  ∀ xs, T.runP xs = U.runP xs ∧ T.run xs = U.run xs

@[inherit_doc] scoped infix:50 " ≈ₜ " => Tr.Equiv

/-- Equivalence of the whole outputs only. -/
def EquivF (T : Tr σ α β) (U : Tr τ α β) : Prop := ∀ xs, T.run xs = U.run xs

end Tr

end Silmaril.Wasm.Component.Streams
