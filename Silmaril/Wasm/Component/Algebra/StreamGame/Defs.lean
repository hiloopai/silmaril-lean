module

public import Silmaril.Wasm.Component.Algebra.Kahn.Defs
public import Silmaril.Wasm.Component.Algebra.Pipe.Defs

/-!
# A concrete game semantics of stream transformers

The pull game of `Silmaril.Wasm.Component.Algebra.Kahn` gives every stream transformer
`T : Tr σ Val Val` (`Silmaril.Wasm.Component.Streams.Spec`) a strategy over `sigU`:

* `item v = some (.vals [v])` is the answer carrying one item (a `stream.write [v]` meeting a
  `stream.read`: `COMPLETED`, count 1), `ofItem` reads it back; **every other answer** ends the
  current stream (`stream.drop-writable`, `DROPPED`; a trap `none` included) and is passed on
  verbatim;
* `react T s a`: on an item, `T` is fed it (`T.feed s [v]`, which reads nothing after `done`);
  on an end, `T` emits its flush, passes the end on, and **starts again** from `T.init` (the
  next question opens a new stream);
* `ans T h`: the answers `T` produces after receiving `h` from upstream;
* **`den T = kahn (ans T)`**: the Kahn strategy of that stream function.

`Realizes C c T`: the component `c` has one import and one export and the strategy `den T`.

`Silmaril.Wasm.Component.Algebra.StreamGame.Thms` proves the three conditions of
`Algebra.StreamSem` for `den` (`den_comp`, `den_congr`, `den_id`: the identity is copycat) and
derives unconditionally the transformer laws that `Algebra.Pipe.Thms` states for a hypothetical
`StreamSem`.

## Differences from `Algebra.StreamSem`

`StreamSem.den` takes transformers between **arbitrary** item types; `den` here takes
transformers on component values `Val`, the items a stream carries in the IR (`Streams.Proc`
uses the same `Tr σ Val Val`). Typed transformers are read on `Val` through an encoding. This is
forced: no `StreamSem` distinguishes all inequivalent transformers
(`StreamSem.not_faithful`, by Cantor's theorem).

`done` (an early stop, as in `take`) is honoured on outputs but not observed on the game: a
transformer that is `done` still answers pulls by pulling (and discarding) until the stream
ends. `Tr.Equiv` does not compare how much input is read, and `den_congr` requires equivalent
transformers to have equal strategies, so a semantics satisfying `den_congr` cannot observe the
early drop of a readable end.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra.StreamGame

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Algebra.Kahn

variable {σ : Type}

/-- The answer carrying one item. -/
def item (v : Val) : Ans := some (.vals [v])

/-- Read an answer as one item; every other answer ends the stream. -/
def ofItem : Ans → Option Val
  | some (.vals [v]) => some v
  | _ => none

/-- How `T` reacts to one answer from upstream: its new state and the answers it produces. -/
def react (T : Tr σ Val Val) (s : σ) (a : Ans) : σ × List Ans :=
  match ofItem a with
  | some v => ((T.feed s [v]).1, (T.feed s [v]).2.map item)
  | none => (T.init, (T.flush s).map item ++ [a])

/-- React to a list of answers. -/
def feedA (T : Tr σ Val Val) : σ → List Ans → σ × List Ans
  | s, [] => (s, [])
  | s, a :: h => ((feedA T (react T s a).1 h).1, (react T s a).2 ++ (feedA T (react T s a).1 h).2)

/-- **The stream function of `T`** on answers. -/
def ans (T : Tr σ Val Val) (h : List Ans) : List Ans := (feedA T T.init h).2

/-- **The strategy of a stream transformer.** -/
def den (T : Tr σ Val Val) : Strategy sigU sigU := kahn (ans T)

variable {M : Type} [CoreModule M]

/-- The component `c` **realises** the transformer `T` in the stream game. -/
def Realizes (C : CoreSem M) (c : Comp M) (T : Tr σ Val Val) : Prop :=
  c.imports.length = 1 ∧ c.exports.length = 1 ∧ c.denU C = den T

end Silmaril.Wasm.Component.Algebra.StreamGame
