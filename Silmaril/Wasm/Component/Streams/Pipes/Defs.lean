module

public import Silmaril.Wasm.Component.Streams.Net.Defs

/-!
# Pipelines, chains and tees as networks

Concrete networks of `Silmaril.Wasm.Component.Streams.Net` (drop-faithful stream built-ins):

* `pipe xs T`: a source of `xs` → a transformer component `T` → a sink;
* `chain xs T U`: a source → `T` → `U` → a sink: **two separate transformer components**, each
  with its own input and output streams;
* `teeNet xs T U`: a source → a **tee** component with two output streams (the node `Tr.id` with
  two outputs) → `T` → a sink, and → `U` → another sink. A branch may stop early (e.g. `T` a
  `take`): the tee's write on that branch then reports `DROPPED` and it keeps serving the other.

Streams are numbered from `0` (handles `2c+1`, `2c+2`), nodes from `0`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Pipes

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Net

variable {σ τ : Type}

/-- A source of `xs` writing to stream `c`. -/
def src (xs : List Val) (c : Nat) : Node := ⟨Unit, Tr.source xs, none, [c]⟩

/-- A transformer component reading stream `a` and writing stream `b`. -/
def stage (T : Tr σ Val Val) (a b : Nat) : Node := ⟨σ, T, some a, [b]⟩

/-- A sink reading stream `a`. -/
def sink (a : Nat) : Node := ⟨Unit, Tr.id, some a, []⟩

/-- A tee reading stream `a` and writing streams `b` and `c`. -/
def tee (a b c : Nat) : Node := ⟨Unit, Tr.id, some a, [b, c]⟩

/-- **Source → `T` → sink.** Streams: `0` (source to `T`), `1` (`T` to sink). -/
abbrev pipe (xs : List Val) (T : Tr σ Val Val) : Network where
  k := 3
  node i := if i.val = 0 then src xs 0 else if i.val = 1 then stage T 0 1 else sink 1
  m := 2
  wr c := if c = 0 then (0, 0) else (1, 0)
  rd c := if c = 0 then 1 else 2

/-- **Source → `T` → `U` → sink**, with `T` and `U` separate components. Streams `0`, `1`, `2`. -/
abbrev chain (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) : Network where
  k := 4
  node i := if i.val = 0 then src xs 0 else if i.val = 1 then stage T 0 1
    else if i.val = 2 then stage U 1 2 else sink 2
  m := 3
  wr c := if c = 0 then (0, 0) else if c = 1 then (1, 0) else (2, 0)
  rd c := if c = 0 then 1 else if c = 1 then 2 else 3

/-- **Source → tee → (`T` → sink₁, `U` → sink₂).** Streams: `0` (source to tee), `1` and `2`
(the tee's outputs), `3` (`T` to sink₁), `4` (`U` to sink₂). Nodes: source `0`, tee `1`, `T` `2`,
`U` `3`, sink₁ `4`, sink₂ `5`. -/
abbrev teeNet (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) : Network where
  k := 6
  node i := if i.val = 0 then src xs 0 else if i.val = 1 then tee 0 1 2
    else if i.val = 2 then stage T 1 3 else if i.val = 3 then stage U 2 4
    else if i.val = 4 then sink 3 else sink 4
  m := 5
  wr c := if c = 0 then (0, 0) else if c = 1 then (1, 0) else if c = 2 then (1, 1)
    else if c = 3 then (2, 0) else (3, 0)
  rd c := if c = 0 then 1 else if c = 1 then 2 else if c = 2 then 3 else if c = 3 then 4 else 5

/-- **Liveness** (proved: `pipe_live` in `Silmaril.Wasm.Component.Streams.Live.Thms`): from every reachable system of a pipe, some sequence of steps reaches a
system where the sink has dropped its input (and so, by `pipe_correct`, holds `T.run xs`). Only
safety and correctness at the end are proved; every run of the tests finished. -/
def PipeLive : Prop :=
  ∀ {σ : Type} (xs : List Val) (T : Tr σ Val Val) (s : Sys (pipe xs T)), Reach (pipe xs T) s →
    ∃ s', Steps (pipe xs T) s s' ∧ ∃ b, (s'.ns 2).rd = .gone b

end Silmaril.Wasm.Component.Streams.Pipes
