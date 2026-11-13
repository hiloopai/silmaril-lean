module

public import Silmaril.Wasm.Component.Streams.Live.Defs
public import Silmaril.Wasm.Component.Streams.Pipes.Defs
public import Silmaril.Wasm.Component.Algebra.Pipe.Defs

/-!
# The observable behaviour of stream networks, and the link to the component algebra

* `Outcomes net obs a`: some maximal execution of `net` (under some scheduler) reaches a system
  where every node has finished, and `obs` of it is `a`. `pipeOut xs T`, `chainOut xs T U` and
  `teeOut xs T U` observe the sinks of `Pipes.pipe`, `Pipes.chain` and `Pipes.teeNet`.
* `NetEquiv T U`: the transformer components `T` and `U` are **observationally equivalent as
  network nodes**: in a pipe, every input gives them the same outcomes.
* `VSem C`: a compositional semantics of transformers on component values as strategies of the
  component algebra (`den_comp`, `den_congr`), on a stream interface of `width` functions; and
  `VSem.Realizes V c T`: the component `c` has that interface and the strategy `V.den T`.
  `VSem.ofStreamSem` reads every `Algebra.StreamSem` as one; the concrete stream game of the
  algebra track (`Algebra.StreamGame.den`, width `1`, with `den_comp` and `den_congr`) has
  exactly these fields, so it is one too.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.NetSem

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Live
open Silmaril.Wasm.Component.Streams.Pipes

/-- **The outcomes of a network**: observations of the finished systems that maximal executions
reach. -/
def Outcomes {α : Type} (net : Network) (obs : Sys net → α) (a : α) : Prop :=
  ∃ r, Exec net r ∧ ∃ n, (r n).AllDone ∧ obs (r n) = a

variable {σ τ : Type}

/-- What the sink of a pipe holds at the end. -/
def pipeOut (xs : List Val) (T : Tr σ Val Val) : List Val → Prop :=
  Outcomes (pipe xs T) fun s => (s.ns 2).got

/-- What the sink of a chain holds at the end. -/
def chainOut (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) : List Val → Prop :=
  Outcomes (chain xs T U) fun s => (s.ns 3).got

/-- What the two sinks of a tee network hold at the end. -/
def teeOut (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) : List Val × List Val → Prop :=
  Outcomes (teeNet xs T U) fun s => ((s.ns 4).got, (s.ns 5).got)

/-- **Observational equivalence of transformer components** in networks. -/
def NetEquiv (T : Tr σ Val Val) (U : Tr τ Val Val) : Prop := ∀ xs, pipeOut xs T = pipeOut xs U

/-- A compositional semantics of transformers on component values, in the component algebra. -/
structure VSem {M : Type} [CoreModule M] (C : CoreSem M) where
  width : Nat
  den : {σ : Type} → Tr σ Val Val → Strategy sigU sigU
  den_comp : ∀ {σ τ : Type} (T : Tr σ Val Val) (U : Tr τ Val Val),
    den (T.comp U) = (den T).comp (den U)
  den_congr : ∀ {σ τ : Type} {T : Tr σ Val Val} {U : Tr τ Val Val}, T.Equiv U → den T = den U

namespace VSem

variable {M : Type} [CoreModule M] {C : CoreSem M}

/-- Every `Algebra.StreamSem`, on component values. -/
def ofStreamSem (S : Algebra.StreamSem C) : VSem C where
  width := S.width
  den T := S.den T
  den_comp T U := S.den_comp T U
  den_congr h := S.den_congr h

/-- The component `c` realises `T`. -/
def Realizes (V : VSem C) (c : Comp M) (T : Tr σ Val Val) : Prop :=
  c.imports.length = V.width ∧ c.exports.length = V.width ∧ c.denU C = V.den T

end VSem

end Silmaril.Wasm.Component.Streams.NetSem
