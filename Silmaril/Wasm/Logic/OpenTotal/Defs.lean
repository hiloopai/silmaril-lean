module

public import Silmaril.Wasm.Logic.Open.Defs
public import Silmaril.Wasm.Logic.Total.Defs
public import Silmaril.Games.DivLTS.Defs

/-!
# Open Wasm modules with total correctness: divergence-aware games

The partial-correctness game link (`Silmaril.Wasm.Logic.Open`) relates a module's
strategy of *finite* plays to assume/guarantee specifications. Here a module
that meets its export specifications **totally** is related to a
divergence-observing strategy (`Silmaril.Games.DStrategy`,
`Silmaril.Games.Div`/`DivLTS`):

* `specHostT bind Γi`: the most general **terminating** environment meeting the
  import context `Γi` (as `Open.specHost`, but a stub call never diverges);
* `TModuleSat P M bind Γi Γe`: the specifications of `Γe` are about `M`'s
  functions and are **totally** correct (`Hoare.TCtx.Valid`) under
  `specHostT bind Γi`;
* `dmodStrat P M bind`: the divergence-observing strategy of the module's
  reduction semantics `Open.modRed` (`DStrategy.ofReduction`): its divergent
  plays are those after which the module may compute forever without a visible
  move;
* `OppGood I S p`: every Opponent move of `p` meets the specifications;
* `dagStrat I S`: the assume/guarantee strategy `Strategy.agStrat I S` read with
  divergence: it may diverge only after a play in which Opponent broke the
  specifications, and it has every infinite play whose prefixes are plays.

`Silmaril.Wasm.Logic.OpenTotal.Thms` proves `TModuleSat → dmodStrat ≤ dagStrat`:
total correctness rules out divergence after any play in which the environment
behaved.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.OpenTotal

open Silmaril.Games
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Ctx FSpec TCtx.Valid)
open Silmaril.Wasm.Logic.Open (OMod modRed)
open Silmaril.Wasm.Logic.Strategy (WCall resultOutcome ISpec MoveGood agStrat)

variable {H : Type}

/-- **The most general terminating environment** meeting an import context: a
stub call meeting its precondition returns something meeting its postcondition;
it never diverges. -/
def specHostT (bind : H → Nat) (Γi : Ctx H) : HostSemantics H := fun h s args o =>
  ∃ S, Γi (bind h) = some S ∧ S.pre s args ∧
    match o with
    | .returned s' r => S.post s args s' (resultOutcome r)
    | .diverged => False

/-- **An open module meets its export specifications totally** under its import
specifications. -/
def TModuleSat (P : Profile) (M : OMod H) (bind : H → Nat) (Γi Γe : Ctx H) : Prop :=
  (∀ a S, Γe a = some S → (M.funcs a).isSome ∧ ∀ s args, S.pre s args → M.Has s) ∧
    TCtx.Valid P (specHostT bind Γi) Γe

/-- **The divergence-observing strategy of an open module.** -/
def dmodStrat (P : Profile) (M : OMod H) (bind : H → Nat) : DStrategy (WCall H) (WCall H) :=
  DStrategy.ofReduction (modRed P M bind)

universe u

variable {E F : Sig.{u}}

/-- Every Opponent move of the play meets the specifications. -/
def OppGood (I : ISpec E) (S : ISpec F) (p : List (Move E F)) : Prop :=
  ∀ m ∈ p, Move.IsO m → MoveGood I S m

/-- **The divergence-aware assume/guarantee strategy**: the plays of
`agStrat I S`, divergence only after a play in which Opponent broke the
specifications, and every infinite play whose prefixes are plays. -/
def dagStrat (I : ISpec E) (S : ISpec F) : DStrategy E F where
  toStrategy := agStrat I S
  div := {p | p ∈ agStrat I S ∧ (∃ q, Path .idle p (.run q)) ∧ ¬ OppGood I S p}
  inf := {J | IsInfPlay J ∧ J ⊆ (agStrat I S).plays}
  div_mem h := h.1
  div_run h := h.2.1
  inf_isInf h := h.1
  inf_sub h := h.2

/-- The number of moves of a play at the upper interface. -/
def ucount (t : List (Move E F)) : Nat := (upper t).length

/-- **Productivity**: in every infinite play of `δ` whose prefixes have good
Opponent moves, there are infinitely many moves at the upper interface (`δ` does
not chatter forever with its environment below within one question). -/
def Productive (I : ISpec E) (S : ISpec F) (δ : DStrategy E F) : Prop :=
  ∀ J ∈ δ.inf, (∀ t ∈ J, OppGood I S t) → ∀ k, ∃ t ∈ J, k ≤ ucount t

end Silmaril.Wasm.Logic.OpenTotal
