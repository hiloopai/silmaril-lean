module

public import Silmaril.Wasm.Logic.OpenTotal.Defs
public import Silmaril.Wasm.Game.Strategy.Defs

/-!
# The program logic and the Wasm game semantics: specifications

`Silmaril.Wasm.Logic.Open` relates the every-run logic to the strategy of an
*open-module model* (`Open.modStrat`, store passed with every move, imports
resolved by `bind`). This topic relates it to the module strategies of
`Silmaril.Wasm.Game` instead: `I.strategy P s : Strategy I.E I.F` of a
`ScalarInstance` (store hidden and persisting across export calls, host
function `.host k` being import `k`, every profile `P`), its
divergence-observing version `I.dstrategy P s`, and through M3 the strategy
of a statically linked module.

## The fragment

Exactly the fragment of `Silmaril.Wasm.Game`: a Core 3.0 module instance
(`ScalarInstance`) whose imports and exports are functions with
store-independent (scalar) parameter and result types (numbers, `v128`,
`(ref null? i31)`); the environment answers an import call with values, a
trap or an exception address and **does not write the store**; host calls are
atomic (no re-entrancy during an import call). Interface specifications
therefore talk about values only: an import specification `Ii : ISpec I.E`
and an export specification `Ie : ISpec I.F` (`Silmaril.Wasm.Logic.Strategy`) are
predicates on typed calls and their `Answer`s. What the module keeps in its
store between export calls is described by a **store invariant** `Inv`.

## Definitions

* `importSpec I Ii k`: the Hoare specification of import `k` (host code
  `.host k`): a call is allowed when its arguments form an import question
  `e` (`I.importOp? k args = some e`) with `Ii.pre e`; it returns in the same
  store with the outcome of an answer `v` with `Ii.post e v`. `importCtx I Ii`
  collects them, indexed by the host code.
* `gameHost I Ii = Open.specHost id (importCtx I Ii)`: the most general
  environment of the game meeting `Ii`, as a silmaril-lean host relation
  (it may also diverge); `gameHostT I Ii` is the terminating one
  (`OpenTotal.specHostT`).
* `exportSpec I Inv Ie j`: the Hoare specification of export `j` at its
  address `I.addr j`: from a store meeting `Inv`, on typed arguments forming a
  question allowed by `Ie.pre`, every outcome is that of an answer allowed by
  `Ie.post`, in a store meeting `Inv` again.
* `GameSat P I Inv Ii Ie` (partial correctness) and `TGameSat P I Inv Ii Ie`
  (total correctness): every export meets `exportSpec` in the every-run logic
  (`Hoare.FSpecValid`, resp. `Hoare.TFSpecAt`) under `gameHost`, resp.
  `gameHostT`. These are the module-level specifications "import spec ⇒
  export spec" proved in the logic; import calls are proved with the stub
  rules `Open.FSpecAt.stub`/`OpenTotal.TFSpecAt.stub` (the import stubs of
  the instance are the host functions of its store).

The theorems are in `Silmaril.Wasm.Logic.GameLink.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.GameLink

open Silmaril.Games Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Ctx FSpec FSpecValid TFSpecAt)
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)

section

variable (I : ScalarInstance)

/-- The Hoare specification of import `k` of the instance for the import specification
`Ii`: the arguments form an allowed import question; the store is unchanged and the outcome
is that of an allowed answer. -/
def importSpec (Ii : ISpec I.E) (k : Nat) : FSpec Nat where
  pre _ args := ∃ e, I.importOp? k args = some e ∧ Ii.pre e
  post s args s' o := s' = s ∧ ∀ e, I.importOp? k args = some e →
    ∃ v : I.E.Ar e, Ii.post e v ∧ resultOutcome (Answer.toResult (ft := I.imports.get e.1) v) = o

/-- The import specifications, indexed by host code (`.host k` is import `k`). -/
def importCtx (Ii : ISpec I.E) : Ctx Nat := fun k => some (importSpec I Ii k)

/-- **The most general environment of the game** meeting `Ii`, as a host relation: an
allowed import call returns an allowed answer in the same store, or diverges. -/
def gameHost (Ii : ISpec I.E) : HostSemantics Nat := Open.specHost id (importCtx I Ii)

/-- The most general **terminating** environment of the game meeting `Ii`. -/
def gameHostT (Ii : ISpec I.E) : HostSemantics Nat := OpenTotal.specHostT id (importCtx I Ii)

/-- The Hoare specification of export `j` for the store invariant `Inv` and the export
specification `Ie`. -/
def exportSpec (Inv : Store Nat → Prop) (Ie : ISpec I.F) (j : Fin I.exports.length) :
    FSpec Nat where
  pre s args := Inv s ∧
    ∃ ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args, Ie.pre ⟨j, ⟨args, ht⟩⟩
  post _ args s' o := Inv s' ∧
    ∀ (ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args)
      (v : Answer (I.exports.get j)), resultOutcome v.toResult = o → Ie.post ⟨j, ⟨args, ht⟩⟩ v

end

/-- **The instance meets `Ie` under `Ii`** with store invariant `Inv` (partial
correctness): every export meets its specification in the every-run logic under the most
general environment of the game. -/
def GameSat (P : Profile) (I : ScalarInstance) (Inv : Store Nat → Prop) (Ii : ISpec I.E) (Ie : ISpec I.F) : Prop :=
  ∀ j, FSpecValid P (gameHost I Ii) (I.addr j) (exportSpec I Inv Ie j)

/-- **The instance meets `Ie` under `Ii` totally** with store invariant `Inv`: every export
meets its specification with total correctness under the most general terminating
environment of the game. -/
def TGameSat (P : Profile) (I : ScalarInstance) (Inv : Store Nat → Prop) (Ii : ISpec I.E) (Ie : ISpec I.F) : Prop :=
  ∀ j, TFSpecAt P (gameHostT I Ii) (I.addr j) (exportSpec I Inv Ie j)

end Silmaril.Wasm.Logic.GameLink
