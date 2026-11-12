module

public import Silmaril.Wasm.Logic.Hoare.Defs
public import Silmaril.Wasm.Spec.Multi.Defs

@[expose] public section

/-!
# Verified Wasm examples: shared definitions

Generic pieces for proving safety properties of **sessions** (sequences of export calls on one
instance, `Silmaril.Wasm.Spec.Multi.Session`, the store persisting between calls) from every-run
Hoare specifications (`Silmaril.Wasm.Logic.Hoare`) of the exports, at every profile:

* an abstract state `σ` with a representation relation `R : σ → Store Nat → Prop`, a transition
  `next : σ → Call I → σ` per answered export call and a per-call safety property
  `Good : σ → Call I → Prop`;
* `callSpec I R next Good f`: the function specification of export call `f` (export index and
  typed arguments): from a store representing `a`, every outcome that is a result with answer
  `w` satisfies `Good a ⟨f, w⟩` and leaves a store representing `next a ⟨f, w⟩`;
* `bodyPost n post`: the postcondition of a function body that returns `n` results or traps,
  as the function specification's `post` allows (no branch out, no exception, no tail call);
* `AllGood next Good a l`: every call of the list `l` is `Good` in the state reached by the
  calls before it.

`Silmaril.Wasm.Examples.Common.Thms` proves `session_allGood`: valid call specifications give
`AllGood` for every session. Used by the Farkas checker (`Silmaril.Wasm.Examples.Farkas`).
A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.Common

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.Logic.Hoare (FSpec)
open Silmaril.Wasm.Spec.Multi (Call)

/-- The Core result an outcome stands for (values, a trap or an exception). -/
def outcomeResult? : Outcome → Option Result
  | .normal vs => some (.values vs)
  | .trap => some .trap
  | .throw a => some (.throw a)
  | _ => none

/-- The postcondition of a body that ends with `n` results or a trap allowed by `post`. -/
def bodyPost {H : Type} (n : Nat) (post : Store H → Outcome → Prop) :
    Silmaril.Wasm.Logic.Core.Post H := fun s _ o =>
  match o with
  | .normal res => res.length = n ∧ post s (.normal res)
  | .trap => post s .trap
  | _ => False

variable {σ : Type}

/-- **The specification of export call `f`** relative to the abstract state: the arguments are
those of `f`, the store represents some state, and every result answered as `w` is `Good` and
leaves a store representing the next state. -/
def callSpec (I : ScalarInstance) (R : σ → Store Nat → Prop) (next : σ → Call I → σ)
    (Good : σ → Call I → Prop) (f : I.F.Op) : FSpec Nat where
  pre s args := args = f.2.1 ∧ ∃ a, R a s
  post s _ s' o := ∀ a, R a s → ∀ r, outcomeResult? o = some r →
    ∀ w, Answer.ofResult? (I.exports.get f.1) r = some w → Good a ⟨f, w⟩ ∧ R (next a ⟨f, w⟩) s'

/-- The state after a list of calls. -/
def after {I : ScalarInstance} (next : σ → Call I → σ) (a : σ) (l : List (Call I)) : σ :=
  l.foldl next a

/-- Every call of a list is `Good` in the state reached by the calls before it. -/
def AllGood {I : ScalarInstance} (next : σ → Call I → σ) (Good : σ → Call I → Prop) :
    σ → List (Call I) → Prop
  | _, [] => True
  | a, c :: l => Good a c ∧ AllGood next Good (next a c) l

end Silmaril.Wasm.Examples.Common
