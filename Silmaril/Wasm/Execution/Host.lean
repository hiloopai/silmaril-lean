module

/-!
# The host interface, defined once

Every WebAssembly semantics in this development is parameterised by an
*embedder*: a type `H` of host functions together with a relation saying what a
call to one of them may do. V1 and Lime1 share `Execution.Runtime.HostSemantics`,
Core 3.0 has `Execution.Core.HostSemantics` and Wasm 2.0 has
`V2.Execution.HostSemantics`. All three had the *same two declarations* written
out over their own store, value and result types:

* an outcome type `returned (store) (result) | diverged` — divergence is an
  alternative of the host outcome, not of the result, because a host call is a
  single step of the Wasm machine and the machine's own `Diverges` predicate
  cannot see inside it; and
* the relation `H → Store → List Val → HostOutcome → Prop`, a *relation* rather
  than a function because a host function may be non-deterministic.

This module gives those two, once, as `Host.Outcome` and `Host.Semantics`,
parameterised by the store, value and result types. The three existing names are
now reducible abbreviations for them, so every pre-existing statement keeps its
type.

## The simulation kit

The subset theorems (Lime1 → Core 3.0, Wasm 2.0 → Core 3.0, Lime1 → Wasm 2.0)
each carried their own copy of the same three definitions relating a source host
to a target host: *outcomes correspond*, *host calls preserve a store
invariant*, and *every source host behaviour is matched by the target host on a
related store*. `Host.Outcome.Sim`, `Host.Preserves` and `Host.Compatible` are
those three, parameterised by the store relation, the value translation and the
result translation; the three `HostOutcomeSim` / `HostPreserves` /
`HostCompatible` triples are now wrappers around them.

`Host.Compatible` is deliberately *asymmetric*: the target is allowed to do more
than the source (a Core 3.0 host may allocate tags, structs or exceptions that
the 2.0 store cannot represent) but every source behaviour must be matched. That
is the direction the forward-simulation proofs consume.

## What is **not** here

Store well-formedness, store extension and the typing contract on host results
stay with each semantics: they talk about the fields of that semantics' store
and about its typing judgement, and there is nothing to share. They enter the
generic definitions as the `pre`, `post` and `store` parameters.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Host

universe u v w x y z t

/-- The outcome of a host call: a new store together with a result, or
divergence. `S` is the semantics' store type and `R` its result type. -/
inductive Outcome (S : Type u) (R : Type v) where
  /-- The call returned, leaving the store in state `store`. -/
  | returned (store : S) (result : R)
  /-- The call did not terminate. -/
  | diverged

/-- The embedder's host semantics: a relation between a host function, the store
it is called in, its arguments and its outcome. A relation, not a function,
because host functions may be non-deterministic and may diverge. -/
abbrev Semantics (H : Type u) (S : Type v) (V : Type w) (R : Type x) :=
  H → S → List V → Outcome S R → Prop

/-- Lift a relation `store` on stores and a translation `result` on results to
host outcomes: divergence corresponds to divergence, and a return corresponds to
a return on a related store with the translated result. -/
def Outcome.Sim {S : Type u} {R : Type v} {S' : Type w} {R' : Type x}
    (store : S → S' → Prop) (result : R → R') : Outcome S R → Outcome S' R' → Prop
  | .diverged, .diverged => True
  | .returned s r, .returned s' r' => store s s' ∧ r' = result r
  | _, _ => False

/-! ### Reduction lemmas for `Outcome.Sim`

These are the four cases of `Outcome.Sim` as global `simp` lemmas. They are
stated about `Outcome.Sim` alone, a symbol introduced by this module, so they
cannot interfere with any pre-existing `simp` set; they exist so that
`simp [HostOutcomeSim]` in each semantics' simulation proofs still closes the
mismatched cases after `HostOutcomeSim` became a wrapper. -/

section SimLemmas

variable {S : Type u} {R : Type v} {S' : Type w} {R' : Type x}
  {store : S → S' → Prop} {result : R → R'}

@[simp] theorem Outcome.Sim_diverged_diverged :
    Outcome.Sim store result .diverged .diverged = True := rfl

@[simp] theorem Outcome.Sim_returned_returned (s : S) (r : R) (s' : S') (r' : R') :
    Outcome.Sim store result (.returned s r) (.returned s' r') =
      (store s s' ∧ r' = result r) := rfl

@[simp] theorem Outcome.Sim_diverged_returned (s' : S') (r' : R') :
    Outcome.Sim store result .diverged (.returned s' r') = False := rfl

@[simp] theorem Outcome.Sim_returned_diverged (s : S) (r : R) :
    Outcome.Sim store result (.returned s r) .diverged = False := rfl

end SimLemmas

/-- Host calls preserve a store invariant: whenever `src` returns, a store
satisfying `pre` is left in a state related to it by `post`. The two parameters
are separate because the semantics state this as "well-formed in, well-formed
*and extended* out". -/
def Preserves {H : Type u} {S : Type v} {V : Type w} {R : Type x}
    (pre : S → Prop) (post : S → S → Prop) (src : Semantics H S V R) : Prop :=
  ∀ h s args s' r, src h s args (.returned s' r) → pre s → post s s'

/-- Host compatibility: `src` preserves the store invariant, and every behaviour
of `src` on a store `s` is matched by a behaviour of `tgt` on any store `s'`
related to `s` by `store`, with arguments translated by `value` and outcomes
related by `outcome`.

`outcome` is a parameter rather than `Outcome.Sim store result`, even though all
three instances supply exactly that, so that unfolding `Compatible` reproduces
each semantics' own `HostOutcomeSim` in the goal rather than its expansion. -/
def Compatible {H : Type u} {S : Type v} {V : Type w} {R : Type x}
    {S' : Type y} {V' : Type z} {R' : Type t}
    (pre : S → Prop) (post : S → S → Prop) (store : S → S' → Prop) (value : V → V')
    (outcome : Outcome S R → Outcome S' R' → Prop)
    (src : Semantics H S V R) (tgt : Semantics H S' V' R') : Prop :=
  Preserves pre post src ∧
  ∀ h s args out (s' : S'), src h s args out → store s s' →
    ∃ out', tgt h s' (args.map value) out' ∧ outcome out out'

end Silmaril.Wasm.Execution.Host
