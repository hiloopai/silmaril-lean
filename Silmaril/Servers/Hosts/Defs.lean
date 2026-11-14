module

public import Silmaril.Servers.Observe.Defs

/-!
# Host interpretations of imports, and how to quantify over them

A server with imports (a component importing `wasi:random`, a process reading a clock) has no
behaviour of its own: it has one under each **host strategy** `η : H` that answers its imports.
An **open server** (`Open H A`) is that map from host strategies to behaviours. Comparing two
open servers, or asking a property of one, needs an explicit quantifier over a set of hosts
`Hs : Set H`, and the quantifier decides what is claimed:

| claim | definition | reading |
| --- | --- | --- |
| `RefinesAt Hs C D` | `∀ η ∈ Hs, C η ⊆ D η` | same host on both sides: refinement for every environment |
| `EquivAt Hs C D` | `∀ η ∈ Hs, C η = D η` | observational equivalence for every environment |
| `MustAll Hs C φ` | `∀ η ∈ Hs, Must (C η) φ` | `φ` holds whatever the host does (demonic) |
| `MaySome Hs C φ` | `∃ η ∈ Hs, May (C η) φ` | some host lets some run show `φ` (angelic) |
| `MayAll Hs C φ` | `∀ η ∈ Hs, May (C η) φ` | under every host, some run shows `φ` |

`under Hs C` merges the hosts into one behaviour (the union). Universal and existential
properties of the union are `MustAll` and `MaySome` (`Thms`), but refinement of unions is
weaker than `RefinesAt`: it lets the two sides use different hosts (`Thms.under_not_refinesAt`).

## Three kinds of host

Imports are calls `Q` answered in `R` (for `wasi:random` `get-random-u64`: `Q = Unit`,
`R = UInt64`).

* **Pure deterministic** (`Pure Q R`): a function of the call. One host; replay is trivial.
* **User nondeterminism** (`Oracle R`): the `k`-th call is answered `o k`; the set of all
  oracles is "the host answers anything". A **seeded** family (`seeded gen`) is the set of
  hosts `gen s` for seeds `s`: each is deterministic, the set is nondeterministic.
* **Effectful, stateful** (`Stateful σ Q R`): a state machine answering each call from its
  state (a host's file system, a chaos policy with a counter). Deterministic given its state, so
  every run is **replayable** from the initial state (`Stateful.answers`).

Pure hosts and oracles are stateful hosts (`Pure.toStateful`, `Oracle.toStateful`). The runtime
harness (`tests/servers/policies`) runs components under hosts of these kinds (`zero` is pure,
`seeded s` is one member of a seeded family, `chaos s` is stateful); what it observes is testing
evidence about those hosts only, never a `MustAll` over a set it did not exhaust.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Hosts

open Silmaril.Servers Silmaril.Servers.Observe

/-- **An open server**: its behaviour under each host strategy. -/
abbrev Open (H : Type) (A : Sig) : Type := H → Beh A

variable {H : Type} {A : Sig}

/-- The behaviours under the hosts of `Hs`, merged. -/
def under (Hs : Set H) (C : Open H A) : Beh A := ⋃ η ∈ Hs, C η

/-- **Refinement for every host of `Hs`**, the same host on both sides. -/
def RefinesAt (Hs : Set H) (C D : Open H A) : Prop := ∀ η ∈ Hs, (C η).Refines (D η)

/-- **Observational equivalence for every host of `Hs`.** -/
def EquivAt (Hs : Set H) (C D : Open H A) : Prop := ∀ η ∈ Hs, C η = D η

/-- `φ` holds of every observation under every host of `Hs`. -/
def MustAll (Hs : Set H) (C : Open H A) (φ : Obs A → Prop) : Prop := ∀ η ∈ Hs, (C η).Must φ

/-- Some host of `Hs` lets some observation satisfy `φ`. -/
def MaySome (Hs : Set H) (C : Open H A) (φ : Obs A → Prop) : Prop := ∃ η ∈ Hs, (C η).May φ

/-- Under every host of `Hs`, some observation satisfies `φ`. -/
def MayAll (Hs : Set H) (C : Open H A) (φ : Obs A → Prop) : Prop := ∀ η ∈ Hs, (C η).May φ

/-! ## Kinds of host -/

/-- **A pure deterministic host**: a function of the call. -/
abbrev Pure (Q R : Type) : Type := Q → R

/-- **An oracle**: the `k`-th call is answered `o k` (user nondeterminism, over all oracles). -/
abbrev Oracle (R : Type) : Type := Nat → R

/-- **A stateful host**: an initial state and a deterministic step answering each call. -/
structure Stateful (σ Q R : Type) where
  /-- The initial state. -/
  init : σ
  /-- Answer a call from a state, with the next state. -/
  step : σ → Q → R × σ

/-- The answers of a stateful host to a sequence of calls, from a state: its replay. -/
def Stateful.answers {σ Q R : Type} (h : Stateful σ Q R) : σ → List Q → List R
  | _, [] => []
  | s, q :: qs => (h.step s q).1 :: h.answers (h.step s q).2 qs

/-- A pure host as a stateful host. -/
def Pure.toStateful {Q R : Type} (f : Pure Q R) : Stateful Unit Q R := ⟨(), fun _ q => (f q, ())⟩

/-- An oracle as a stateful host counting calls. -/
def Oracle.toStateful {Q R : Type} (o : Oracle R) : Stateful Nat Q R := ⟨0, fun k _ => (o k, k + 1)⟩

/-- A seeded family of hosts. -/
def seeded {S σ Q R : Type} (gen : S → Stateful σ Q R) : Set (Stateful σ Q R) := Set.range gen

end Silmaril.Servers.Hosts
