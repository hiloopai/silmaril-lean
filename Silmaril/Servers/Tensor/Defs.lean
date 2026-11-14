module

public import Silmaril.Servers.Core.Defs

/-!
# Independent endpoints: the tensor of servers

Two endpoints are **independent** when a client can tell what one of them does without looking
at the other: the requests of each go to it alone (**route disjointness**) and its responses
depend on its own requests only (**state isolation**). This module gives that notion a
semantics and states its laws; it does not claim it of servers that share state
(`Thms.shared_not_tensor`).

## Interfaces and traces

The tensor interface `A ⊗ B` (`Sig.tensor`) has the requests and responses of either side,
tagged (`Sum`). A trace of `A ⊗ B` interleaves events of both sides; `Trace.left` and
`Trace.right` keep the events of one side (with their identities).

## Models

The **tensor of models** (`Model.tensor M N`) has the traces whose left part is a trace of `M`
and whose right part is a trace of `N`: every interleaving of their observations
(**interleaving semantics**: the order across the two sides is the environment's, and nothing
in one side's part depends on the other's). The unit is the model of the empty interface with
only the empty trace (`Model.unit`).

## Routing over one interface

A **router** `ρ : A.Req → Bool` sends a request to the left endpoint (`true`) or the right one.
Because it is a function of the request, the two routes are disjoint and cover every request.
`Model.routed ρ M N` is the server over `A` that answers the requests of each route by the
corresponding endpoint: the tensor traces whose every request is on its route, with the tags
forgotten (`untag`).

## Machines with isolated state

`Machine.tensor M₁ M₂` runs the handler of the side a request belongs to on that side's state
only (**state isolation**): its histories are the interleavings of histories of the two
machines (`Thms.tensor_run_iff`). A machine whose two endpoints share a counter is not of this
form (`Thms.shared_not_tensor`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers

/-- **The tensor of interfaces**: requests and responses of either side, tagged. -/
@[reducible] def Sig.tensor (A B : Sig) : Sig := ⟨A.Req ⊕ B.Req, A.Resp ⊕ B.Resp⟩

/-- The empty interface, the unit of the tensor. -/
@[reducible] def Sig.unit : Sig := ⟨Empty, Empty⟩

namespace Tensor

variable {A B C : Sig}

/-- The event of the left side, if it is one. -/
def Event.left : Event (A.tensor B) → Option (Event A)
  | .recv i (.inl r) => some (.recv i r)
  | .send i (.inl s) => some (.send i s)
  | _ => none

/-- The event of the right side, if it is one. -/
def Event.right : Event (A.tensor B) → Option (Event B)
  | .recv i (.inr r) => some (.recv i r)
  | .send i (.inr s) => some (.send i s)
  | _ => none

/-- A left event, tagged. -/
def Event.inl : Event A → Event (A.tensor B)
  | .recv i r => .recv i (.inl r)
  | .send i s => .send i (.inl s)

/-- A right event, tagged. -/
def Event.inr : Event B → Event (A.tensor B)
  | .recv i r => .recv i (.inr r)
  | .send i s => .send i (.inr s)

/-- The two sides exchanged. -/
def Event.swap : Event (A.tensor B) → Event (B.tensor A)
  | .recv i r => .recv i r.swap
  | .send i s => .send i s.swap

/-- Reassociation. -/
def Event.assoc : Event ((A.tensor B).tensor C) → Event (A.tensor (B.tensor C))
  | .recv i r => .recv i (Equiv.sumAssoc _ _ _ r)
  | .send i s => .send i (Equiv.sumAssoc _ _ _ s)

/-- The events of the left side. -/
def Trace.left (t : Trace (A.tensor B)) : Trace A := t.filterMap Event.left

/-- The events of the right side. -/
def Trace.right (t : Trace (A.tensor B)) : Trace B := t.filterMap Event.right

end Tensor

open Tensor

/-- **The tensor of models**: the interleavings of a trace of each. -/
def Model.tensor {A B : Sig} (M : Model A) (N : Model B) : Model (A.tensor B) :=
  ⟨fun t => M.Tr (Trace.left t) ∧ N.Tr (Trace.right t)⟩

/-- The unit model: the empty interface, only the empty trace. -/
def Model.unit : Model Sig.unit := ⟨fun t => t = []⟩

/-- **A router**: `true` sends a request to the left endpoint, `false` to the right one. -/
abbrev Router (A : Sig) : Type := A.Req → Bool

/-- Every request of the trace is on its route. -/
def RoutedBy {A : Sig} (ρ : Router A) (t : Trace (A.tensor A)) : Prop :=
  ∀ i r, Event.recv i r ∈ t → ρ (Sum.elim id id r) = r.isLeft

/-- Forget the tags. -/
def untag (A : Sig) : Hom A (A.tensor A) := ⟨Sum.elim id id, Sum.elim id id⟩

/-- **The routed server**: requests on the left route answered by `M`, the others by `N`. -/
def Model.routed {A : Sig} (ρ : Router A) (M N : Model A) : Model A :=
  ⟨fun t => ∃ t', (M.tensor N).Tr t' ∧ RoutedBy ρ t' ∧ (untag A).trace t' = t⟩

/-- **Machines with isolated state**: a request of either side runs that side's handler on
that side's state. -/
def Machine.tensor {A B : Sig} {σ τ : Type} (M₁ : Machine A σ) (M₂ : Machine B τ) :
    Machine (A.tensor B) (σ × τ)
  | (q₁, q₂), .inl r, .inl s, (q₁', q₂') => M₁ q₁ r s q₁' ∧ q₂' = q₂
  | (q₁, q₂), .inr r, .inr s, (q₁', q₂') => M₂ q₂ r s q₂' ∧ q₁' = q₁
  | _, _, _, _ => False

namespace Tensor

/-- The left pairs of a history. -/
def History.left {A B : Sig} (h : History (A.tensor B)) : History A :=
  h.filterMap fun | (.inl r, .inl s) => some (r, s) | _ => none

/-- The right pairs of a history. -/
def History.right {A B : Sig} (h : History (A.tensor B)) : History B :=
  h.filterMap fun | (.inr r, .inr s) => some (r, s) | _ => none

/-- Every pair of the history is answered on the side of its request. -/
def History.Routed {A B : Sig} (h : History (A.tensor B)) : Prop :=
  ∀ p ∈ h, p.1.isLeft = p.2.isLeft

end Tensor

end Silmaril.Servers

/-! ## A shared counter (not independent) -/

namespace Silmaril.Servers.Tensor

/-- A counter endpoint: a request is answered with the count, which then increases. -/
abbrev cntSig : Sig := ⟨Unit, Nat⟩

/-- **A counter**, with its own state. -/
def counter : Machine cntSig Nat := fun n _ s n' => s = n ∧ n' = n + 1

/-- **Two endpoints sharing one counter**: either endpoint answers the shared count. -/
def sharedCounter : Machine (cntSig.tensor cntSig) Nat
  | n, .inl _, .inl s, n' => s = n ∧ n' = n + 1
  | n, .inr _, .inr s, n' => s = n ∧ n' = n + 1
  | _, _, _, _ => False

end Silmaril.Servers.Tensor
