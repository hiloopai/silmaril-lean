module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.List.Forall2

@[expose] public section

/-!
# Atomic servers: interfaces, exchange traces, specifications and refinement

The smallest platform-neutral reading of a server, used by the `wasi:http` instance
(`Silmaril.Servers.WasiHttp`). Each request and its response form one **atomic exchange**; a
server is observed through the sequences of exchanges it can take part in. This is the
simplification people reason with when a request is handled as one indivisible step. Concurrent
traces, where a second request arrives before the first response, are not part of this module.

* `Iface`: a signature: what requests and responses are.
* `Model I`: a set of exchange traces (a server, as what it can do).
* `Sen I`: a specification, a predicate on exchange traces; `Sat M φ`: every trace of `M`
  satisfies `φ`. `each R`: every exchange is related by `R`.
* `Refines M N`: trace inclusion. Refinement preserves satisfaction (`Refines.sat`).
* `ofFun f`: the server of a response function; `ofRel R`: the loosest server of `each R`.
* `Hom I J`: an interface morphism: `J`'s requests are read as `I`'s and `I`'s responses
  are written as `J`'s, so an `I`-server serves `J` (`Hom.lift`). Specifications pull back
  along it (`Hom.pull`), with the satisfaction condition `Hom.sat_lift_iff`.

A Silmaril addition.
-/

namespace Silmaril.Servers

/-- A server interface: the requests and the responses. -/
structure Iface where
  /-- The requests. -/
  Req : Type
  /-- The responses. -/
  Resp : Type

variable {I J : Iface}

/-- An atomic exchange: a request and its response. -/
abbrev Exch (I : Iface) : Type := I.Req × I.Resp

/-- A server, as the exchange traces it can take part in. -/
abbrev Model (I : Iface) : Type := Set (List (Exch I))

/-- A specification: a predicate on exchange traces. -/
abbrev Sen (I : Iface) : Type := List (Exch I) → Prop

/-- **Satisfaction**: every trace of the server satisfies the specification. -/
def Sat (M : Model I) (φ : Sen I) : Prop := ∀ t ∈ M, φ t

/-- **Refinement** is trace inclusion. -/
def Refines (M N : Model I) : Prop := M ⊆ N

/-- Every exchange is related by `R`. -/
def each (R : I.Req → I.Resp → Prop) : Sen I := fun t => ∀ e ∈ t, R e.1 e.2

/-- The server answering every request `q` with `f q`. -/
def ofFun (f : I.Req → I.Resp) : Model I := {t | ∀ e ∈ t, e.2 = f e.1}

/-- The loosest server whose exchanges are related by `R`. -/
def ofRel (R : I.Req → I.Resp → Prop) : Model I := {t | each R t}

/-- An interface morphism: `J`'s requests read as `I`'s, `I`'s responses written as `J`'s. -/
structure Hom (I J : Iface) where
  /-- Reading a request. -/
  req : J.Req → I.Req
  /-- Writing a response. -/
  resp : I.Resp → J.Resp

/-- An exchange of `J` is served by an exchange of `I` along `h`. -/
def Hom.Serves (h : Hom I J) (e : Exch I) (e' : Exch J) : Prop :=
  h.req e'.1 = e.1 ∧ e'.2 = h.resp e.2

/-- **An `I`-server serving `J`**: the `J`-traces served exchange by exchange. -/
def Hom.lift (h : Hom I J) (M : Model I) : Model J :=
  {t' | ∃ t ∈ M, List.Forall₂ h.Serves t t'}

/-- A `J`-specification pulled back to `I`: it holds of every trace served along `h`. -/
def Hom.pull (h : Hom I J) (φ : Sen J) : Sen I :=
  fun t => ∀ t', List.Forall₂ h.Serves t t' → φ t'

end Silmaril.Servers
