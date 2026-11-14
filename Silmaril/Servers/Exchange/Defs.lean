module

public import Silmaril.Servers.Core.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.List.Forall2

@[expose] public section

/-!
# Exchange servers: atomic exchanges, specifications and refinement

The sequential reading of a server, used by the `wasi:http` instance
(`Silmaril.Servers.WasiHttp`). Each request and its response form one **atomic exchange**; a
server is observed through the sequences of exchanges it can take part in, that is through its
histories (`Silmaril.Servers.History`). This is the simplification people reason with when a
request is handled as one indivisible step. The concurrent traces of the server core
(`Silmaril.Servers.Core`), where a second request may arrive before the first response, are
reached by two lifts: `seqUse M` (one instance used one request at a time) and `fresh M` (a
fresh instance per request, any number running at once), proved linearizable in `Thms`.

* `Iface`: the interface, the core's `Sig`; an exchange trace is a core `History`.
* `Model I`: a set of exchange traces (a server, as what it can do).
* `Sen I`: a specification, a predicate on exchange traces (a core `SeqSpec`);
  `Sat M φ`: every trace of `M` satisfies `φ`. `each R`: every exchange is related by `R`.
* `Refines M N`: trace inclusion. Refinement preserves satisfaction (`Refines.sat`).
* `ofFun f`: the server of a response function; `ofRel R`: the loosest server of `each R`.
* `Hom I J`: an interface morphism: `J`'s requests are read as `I`'s and `I`'s responses
  are written as `J`'s, so an `I`-server serves `J` (`Hom.lift`). Specifications pull back
  along it (`Hom.pull`), with the satisfaction condition `Hom.sat_lift_iff`.

A Silmaril addition.
-/

namespace Silmaril.Servers.Exchange

/-- A server interface: the core's signature, the requests and the responses. -/
abbrev Iface : Type 1 := Sig

variable {I J : Iface}

/-- An atomic exchange: a request and its response. -/
abbrev Exch (I : Iface) : Type := I.Req × I.Resp

/-- A server, as the exchange traces it can take part in. -/
abbrev Model (I : Iface) : Type := Set (History I)

/-- A specification: a predicate on exchange traces. -/
abbrev Sen (I : Iface) : Type := SeqSpec I

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

/-! ## Lifts to the concurrent traces of the core -/

/-- **One instance, used sequentially**: the core traces in which each request is answered
before the next arrives, on fresh identities, with the history a trace of `M`. -/
def seqUse (M : Model I) : Servers.Model I :=
  ⟨fun t => ∃ h : List (ReqId × I.Req × I.Resp),
    (h.map (·.1)).Nodup ∧ h.map (·.2) ∈ M ∧ t = Trace.seq h⟩

/-- **A fresh instance per request** (the `wasi:http` proxy world as `wasmtime serve` runs it):
the well-formed core traces, with any overlap of requests, in which every request and its
response form a one-exchange trace of `M`. -/
def fresh (M : Model I) : Servers.Model I :=
  ⟨fun t => Sen.WF t ∧ ∀ i r s, Event.recv i r ∈ t → Event.send i s ∈ t → [(r, s)] ∈ M⟩

end Silmaril.Servers.Exchange
