module

public import Silmaril.Servers.Http.Defs
public import Silmaril.Net.Http.OpenApi.Defs
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# An institution for "does this HTTP server satisfy this OpenAPI document?"

The question is asked of a **server** of the core (`Silmaril.Servers.Core`): the set of
request/response traces it can be observed doing over RFC 9110 messages (`Servers.Http.sig`),
whatever runs it (a `wasi:http` component, a process, the HTTP/1.1 reference server). The
document side is the OpenAPI 3.1 subset of `Silmaril.Net.Http.OpenApi` (paths, templates,
operations, parameters with simple schemas, request body media types, documented responses).

| institution | here |
| --- | --- |
| signatures | `Sig`: a type of **operation symbols** |
| morphisms | `Sig.Hom`: maps of operation symbols (renaming, extension, identification) |
| models | `Model Σ`: a document, the operation each symbol denotes in it (`bind`), and a server |
| reduct | `Model.reduct σ`: the same document and server, symbols bound through `σ` |
| sentences | `Sen Σ`: obligations per operation symbol, with conjunction and negation |
| satisfaction | `Sat M φ`: trace sentences of the server |

**Obligations.** A request is *routed to* the symbol `o` when the document's router
(`OpenApi.route`, with concrete paths before templated ones) sends it to the operation `bind o`.
Three kinds of obligation are kept apart:

* `respOk o` (**response obligation**, assume–guarantee): every response to a request routed to
  `o` *that conforms to the operation* (`RequestConforms`, the client's obligation, taken as the
  hypothesis) conforms to the documented response for its status (`ResponseConforms`);
* `closed o` (**closed-world status**): every response to a request routed to `o` has a
  documented status (OpenAPI does not require this, so it is a separate sentence);
* `rejects o cs` (**request obligation on the server**: validation): every response to a request
  routed to `o` that does *not* conform has a status in `cs` (typically `4xx`).

Each is an atomic trace sentence (`Servers.Sen.atomic`): it constrains the response to each
request on its own. Obligations about connections, framing or ordering are not sentences
here: they belong to the HTTP/1.1 institution (`Silmaril.Net.Http1.Inst`) and the transport
readings.

**Supported subset.** That of `Net.Http.OpenApi`: OpenAPI 3.1.0, path/query/header
parameters with `string`/`integer`/`boolean` schemas (no percent-decoding, no `style`), body
presence and media types (not body schemas), documented status codes, ranges and `default`,
response media types and required headers. Callbacks, security, links and JSON Schema beyond
these are out of scope.

`docSig d` and `docModel d S` read a document and a service (a function) as a signature and a
model; `Thms` shows that the sentences of a document hold exactly when the existing
`OpenApi.Conforms` and `OpenApi.Closed` hold.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.OpenApiInst

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Net.Http (Request Response)
open Silmaril.Net.Http.OpenApi

/-- **A signature**: operation symbols. -/
structure Sig : Type 1 where
  Op : Type

/-- **A signature morphism**: a map of operation symbols. -/
@[ext] structure Sig.Hom (A B : Sig) : Type where
  op : A.Op → B.Op

instance : Category Sig where
  Hom := Sig.Hom
  id _ := ⟨id⟩
  comp σ τ := ⟨τ.op ∘ σ.op⟩

/-- **Obligations of a server towards the operations of a document.** -/
inductive Sen (A : Sig) : Type where
  /-- Conforming requests routed to `o` get conforming responses. -/
  | respOk (o : A.Op)
  /-- Requests routed to `o` get documented statuses. -/
  | closed (o : A.Op)
  /-- Non-conforming requests routed to `o` are answered with a status in `cs`. -/
  | rejects (o : A.Op) (cs : List Nat)
  | conj (φ ψ : Sen A)
  | neg (φ : Sen A)

/-- Sentence translation. -/
def Sen.map {A B : Sig} (σ : Sig.Hom A B) : Sen A → Sen B
  | .respOk o => .respOk (σ.op o)
  | .closed o => .closed (σ.op o)
  | .rejects o cs => .rejects (σ.op o) cs
  | .conj φ ψ => .conj (φ.map σ) (ψ.map σ)
  | .neg φ => .neg (φ.map σ)

/-- **A model**: a document, the operation each symbol denotes, and a server. -/
structure Model (A : Sig) : Type where
  doc : Document
  bind : A.Op → Operation
  server : Servers.Model Http.sig

/-- The reduct along a signature morphism. -/
def Model.reduct {A B : Sig} (σ : Sig.Hom A B) (M : Model B) : Model A :=
  ⟨M.doc, M.bind ∘ σ.op, M.server⟩

/-- The request is routed to the operation `op` of the document, with path item `p` and
template values `vs`. -/
def Routed (d : Document) (op : Operation) (r : Request) (p : PathItem) (vs : List Bytes) :
    Prop :=
  route d r = some (op, p, vs)

/-- The response obligation of an operation, as a relation. -/
def respOkRel (d : Document) (op : Operation) (r : Request) (s : Response) : Prop :=
  ∀ p vs, Routed d op r p vs → RequestConforms r op p vs → ResponseConforms op s

/-- The closed-world status obligation. -/
def closedRel (d : Document) (op : Operation) (r : Request) (s : Response) : Prop :=
  ∀ p vs, Routed d op r p vs → Documented op s.status

/-- The validation obligation. -/
def rejectsRel (d : Document) (op : Operation) (cs : List Nat) (r : Request) (s : Response) :
    Prop :=
  ∀ p vs, Routed d op r p vs → ¬ RequestConforms r op p vs → s.status ∈ cs

/-- **Satisfaction.** -/
def Sat {A : Sig} (M : Model A) : Sen A → Prop
  | .respOk o => M.server.Sat (Servers.Sen.atomic (A := Http.sig) (respOkRel M.doc (M.bind o)))
  | .closed o => M.server.Sat (Servers.Sen.atomic (A := Http.sig) (closedRel M.doc (M.bind o)))
  | .rejects o cs =>
      M.server.Sat (Servers.Sen.atomic (A := Http.sig) (rejectsRel M.doc (M.bind o) cs))
  | .conj φ ψ => Sat M φ ∧ Sat M ψ
  | .neg φ => ¬ Sat M φ

/-- Sentences without negation. -/
def Sen.Pos {A : Sig} : Sen A → Prop
  | .conj φ ψ => φ.Pos ∧ ψ.Pos
  | .neg _ => False
  | _ => True

/-! ## Documents as signatures and theories -/

/-- The operations of a document. -/
def DocOp (d : Document) : Type := {op : Operation // ∃ p ∈ d.paths, op ∈ p.operations}

/-- **The signature of a document**: its operations. -/
def docSig (d : Document) : Sig := ⟨DocOp d⟩

/-- **A service with a document, as a model**: the function server of the service. -/
def docModel (d : Document) (S : Service) : Model (docSig d) :=
  ⟨d, Subtype.val, Servers.Model.ofFun (A := Http.sig) S⟩

/-- A server with a document, as a model. -/
def serverModel (d : Document) (M : Servers.Model Http.sig) : Model (docSig d) :=
  ⟨d, Subtype.val, M⟩

end Silmaril.Servers.OpenApiInst
