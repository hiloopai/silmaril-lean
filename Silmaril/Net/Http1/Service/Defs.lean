module

public import Silmaril.Net.Http1.Institution.Defs
public import Silmaril.Net.Http.OpenApi.Defs

/-!
# REST services over HTTP/1.1: OpenAPI documents as theories of the HTTP/1.1 institution

This module relates the OpenAPI service model of `Silmaril.Net.Http.OpenApi`, which works over
RFC 9110 messages, to HTTP/1.1:

* **Running a service.** `serviceHandler S` puts a service `S : Service` behind the
  reference HTTP/1.1 server (`Silmaril.Net.Http1.Pipeline`). A checked request becomes an RFC
  9110 request (`toRequest`), and the service's response becomes an HTTP/1.1 response
  (`toResponse`). The server owns the framing: it drops framing and hop-by-hop fields from
  the service's headers and frames content with `Content-Length`. `CONNECT`, which OpenAPI
  does not describe, is answered `501`. `serviceModel S` is the result as a model of the
  HTTP/1.1 institution, over the vocabulary `ApiSig` (the standard methods and `PATCH`).
* **Documents as theories.** `toTheory d` reads the closed-world status obligations of a
  document as sentences: for each operation without a `default` response, every valid
  request with its method that the document routes to its path is answered with a documented
  status, or with a request error of the server (`400`, `501`, `505`).

The laws (`Service.Thms`): a service with valid responses is a **vanilla** HTTP/1.1
implementation behind the reference server (`serviceModel_vanilla`), and a service that is
**closed** for a valid document **satisfies the document's theory**
(`closed_satisfies_theory`). The vanilla obligations and the service's obligations then hold
together in one institution.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Net.Http.OpenApi (Document PathItem Operation ResponseKey)

/-- Fields the server owns: framing and hop-by-hop fields (lowercase). -/
def serverOwnedNames : List Bytes :=
  [contentLengthName, transferEncodingName, connectionName, keepAliveOption, teName, upgradeName,
    ascii "trailer", ascii "proxy-connection"]

/-- An RFC 9110 field line as an HTTP/1.1 field line. -/
def FieldLine.ofLine (l : Http.Field.Line) : FieldLine := ⟨l.name, l.value⟩

/-- The service's fields that the server forwards. -/
def forwardedFields (s : Http.Field.Section) : List FieldLine :=
  (s.filter fun l => !serverOwnedNames.contains (lower l.name)).map FieldLine.ofLine

/-- The HTTP/1.1 response of an RFC 9110 response, framed by `Content-Length` when its status
allows content (RFC 9110 §6.4.1, RFC 9112 §6.2). -/
def toResponse (r : Http.Response) : ResponseHead × Body :=
  if Http.Status.allowsContent r.status then
    (⟨⟨Version.http11, r.status, []⟩,
      forwardedFields r.headers ++ [⟨ascii "Content-Length", decDigits r.content.length⟩]⟩,
      .content r.content)
  else (⟨⟨Version.http11, r.status, []⟩, forwardedFields r.headers⟩, .none)

/-- A service behind the reference server. -/
def serviceHandler (S : Http.OpenApi.Service) : Handler := fun h b c =>
  if h.line.method = methodCONNECT then toResponse (Http.Response.simple 501 [])
  else toResponse (S (toRequest h b c))

/-- A service's responses are valid: valid field lines and a three-digit status. -/
def ServiceValid (S : Http.OpenApi.Service) : Prop :=
  ∀ r, (S r).headers.isValid = true ∧ (S r).status < 1000

namespace Inst

/-- The vocabulary of OpenAPI operations: the standard methods and `PATCH`. -/
abbrev ApiSig : Sig := PatchSig

/-- The symbol of an OpenAPI method (`CONNECT` and extension methods have none). -/
def methodSym : Http.Method → Option ApiSig.Meth
  | .get => some (.inl .get) | .head => some (.inl .head) | .post => some (.inl .post)
  | .put => some (.inl .put) | .delete => some (.inl .delete) | .options => some (.inl .options)
  | .trace => some (.inl .trace) | .patch => some (.inr ()) | .connect => none | .other _ => none

/-- A service behind the reference server, as a model of `ApiSig`. -/
def serviceModel (S : Http.OpenApi.Service) : Model ApiSig :=
  ⟨Sum.elim StdMethod.token fun _ => methodPATCH, Sum.elim StdField.name Empty.elim,
    Sum.elim StdCoding.name Empty.elim, refImpl {} (serviceHandler S)⟩

/-- The origin-form targets that the document routes to the path `p`. -/
def routesTo (d : Document) (p : PathItem) : Route := fun t =>
  t.head? == some 0x2F &&
    match Http.OpenApi.routePath d (Http.OpenApi.pathPart t) with
    | some (q, _) => q.template == p.template
    | none => false

/-- The documented status codes of an operation; `none` when it has a `default` response. -/
def opCodes (op : Operation) : Option (List Nat) :=
  if op.responses.any (·.1 == .default) then none
  else some (op.responses.flatMap fun k => match k.1 with
    | .code c => [c]
    | .range n => (List.range 100).map (100 * n + ·)
    | .default => [])

/-- The status codes the reference server answers without consulting the service. -/
def serverErrorCodes : List Nat := [400, 501, 505]

/-- The closed-world status obligations of a document. -/
def toTheory (d : Document) : List (Sen ApiSig) :=
  d.paths.flatMap fun p => p.operations.filterMap fun op =>
    match methodSym op.method, opCodes op with
    | some m, some cs => some (.status m (routesTo d p) (cs ++ serverErrorCodes))
    | _, _ => none

end Inst

end Silmaril.Net.Http1
