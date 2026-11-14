module

public import Silmaril.Net.Http.Message.Defs

/-!
# A REST service model: a subset of OpenAPI 3.1

An OpenAPI document describes a REST service: the **paths** it serves (templates such as
`/pets/{petId}`), the **operations** on each path (an HTTP method with parameters, an optional
request body and the documented responses), over the RFC 9110 messages of
`Silmaril.Net.Http.Message`. This module models a subset of OpenAPI **3.1.0**:

| OpenAPI 3.1.0 | here | not covered (yet) |
| --- | --- | --- |
| `openapi` | `Document.version`, must be `3.1.0` (`supportedVersion`) | other versions |
| Paths Object, path templating (§4.8.8, §4.8.2.1 of the spec text) | `PathTemplate`, `matchTemplate`; concrete paths are matched before templated ones | path-level `servers`, `$ref` |
| Path Item Object | the operations of a path | `parameters` at path level, `summary` |
| Operation Object | `Operation`: method, `operationId`, parameters, request body, responses | callbacks, security, `deprecated` |
| Parameter Object | `in: path, query, header`, `required`, a schema | `in: cookie`, `style`/`explode`, `content`, percent-decoding |
| Schema Object | `Schema`: `string` (length bounds, `enum`), `integer` (bounds), `boolean` | JSON Schema 2020-12 beyond these; request and response *body* schemas |
| Request Body Object | `required`, the media types of `content` | media type parameters, encodings |
| Responses Object | exact codes, ranges `1XX`–`5XX`, `default`, with exact codes taking precedence over ranges | links |
| Response Object | the media types of `content`, the required `headers` | header schemas |

**Semantics.** `route doc req` finds the operation a request addresses. `RequestConforms`
checks the request against that operation: its required parameters are present and accepted by
their schemas, and its body has a documented media type. `responseSpec op code` is the
documented response for a status code. `ResponseConforms` checks a response against it: the
content type is documented, content is present only when documented, and the required headers
are present. A **service** (`Service`: a function from requests to responses) **conforms**
(`Conforms`) when every conforming request gets a conforming response. It is **closed**
(`Closed`) when, in addition, every response to a routed request has a documented status. The
OpenAPI specification does not require documents to list every status ("It is not expected
for the documentation to necessarily cover all possible HTTP response codes"), so `Closed` is
the stricter, contract-testing reading and is kept separate.

`Silmaril.Net.Http1.Service` relates this model to HTTP/1.1. It runs a service behind the
reference HTTP/1.1 server, and reads a document as a theory of the HTTP/1.1 institution.
-/

@[expose] public section

namespace Silmaril.Net.Http.OpenApi

/-- Octets. -/
abbrev Bytes := List UInt8

/-- The OpenAPI version this model supports. -/
def supportedVersion : String := "3.1.0"

/-- A segment of a path template. -/
inductive Segment where
  /-- A literal segment. -/
  | lit (s : Bytes)
  /-- A template expression `{name}`. -/
  | param (name : Bytes)
  deriving DecidableEq, Repr

/-- A path template, by its segments (`/pets/{petId}` is `[lit "pets", param "petId"]`). -/
abbrev PathTemplate := List Segment

/-- The octets of an ASCII string. -/
def ascii (s : String) : Bytes := s.toList.map fun c => c.toNat.toUInt8

/-- Split at `/`. -/
def splitSlash : Bytes → List Bytes
  | [] => [[]]
  | c :: cs =>
    if c = 0x2F then [] :: splitSlash cs
    else match splitSlash cs with
      | [] => [[c]]
      | w :: ws => (c :: w) :: ws

/-- The path of a path-with-query (before `?`). -/
def pathPart (pq : Bytes) : Bytes := pq.takeWhile (· ≠ 0x3F)

/-- The query of a path-with-query (after the first `?`, empty if none). -/
def queryPart (pq : Bytes) : Bytes := (pq.dropWhile (· ≠ 0x3F)).drop 1

/-- The segments of an absolute path (`/a/b` is `[a, b]`; `/` is `[""]`). -/
def segments (path : Bytes) : List Bytes := (splitSlash path).drop 1

/-- Parse one template segment: `{name}` or a literal. -/
def parseSegment (s : Bytes) : Segment :=
  match s with
  | 0x7B :: rest =>
    if rest.getLast? = some 0x7D ∧ rest.length ≥ 2 then .param rest.dropLast else .lit s
  | _ => .lit s

/-- Parse a path template such as `/pets/{petId}`; it must start with `/`. -/
def parseTemplate (s : Bytes) : Option PathTemplate :=
  if s.head? = some 0x2F then some ((segments s).map parseSegment) else none

/-- Match a template against path segments; the values of the template expressions in order. -/
def matchTemplate : PathTemplate → List Bytes → Option (List Bytes)
  | [], [] => some []
  | .lit l :: ts, s :: ss => if l = s then matchTemplate ts ss else none
  | .param _ :: ts, s :: ss => if s ≠ [] then (matchTemplate ts ss).map (s :: ·) else none
  | _, _ => none

/-- Instantiate a template with values for its expressions, in order. -/
def render : PathTemplate → List Bytes → List Bytes
  | [], _ => []
  | .lit l :: ts, vs => l :: render ts vs
  | .param _ :: ts, v :: vs => v :: render ts vs
  | .param _ :: ts, [] => [] :: render ts []

/-- The names of the template expressions, in order. -/
def PathTemplate.params (t : PathTemplate) : List Bytes :=
  t.filterMap fun | .param n => some n | .lit _ => none

/-- A template is concrete when it has no expressions. -/
def PathTemplate.concrete (t : PathTemplate) : Bool := t.params.isEmpty

/-! ## Schemas and parameters -/

/-- A schema for a parameter value (a subset of JSON Schema 2020-12 as used by OpenAPI 3.1). -/
inductive Schema where
  | string (minLength : Nat) (maxLength : Option Nat) (enum : Option (List Bytes))
  | integer (minimum maximum : Option Int)
  | boolean
  deriving DecidableEq, Repr

/-- The decimal integer a value spells (`-?[0-9]+`). -/
def parseInt? (v : Bytes) : Option Int :=
  let digits (ds : Bytes) : Option Nat :=
    if ds ≠ [] ∧ ds.all (fun c => 0x30 ≤ c ∧ c ≤ 0x39) then
      some (ds.foldl (fun n c => 10 * n + (c.toNat - 0x30)) 0) else none
  match v with
  | 0x2D :: ds => (digits ds).map fun n => -(n : Int)
  | ds => (digits ds).map fun n => (n : Int)

/-- The schema accepts a raw parameter value. -/
def Schema.accepts : Schema → Bytes → Bool
  | .string lo hi en, v => lo ≤ v.length && hi.all (v.length ≤ ·) && en.all (·.contains v)
  | .integer lo hi, v => match parseInt? v with
    | some n => lo.all (· ≤ n) && hi.all (n ≤ ·)
    | none => false
  | .boolean, v => v = ascii "true" || v = ascii "false"

/-- Where a parameter is. -/
inductive Location where
  | path | query | header
  deriving DecidableEq, Repr

/-- A Parameter Object. -/
structure Parameter where
  name : Bytes
  location : Location
  required : Bool
  schema : Schema
  deriving DecidableEq, Repr

/-- A Request Body Object: whether a body is required and its documented media types. -/
structure RequestBody where
  required : Bool
  mediaTypes : List Bytes
  deriving DecidableEq, Repr

/-- A key of the Responses Object. -/
inductive ResponseKey where
  | code (c : Nat)
  /-- `1XX` … `5XX`: the class digit. -/
  | range (cls : Nat)
  | default
  deriving DecidableEq, Repr

/-- A Response Object: documented media types (none: no content) and required headers. -/
structure ResponseSpec where
  mediaTypes : List Bytes
  headers : List Bytes
  deriving DecidableEq, Repr

/-- An Operation Object. -/
structure Operation where
  method : Method
  operationId : String
  parameters : List Parameter
  requestBody : Option RequestBody
  responses : List (ResponseKey × ResponseSpec)
  deriving Repr

/-- A path and its operations. -/
structure PathItem where
  template : PathTemplate
  operations : List Operation
  deriving Repr

/-- An OpenAPI document (the modelled subset). -/
structure Document where
  version : String
  title : String
  paths : List PathItem
  deriving Repr

/-- The methods an Operation Object may have (OpenAPI 3.1 Path Item fields). -/
def isOpenApiMethod : Method → Bool
  | .get | .put | .post | .delete | .options | .head | .patch | .trace => true
  | _ => false

/-- A well-formed document: the supported version, distinct path templates, operations with OpenAPI methods, distinct
methods per path, at least one response each, and each template expression declared as a
required path parameter. -/
def Document.Valid (d : Document) : Prop :=
  d.version = supportedVersion ∧ (d.paths.map PathItem.template).Nodup ∧
  ∀ p ∈ d.paths, (p.operations.map Operation.method).Nodup ∧ ∀ op ∈ p.operations,
    isOpenApiMethod op.method = true ∧ op.responses ≠ [] ∧
    ∀ n ∈ p.template.params, ∃ q ∈ op.parameters, q.name = n ∧ q.location = .path ∧ q.required = true

/-! ## Routing and conformance -/

/-- The path-with-query of a request target (origin form, or the path of an absolute form). -/
def targetPq (t : Target) : Bytes := t.pathWithQuery.getD []

/-- The path item a path is routed to: a concrete template first, then a templated one, each
in document order (OpenAPI: "concrete (non-templated) paths would be matched before their
templated counterparts"). -/
def routePath (d : Document) (path : Bytes) : Option (PathItem × List Bytes) :=
  let segs := segments path
  let hit (p : PathItem) := (matchTemplate p.template segs).map fun vs => (p, vs)
  match (d.paths.filter (·.template.concrete)).findSome? hit with
  | some r => some r
  | none => (d.paths.filter (!·.template.concrete)).findSome? hit

/-- The operation a request addresses, with the values of the path's template expressions. -/
def route (d : Document) (r : Request) : Option (Operation × PathItem × List Bytes) :=
  (routePath d (pathPart (targetPq r.target))).bind fun (p, vs) =>
    (p.operations.find? (·.method == r.method)).map fun op => (op, p, vs)

/-- The value of a query parameter (`name=value` pairs separated by `&`, not percent-decoded). -/
def queryValue (q name : Bytes) : Option Bytes :=
  let pairs := (q.splitOn 0x26 |>.filter (· ≠ [])).map fun kv =>
    (kv.takeWhile (· ≠ 0x3D), (kv.dropWhile (· ≠ 0x3D)).drop 1)
  (pairs.find? (·.1 == name)).map (·.2)

/-- The value of a parameter in a request routed to `p` with template values `vs`. -/
def paramValue (r : Request) (p : PathItem) (vs : List Bytes) (q : Parameter) : Option Bytes :=
  match q.location with
  | .path => ((p.template.params.zip vs).find? (·.1 == q.name)).map (·.2)
  | .query => queryValue (queryPart (targetPq r.target)) q.name
  | .header => r.headers.fieldValue? q.name

/-- `content-type`. -/
def contentTypeName : Bytes := ascii "content-type"

/-- The media type of a message: its `Content-Type` without parameters, lowercase. -/
def mediaType (fs : Field.Section) : Option Bytes :=
  (fs.fieldValue? contentTypeName).map fun v =>
    Abnf.lower ((v.takeWhile (· ≠ 0x3B)).reverse.dropWhile (· = 0x20) |>.reverse)

/-- A request conforms to the operation it is routed to. -/
def RequestConforms (r : Request) (op : Operation) (p : PathItem) (vs : List Bytes) : Prop :=
  (∀ q ∈ op.parameters, match paramValue r p vs q with
    | some v => q.schema.accepts v = true
    | none => q.required = false) ∧
  (match op.requestBody with
    | none => r.content = []
    | some rb => (rb.required = true → r.content ≠ []) ∧
        (r.content ≠ [] → ∃ m ∈ mediaType r.headers, m ∈ rb.mediaTypes))

/-- The documented response for a status code: an exact code, else its range, else `default`. -/
def responseSpec (op : Operation) (code : Nat) : Option ResponseSpec :=
  match op.responses.find? (·.1 == .code code) with
  | some (_, s) => some s
  | none => match op.responses.find? (·.1 == .range (code / 100)) with
    | some (_, s) => some s
    | none => (op.responses.find? (·.1 == .default)).map (·.2)

/-- A response conforms to a documented response. -/
def ResponseConforms (op : Operation) (resp : Response) : Prop :=
  match responseSpec op resp.status with
  | none => True
  | some s =>
    (s.mediaTypes = [] → resp.content = []) ∧
    (resp.content ≠ [] → ∃ m ∈ mediaType resp.headers, m ∈ s.mediaTypes) ∧
    ∀ h ∈ s.headers, resp.headers.has h = true

/-- The status of a response is documented. -/
def Documented (op : Operation) (code : Nat) : Prop := (responseSpec op code).isSome

instance (op : Operation) (code : Nat) : Decidable (Documented op code) :=
  inferInstanceAs (Decidable ((responseSpec op code).isSome = true))

instance (op : Operation) (resp : Response) : Decidable (ResponseConforms op resp) := by
  unfold ResponseConforms; split <;> infer_instance

instance (d : Document) : Decidable d.Valid := by unfold Document.Valid; infer_instance

/-- A service: the response to each request. -/
abbrev Service := Request → Response

/-- A service conforms to a document: conforming requests get conforming responses. -/
def Conforms (d : Document) (S : Service) : Prop :=
  ∀ r op p vs, route d r = some (op, p, vs) → RequestConforms r op p vs → ResponseConforms op (S r)

/-- A service is closed for a document: every routed request gets a documented status. -/
def Closed (d : Document) (S : Service) : Prop :=
  ∀ r op p vs, route d r = some (op, p, vs) → Documented op (S r).status

/-- A service built from a handler per operation: a routed request goes to its operation's
handler with the template values; an unrouted request is answered `405 (Method Not Allowed)`
when its path exists and `404 (Not Found)` otherwise (RFC 9110 §15.5.5, §15.5.6). -/
def Service.ofHandlers (d : Document) (H : Operation → List Bytes → Request → Response) : Service :=
  fun r => match route d r with
    | some (op, _, vs) => H op vs r
    | none =>
      if (routePath d (pathPart (targetPq r.target))).isSome then Response.simple 405 []
      else Response.simple 404 []

end Silmaril.Net.Http.OpenApi
