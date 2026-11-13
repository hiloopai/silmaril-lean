module

public import Silmaril.Net.Http.Method.Defs
public import Silmaril.Net.Http.Status.Defs

@[expose] public section

/-!
# HTTP messages (RFC 9110 §6)

"HTTP messages … consist of: control data …, a header section, content and a trailer section"
(§6, §6.1). `Message C` is that abstraction, version-independent (§6: "the following
abstract data types"), with control data `C`:

* a request's control data (§6.2) is its method (§9) and target (§7.1). The target is given
  by its pieces as WASI has them: an optional scheme, an optional authority and an optional
  path-with-query (`Target`). Their grammars are in `Silmaril.Net.Http.Uri`;
* a response's control data is its status code (§15).

The header and trailer sections are `Field.Section`s (§6.3, §6.5); content is a sequence of
octets (§6.4). Framing (§6.2 "self-descriptive", §6.4.1 content length) belongs to each
version's syntax (`Silmaril.Net.Http1` for HTTP/1.1, not in this module).

Validity (`Request.isValid`, `Response.isValid`): the method is a token, the status code is in
range, every field line is a valid field line, and a response whose status forbids content
(§6.4.1) has none. Target validity is in `Uri`.
-/

namespace Silmaril.Net.Http

open Silmaril.Net.Http.Field

/-- A URI scheme as WASI has it (`http`, `https`, or another scheme by its name). -/
inductive Scheme where
  | http | https
  | other (name : List UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- The pieces of a request target that WASI exposes (§7.1: "target URI": scheme,
authority, path and query). -/
structure Target where
  /-- The scheme (§4.2), if known. -/
  scheme : Option Scheme
  /-- The authority (§4.2.1, RFC 3986 §3.2), if any. -/
  authority : Option (List UInt8)
  /-- The path and query (`absolute-path [ "?" query ]`, §7.1), if any. -/
  pathWithQuery : Option (List UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- The control data of a request (§6.2): method and target. -/
structure RequestLine where
  method : Method
  target : Target
  deriving DecidableEq, Repr, Inhabited

/-- An HTTP message (§6.1) with control data `C`. -/
structure Message (C : Type) where
  /-- Control data (§6.2). -/
  control : C
  /-- The header section (§6.3). -/
  headers : Section
  /-- The content (§6.4). -/
  content : List UInt8
  /-- The trailer section (§6.5). -/
  trailers : Section
  deriving DecidableEq, Repr

/-- A request (§6, §9). -/
abbrev Request := Message RequestLine

/-- A response (§6, §15). -/
abbrev Response := Message Status

namespace Message

variable {C : Type}

/-- The message without content and trailers (the response to `HEAD`, §9.3.2; a 204 or 304,
§6.4.1). -/
def stripContent (m : Message C) : Message C := { m with content := [], trailers := [] }

/-- The field sections are valid. -/
def fieldsValid (m : Message C) : Bool := m.headers.isValid && m.trailers.isValid

end Message

/-- A response with a status and content, no fields. -/
def Response.simple (s : Status) (c : List UInt8) : Response := ⟨s, [], c, []⟩

/-- The method of a request. -/
def Request.method (r : Request) : Method := r.control.method

/-- The target of a request. -/
def Request.target (r : Request) : Target := r.control.target

/-- The status of a response. -/
def Response.status (r : Response) : Status := r.control

/-- A valid request: a token method and valid field lines. -/
def Request.isValid (r : Request) : Bool := r.method.isValid && r.fieldsValid

/-- A valid response: a status code in range, valid field lines, and no content when the
status forbids it (§6.4.1). -/
def Response.isValid (r : Response) : Bool :=
  Status.isValid r.status && r.fieldsValid && (Status.allowsContent r.status || r.content.isEmpty)

end Silmaril.Net.Http
