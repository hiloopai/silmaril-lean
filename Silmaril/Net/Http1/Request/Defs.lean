module

public import Silmaril.Net.Http1.Profile.Defs
public import Silmaril.Net.Http.Message.Defs
public import Silmaril.Net.Http.Uri.Defs

/-!
# HTTP/1.1 request context: target forms, `Host`, validation and the RFC 9110 message

A server that has read a request head (`Silmaril.Net.Http1.Message`) still has to decide
whether the request is acceptable and what it means. This module transcribes those rules:

* **Request-target forms** (RFC 9112 §3.2): `origin-form` (`absolute-path [ "?" query ]`),
  `absolute-form` (here `scheme "://" authority [ path-with-query ]`, the hierarchical
  `absolute-URI`s that HTTP uses), `authority-form` (`uri-host ":" port`, CONNECT only,
  §3.2.3) and `asterisk-form` (`*`, OPTIONS only, §3.2.4). `targetForm` classifies a target
  with the RFC 3986 checks of `Silmaril.Net.Http.Uri`. Not covered: `IP-literal` hosts
  (RFC 3986 §3.2.2) and non-hierarchical absolute URIs, which are rejected.
* **`Host`** (RFC 9112 §3.2, RFC 9110 §7.2): "A server MUST respond with a 400 (Bad Request)
  status code to any HTTP/1.1 request message that lacks a Host header field and to any
  request message that contains more than one Host header field line or a Host header
  field with an invalid field value."
* **Version** (RFC 9110 §2.5, §15.6.6): a major version other than 1 is answered `505`.
* **Framing and codings** (RFC 9112 §6.1, §6.3, §7): the framing as the recipient's
  `Profile` reads it; `400` for invalid framing, `501` for a coding the server does not
  implement (`checkCodings`).
* **The target URI** (RFC 9112 §3.3): from the absolute form, or from the scheme of the
  connection, the `Host` value and the target.
* **Persistence** (RFC 9112 §9.3, §6.1, §6.3 rule 3): whether the connection may carry
  another request (`Connection.persists`, `framingForcesClose`).

`checkRequest cfg h` returns either a `RequestError` (with the status a server answers,
`RequestError.status`) or the request's `Context`. `toRequest` then builds the
version-independent `Silmaril.Net.Http.Request` (RFC 9110 §6) from the head, the body and the
context: headers, content (the dechunked payload) and trailers.

**Trailers** (RFC 9110 §6.5, RFC 9112 §7.1.2): a recipient may merge trailer fields into the
header section only when their definition permits it. `mergeTrailers` keeps none of the
fields that §6.5.1 forbids in trailers (framing, routing, request modifiers, authentication,
response control data and content processing), so merging cannot change how a message is
framed or routed (`Request.Thms`).
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)

/-- The forms of a request target (RFC 9112 §3.2). -/
inductive TargetForm where
  | origin | absolute | authority | asterisk
  deriving DecidableEq, Repr

/-- `OPTIONS`. -/
def methodOPTIONS : Bytes := ascii "OPTIONS"

/-- `"/"`, `"?"`, `":"`. -/
abbrev SLASH : UInt8 := 0x2F
abbrev QMARK : UInt8 := 0x3F

/-- Normalise an empty path to `/` (RFC 9110 §4.2.3). -/
def pathOrRoot (rest : Bytes) : Bytes :=
  match rest with
  | [] => [SLASH]
  | c :: cs => if c = QMARK then SLASH :: c :: cs else c :: cs

/-- The pieces of an absolute-form target `scheme "://" authority [ path-with-query ]`:
the scheme, the authority and the path with query (an empty path read as `/`). -/
def absoluteParts (t : Bytes) : Option (Bytes × Bytes × Bytes) :=
  let scheme := t.takeWhile (· ≠ COLON)
  match t.dropWhile (· ≠ COLON) with
  | _ :: s₁ :: s₂ :: rest =>
    if s₁ = SLASH ∧ s₂ = SLASH then
      let auth := rest.takeWhile fun c => c ≠ SLASH ∧ c ≠ QMARK
      let pq := pathOrRoot (rest.dropWhile fun c => c ≠ SLASH ∧ c ≠ QMARK)
      if Http.Uri.isScheme scheme ∧ auth ≠ [] ∧ Http.Uri.isHttpAuthority auth ∧
          Http.Uri.isPathWithQuery pq then some (lower scheme, auth, pq) else none
    else none
  | _ => none

/-- `authority-form = uri-host ":" port` (RFC 9112 §3.2.3), with a nonempty host and port. -/
def isAuthorityForm (t : Bytes) : Bool :=
  Http.Uri.isHttpAuthority t &&
    ((Http.Uri.splitAt? COLON t).2.any fun p => p ≠ []) && (Http.Uri.splitAt? COLON t).1 ≠ []

/-- Classify a request target (RFC 9112 §3.2); `none` if it has none of the forms. -/
def targetForm (method target : Bytes) : Option TargetForm :=
  if target = [0x2A] then some .asterisk
  else if target.head? = some SLASH then
    if Http.Uri.isPathWithQuery target then some .origin else none
  else if method = methodCONNECT then
    if isAuthorityForm target then some .authority else none
  else if (absoluteParts target).isSome then some .absolute
  else none

/-- The form agrees with the method (RFC 9112 §3.2.3, §3.2.4, RFC 9110 §9.3.6). -/
def formFits (method : Bytes) : TargetForm → Bool
  | .asterisk => method = methodOPTIONS
  | .authority => method = methodCONNECT
  | .origin | .absolute => method ≠ methodCONNECT

/-! ## Errors and context -/

/-- Why a server rejects a request head. -/
inductive RequestError where
  /-- A major version other than 1 (RFC 9110 §15.6.6). -/
  | versionNotSupported
  /-- A target of none of the four forms (RFC 9112 §3.2). -/
  | badTarget
  /-- A form the method does not allow (RFC 9112 §3.2.3, §3.2.4). -/
  | formMismatch
  /-- No `Host` in an HTTP/1.1 request (RFC 9112 §3.2). -/
  | missingHost
  /-- More than one `Host` field line (RFC 9112 §3.2). -/
  | multipleHost
  /-- A `Host` value that is not `uri-host [ ":" port ]` (RFC 9112 §3.2). -/
  | invalidHost
  /-- Invalid or faulty framing (RFC 9112 §6.1, §6.3). -/
  | badFraming
  /-- `chunked` applied more than once (RFC 9112 §6.1). -/
  | chunkedRepeated
  /-- A transfer coding the server does not implement (RFC 9112 §6.1). -/
  | unknownCoding (name : Bytes)
  deriving DecidableEq, Repr

/-- The status code answered for an error. -/
def RequestError.status : RequestError → Nat
  | .versionNotSupported => 505
  | .unknownCoding _ => 501
  | _ => 400

/-- A server's configuration: its framing profile, the transfer codings it implements besides
`chunked`, whether the connection is secured (the default scheme, RFC 9112 §3.3) and its
treatment of HTTP/1.0 `keep-alive`. -/
structure ServerConfig where
  profile : Profile := Profile.teWins
  implements : Bytes → Bool := fun _ => false
  secure : Bool := false
  keepAlive : KeepAlive := {}

/-- What a server knows about an acceptable request. -/
structure Context where
  /-- The method (RFC 9110 §9.1). -/
  method : Http.Method
  /-- The form of the target (RFC 9112 §3.2). -/
  form : TargetForm
  /-- The target URI (RFC 9112 §3.3). -/
  target : Http.Target
  /-- The framing of the body (RFC 9112 §6.3). -/
  framing : BodyLength
  /-- The connection may carry another request after the response (RFC 9112 §9.3). -/
  persistent : Bool
  deriving DecidableEq, Repr

/-- The target URI (RFC 9112 §3.3). -/
def targetUri (cfg : ServerConfig) (form : TargetForm) (target host : Bytes) : Http.Target :=
  let scheme := if cfg.secure then Http.Scheme.https else Http.Scheme.http
  match form with
  | .absolute =>
    match absoluteParts target with
    | some (s, a, pq) =>
      ⟨some (if s = ascii "http" then .http else if s = ascii "https" then .https else .other s),
        some a, some pq⟩
    | none => ⟨some scheme, some host, none⟩
  | .origin => ⟨some scheme, some host, some target⟩
  | .authority => ⟨none, some target, none⟩
  | .asterisk => ⟨some scheme, some host, none⟩

/-- Check a request head (RFC 9112 §2.3, §3, §6, §9.3; RFC 9110 §7.2). -/
def checkRequest (cfg : ServerConfig) (h : RequestHead) : Except RequestError Context :=
  let v := h.line.version
  let m := h.line.method
  let t := h.line.target
  let fs := h.fields
  if v.major ≠ 1 then .error .versionNotSupported else
  match targetForm m t with
  | none => .error .badTarget
  | some form =>
    if !formFits m form then .error .formMismatch else
    match fieldValues fs hostName with
    | [] => if v.atLeast11 then .error .missingHost
      else checkFraming v m form fs t []
    | [host] => if Http.Uri.isHttpAuthority host then checkFraming v m form fs t host
      else .error .invalidHost
    | _ :: _ :: _ => .error .multipleHost
where
  /-- The framing and coding checks, after the target and `Host`. -/
  checkFraming (v : Version) (m : Bytes) (form : TargetForm) (fs : List FieldLine)
      (t host : Bytes) : Except RequestError Context :=
    let framing := cfg.profile.frame v fs
    if framing = .invalid then .error .badFraming else
    match checkCodings cfg.implements (transferCodings fs) with
    | .chunkedRepeated => .error .chunkedRepeated
    | .unknown c => .error (.unknownCoding c)
    | .chunkedNotFinal => .error .badFraming
    | .ok => .ok
      { method := Http.Method.ofToken m
        form
        target := targetUri cfg form t host
        framing
        persistent := persists cfg.keepAlive v fs && !framingForcesClose v fs }

/-- What an accepted request satisfies (`checkRequest_ok`). -/
structure Accepted (cfg : ServerConfig) (h : RequestHead) (c : Context) : Prop where
  major : h.line.version.major = 1
  form : targetForm h.line.method h.line.target = some c.form
  fits : formFits h.line.method c.form = true
  host : ∃ host, (fieldValues h.fields hostName = [host] ∧ Http.Uri.isHttpAuthority host = true) ∨
    (fieldValues h.fields hostName = [] ∧ h.line.version.atLeast11 = false)
  framing : c.framing = cfg.profile.frame h.line.version h.fields
  framing_ne : c.framing ≠ .invalid
  codings : checkCodings cfg.implements (transferCodings h.fields) = .ok
  method : c.method = Http.Method.ofToken h.line.method
  target : ∃ host, c.target = targetUri cfg c.form h.line.target host
  persistent : c.persistent =
    (persists cfg.keepAlive h.line.version h.fields && !framingForcesClose h.line.version h.fields)

/-! ## The RFC 9110 message -/

/-- A field line as an RFC 9110 field line. -/
def FieldLine.toLine (f : FieldLine) : Http.Field.Line := ⟨f.name, f.value⟩

/-- The trailer fields a body carries (RFC 9112 §7.1.2). -/
def Body.trailers : Body → List FieldLine
  | .chunked c => c.trailers
  | _ => []

/-- The RFC 9110 request (§6) of a checked HTTP/1.1 request: control data from the context,
the header section, the content and the trailer section. -/
def toRequest (h : RequestHead) (b : Body) (c : Context) : Http.Request :=
  { control := ⟨c.method, c.target⟩
    headers := h.fields.map FieldLine.toLine
    content := b.payload
    trailers := b.trailers.map FieldLine.toLine }

/-! ## Trailers -/

/-- Fields that RFC 9110 §6.5.1 forbids in trailers (lowercase): message framing, routing,
request modifiers, authentication, response control data, and how to process the
content. -/
def trailerForbidden : List Bytes :=
  [ "transfer-encoding", "content-length", "host", "te", "trailer", "connection",
    "cache-control", "max-forwards", "expect", "range", "if-match", "if-none-match",
    "if-modified-since", "if-unmodified-since", "if-range", "authorization",
    "proxy-authorization", "www-authenticate", "proxy-authenticate", "set-cookie", "cookie",
    "age", "expires", "date", "location", "retry-after", "vary", "content-encoding",
    "content-type", "content-range" ].map ascii

/-- A trailer field may be merged into the header section. -/
def trailerMergeable (f : FieldLine) : Bool := !trailerForbidden.contains (lower f.name)

/-- The header section with the mergeable trailer fields appended (RFC 9110 §6.5.1). -/
def mergeTrailers (headers trailers : List FieldLine) : List FieldLine :=
  headers ++ trailers.filter trailerMergeable

end Silmaril.Net.Http1
