module

public import Silmaril.Net.Http.Field.Defs

@[expose] public section

/-!
# HTTP request methods (RFC 9110 §9)

`method = token` (§9.1), case-sensitive. The methods of §9.3 (`GET`, `HEAD`, `POST`, `PUT`,
`DELETE`, `CONNECT`, `OPTIONS`, `TRACE`) and `PATCH` (RFC 5789 §2, also a case of WASI's
`method` variant) are constructors; every other token is `other t`.

Properties (§9.2):

* **safe** (§9.2.1): "Of the request methods defined by this specification, the GET, HEAD,
  OPTIONS, and TRACE methods are defined to be safe";
* **idempotent** (§9.2.2): "the PUT, DELETE, and safe request methods … are idempotent";
* **cacheable** (§9.2.3): "This specification defines caching semantics for GET, HEAD, and
  POST, although the overwhelming majority of cache implementations only support GET and
  HEAD".

`PATCH` is neither safe nor idempotent (RFC 5789 §2). An unregistered method has none of the
properties (a client cannot rely on them; the method registry, §16.1, records them per method).
`Method.isSafe` etc. are the checks, `Method.Safe` etc. the properties.
-/

namespace Silmaril.Net.Http

open Silmaril.Net.Http.Field

/-- A request method (§9). -/
inductive Method where
  | get | head | post | put | delete | connect | options | trace
  /-- `PATCH` (RFC 5789). -/
  | patch
  /-- An extension method, by its token (canonical when it is not one of the names above). -/
  | other (token : List UInt8)
  deriving DecidableEq, Repr, Inhabited

namespace Method

/-- The octets of an ASCII string literal. -/
def ascii (s : String) : List UInt8 := s.toList.map (fun c => c.toNat.toUInt8)

/-- The method token as sent in a request (§9.1: case-sensitive, standard methods are
upper case). -/
def toToken : Method → List UInt8
  | get => ascii "GET" | head => ascii "HEAD" | post => ascii "POST" | put => ascii "PUT"
  | delete => ascii "DELETE" | connect => ascii "CONNECT" | options => ascii "OPTIONS"
  | trace => ascii "TRACE" | patch => ascii "PATCH" | other t => t

/-- The named methods. -/
def named : List Method := [get, head, post, put, delete, connect, options, trace, patch]

/-- The method of a token (§9.1: case-sensitive). -/
def ofToken (t : List UInt8) : Method :=
  match named.find? (fun m => m.toToken == t) with
  | some m => m
  | none => other t

/-- A canonical method: `other t` is used only for tokens that are not named methods. -/
def Canonical : Method → Prop
  | other t => ∀ m ∈ named, m.toToken ≠ t
  | _ => True

/-- A valid method: its token is a `token` (§9.1). -/
def isValid (m : Method) : Bool := isToken m.toToken

/-- Safe (§9.2.1). -/
def isSafe : Method → Bool
  | get | head | options | trace => true
  | _ => false

/-- Idempotent (§9.2.2): `PUT`, `DELETE` and the safe methods. -/
def isIdempotent : Method → Bool
  | put | delete => true
  | m => m.isSafe

/-- Cacheable (§9.2.3). -/
def isCacheable : Method → Bool
  | get | head | post => true
  | _ => false

/-- The method may have request content with defined semantics (§9.3: GET, HEAD, DELETE,
CONNECT content "has no generally defined semantics"; TRACE "MUST NOT send content"). -/
def contentDefined : Method → Bool
  | post | put | patch | options => true
  | other _ => true
  | _ => false

end Method

end Silmaril.Net.Http
