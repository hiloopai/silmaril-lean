module

public import Silmaril.Net.Http.Message.Defs

@[expose] public section

/-!
# URI pieces for HTTP targets (RFC 3986, RFC 9110 §4, §7.1)

The pieces of a URI that WASI passes for a request (`Target`: scheme, authority,
path-with-query), with their RFC 3986 grammars and decidable checks:

* `scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )` (RFC 3986 §3.1), check `isScheme`;
* `pct-encoded = "%" HEXDIG HEXDIG` (§2.1), `unreserved` (§2.3), `sub-delims` (§2.2),
  `pchar = unreserved / pct-encoded / sub-delims / ":" / "@"` (§3.3), written as the class
  `isPcharOctet` (`unreserved / sub-delims / ":" / "@"`) alternated with `pct-encoded`
  (`pchar`; an ABNF alternation denotes a union, so regrouping its alternatives keeps the
  rule);
* `segment = *pchar` (§3.3), `absolute-path = 1*( "/" segment )` (RFC 9110 §4.1),
  `query = *( pchar / "/" / "?" )` (§3.4), and the path-with-query of an origin-form target,
  `absolute-path [ "?" query ]` (RFC 9110 §7.1, RFC 9112 §3.2.1);
* `reg-name = *( unreserved / pct-encoded / sub-delims )` (§3.2.2), `port = *DIGIT` (§3.2.3),
  and the authority of an `http`/`https` URI, `host [ ":" port ]` (RFC 9110 §4.2.1; a sender
  MUST NOT generate `userinfo`, §4.2.4). Hosts are `reg-name`s, which include IPv4 dotted
  decimal (`IPv4address` strings are `reg-name` strings); `IP-literal` hosts (`[` IPv6 `]`,
  §3.2.2) are not covered yet.

A run of octets of a class `p` and `pct-encoded` triples (`atoms p`, `*( p / pct-encoded )`)
is decided by the scanner `scanPct p`; every grammar above is reduced to it in `Uri/Thms.lean`.

Not covered yet: full URI references and resolution (§4, §5), normalization and comparison
(§6; RFC 9110 §4.2.3), IP literals, `userinfo`, the `absolute-form`, `authority-form` and
`asterisk-form` targets (RFC 9112 §3.2.2–§3.2.4).
-/

namespace Silmaril.Net.Http.Uri

open Silmaril.Formats.Grammar.Ebnf
open Silmaril.Net.Http.Abnf

/-! ## Character classes -/

/-- `unreserved = ALPHA / DIGIT / "-" / "." / "_" / "~"` (§2.3). -/
def isUnreserved (b : UInt8) : Bool :=
  isAlpha b || isDigit b || [0x2D, 0x2E, 0x5F, 0x7E].contains b

/-- `sub-delims = "!" / "$" / "&" / "'" / "(" / ")" / "*" / "+" / "," / ";" / "="` (§2.2). -/
def isSubDelim (b : UInt8) : Bool :=
  [0x21, 0x24, 0x26, 0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x3B, 0x3D].contains b

/-- The single-octet alternatives of `pchar`: `unreserved / sub-delims / ":" / "@"` (§3.3). -/
def isPcharOctet (b : UInt8) : Bool := isUnreserved b || isSubDelim b || b == 0x3A || b == 0x40

/-- The octets of a path: `pchar` octets and `"/"`. -/
def isPathOctet (b : UInt8) : Bool := isPcharOctet b || b == 0x2F

/-- The single-octet alternatives of `query`: `pchar` octets, `"/"` and `"?"` (§3.4). -/
def isQueryOctet (b : UInt8) : Bool := isPathOctet b || b == 0x3F

/-- The single-octet alternatives of `reg-name`: `unreserved / sub-delims` (§3.2.2). -/
def isRegNameOctet (b : UInt8) : Bool := isUnreserved b || isSubDelim b

/-- `ALPHA / DIGIT / "+" / "-" / "."`: the octets after the first of a scheme (§3.1). -/
def isSchemeOctet (b : UInt8) : Bool := isAlpha b || isDigit b || [0x2B, 0x2D, 0x2E].contains b

/-! ## Grammars -/

/-- `pct-encoded = "%" HEXDIG HEXDIG` (§2.1). -/
def pctEncoded {N : Type} : Expr UInt8 N := .sequence (.terminal 0x25) (.sequence hexdig hexdig)

/-- One octet of the class `p`, or a `pct-encoded` triple. -/
def atom {N : Type} (p : UInt8 → Bool) : Expr UInt8 N := .alternative (cls p) pctEncoded

/-- `*( p / pct-encoded )`. -/
def atoms {N : Type} (p : UInt8 → Bool) : Expr UInt8 N := .repetition (atom p)

/-- `pchar = unreserved / pct-encoded / sub-delims / ":" / "@"` (§3.3). -/
def pchar {N : Type} : Expr UInt8 N := atom isPcharOctet

/-- `segment = *pchar` (§3.3). -/
def segment {N : Type} : Expr UInt8 N := .repetition pchar

/-- `absolute-path = 1*( "/" segment )` (RFC 9110 §4.1). -/
def absolutePath {N : Type} : Expr UInt8 N := Expr.oneOrMore (.sequence (.terminal 0x2F) segment)

/-- `query = *( pchar / "/" / "?" )` (§3.4). -/
def query {N : Type} : Expr UInt8 N := atoms isQueryOctet

/-- `absolute-path [ "?" query ]` (RFC 9110 §7.1, RFC 9112 §3.2.1 `origin-form`). -/
def pathWithQuery {N : Type} : Expr UInt8 N :=
  .sequence absolutePath (Expr.optional (.sequence (.terminal 0x3F) query))

/-- `reg-name = *( unreserved / pct-encoded / sub-delims )` (§3.2.2). -/
def regName {N : Type} : Expr UInt8 N := atoms isRegNameOctet

/-- `port = *DIGIT` (§3.2.3). -/
def port {N : Type} : Expr UInt8 N := .repetition digit

/-- The authority of an `http` URI: `host [ ":" port ]` (RFC 9110 §4.2.1), hosts as
`reg-name`. -/
def httpAuthority {N : Type} : Expr UInt8 N :=
  .sequence regName (Expr.optional (.sequence (.terminal 0x3A) port))

/-- `scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )` (§3.1). -/
def scheme {N : Type} : Expr UInt8 N := .sequence alpha (.repetition (cls isSchemeOctet))

/-! ## Checks -/

/-- Scan a run of octets of the class `p` and `pct-encoded` triples (structural, so that it
evaluates by `decide`). -/
def scanPct (p : UInt8 → Bool) : List UInt8 → Bool
  | [] => true
  | [x] => x != 0x25 && p x
  | [x, y] => x != 0x25 && p x && y != 0x25 && p y
  | x :: y :: z :: rest =>
    if x = 0x25 then isHexDig y && isHexDig z && scanPct p rest
    else p x && scanPct p (y :: z :: rest)

/-- The check of `absolute-path`. -/
def isAbsolutePath (xs : List UInt8) : Bool := xs.head? == some 0x2F && scanPct isPathOctet xs

/-- The check of `query`. -/
def isQuery (xs : List UInt8) : Bool := scanPct isQueryOctet xs

/-- Split at the first `c`: the part before it, and the part after it if there is a `c`. -/
def splitAt? (c : UInt8) : List UInt8 → List UInt8 × Option (List UInt8)
  | [] => ([], none)
  | x :: xs => if x = c then ([], some xs) else (x :: (splitAt? c xs).1, (splitAt? c xs).2)

/-- The check of `absolute-path [ "?" query ]`. -/
def isPathWithQuery (xs : List UInt8) : Bool :=
  isAbsolutePath (splitAt? 0x3F xs).1 && (splitAt? 0x3F xs).2.all isQuery

/-- The check of `reg-name`. -/
def isRegName (xs : List UInt8) : Bool := scanPct isRegNameOctet xs

/-- The check of `port`. -/
def isPort (xs : List UInt8) : Bool := xs.all isDigit

/-- The check of `host [ ":" port ]`. -/
def isHttpAuthority (xs : List UInt8) : Bool :=
  isRegName (splitAt? 0x3A xs).1 && (splitAt? 0x3A xs).2.all isPort

/-- The check of `scheme`. -/
def isScheme : List UInt8 → Bool
  | [] => false
  | x :: rest => isAlpha x && rest.all isSchemeOctet

end Silmaril.Net.Http.Uri

namespace Silmaril.Net.Http

open Silmaril.Net.Http.Uri

/-- The name of a scheme (RFC 9110 §4.2.1, §4.2.2). -/
def Scheme.name : Scheme → List UInt8
  | .http => Method.ascii "http"
  | .https => Method.ascii "https"
  | .other n => n

/-- A valid scheme: its name is a `scheme` (RFC 3986 §3.1). -/
def Scheme.isValid (s : Scheme) : Bool := isScheme s.name

/-- A valid target: each present piece is valid (RFC 9110 §4.2, §7.1). -/
def Target.isValid (t : Target) : Bool :=
  t.scheme.all Scheme.isValid && t.authority.all isHttpAuthority &&
    t.pathWithQuery.all isPathWithQuery

end Silmaril.Net.Http
