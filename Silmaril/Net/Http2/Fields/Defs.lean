module

public import Silmaril.Net.Hpack.Table.Defs

@[expose] public section

/-!
# HTTP/2 field sections: validity and pseudo-header fields (RFC 9113 §8.1–§8.3, §8.5)

An HTTP/2 message's header section is the list of fields its decoded field block carries
(`Silmaril.Net.Hpack.Entry`). RFC 9113 makes a request or response *malformed* (§8.1.1) when
its fields break the rules below; "intermediaries that process HTTP requests or responses …
MUST NOT forward a malformed request or response" (§8.1.1), and these rules are what prevents
request smuggling when HTTP/2 messages are translated to HTTP/1.1 (§8.2.1, §10.3). The
checks:

* **Field names (§8.2.1).** No octet in `0x00–0x20`, `0x41–0x5a` (upper case) or `0x7f–0xff`;
  no colon except the leading one of a pseudo-header field.
* **Field values (§8.2.1).** No NUL, LF or CR anywhere, no leading or trailing SP or HTAB.
* **Connection-specific fields (§8.2.2).** `connection`, `proxy-connection`, `keep-alive`,
  `transfer-encoding` and `upgrade` are malformed; `te` only with the value `trailers`.
* **Pseudo-header fields (§8.3).** They come before every regular field, are not repeated,
  and are the request ones (`:method`, `:scheme`, `:authority`, `:path`) in a request and
  `:status` in a response; unknown pseudo-header fields are malformed. A request carries
  exactly one `:method`, `:scheme` and `:path` (non-empty for `http`/`https`), except CONNECT
  (§8.5), which carries `:method` and `:authority` and omits `:scheme` and `:path`. A response
  carries exactly one `:status`.
* **Content length (§8.1.1).** A `content-length` field that differs from the sum of the
  DATA payload lengths makes the message malformed (`contentLengthMatches`).

Not covered yet: the `:protocol` pseudo-header of extended CONNECT (RFC 8441, RFC 9220), the
`host`/`:authority` consistency rule of §8.3.1, the cookie-crumb rule (§8.2.3), and the
mapping to the version-independent `Silmaril.Net.Http.Request` (roadmap,
docs/projects/http.md).
-/

namespace Silmaril.Net.Http2

open Silmaril.Net.Hpack

/-- `':'`. -/
def colon : UInt8 := 0x3a

/-- An octet allowed in a field name (§8.2.1), not counting the colon rule. -/
def isNameOctet (b : UInt8) : Bool := !(b ≤ 0x20 || (0x41 ≤ b && b ≤ 0x5a) || 0x7f ≤ b)

/-- A pseudo-header field: its name starts with a colon (§8.3). -/
def isPseudo (e : Entry) : Bool := e.name.head? == some colon

/-- A valid field name (§8.2.1): non-empty, allowed octets, and a colon only in first position
for a pseudo-header field. -/
def validName (n : List UInt8) : Bool :=
  !n.isEmpty && n.all isNameOctet && !n.tail.contains colon

/-- A valid field value (§8.2.1). -/
def validValue (v : List UInt8) : Bool :=
  v.all (fun b => b != 0x00 && b != 0x0a && b != 0x0d) &&
    v.head?.all (fun b => b != 0x20 && b != 0x09) &&
    v.getLast?.all (fun b => b != 0x20 && b != 0x09)

/-- The connection-specific field names (§8.2.2). -/
def connectionSpecific : List (List UInt8) :=
  ["connection", "proxy-connection", "keep-alive", "transfer-encoding", "upgrade"].map ascii

/-- A regular field allowed in HTTP/2 (§8.2.1, §8.2.2). -/
def validRegular (e : Entry) : Bool :=
  validName e.name && validValue e.value && !isPseudo e &&
    !connectionSpecific.contains e.name &&
    (e.name != ascii "te" || e.value == ascii "trailers")

/-- Pseudo-header fields first (§8.3): the section is pseudo fields then regular fields. -/
def pseudoFirst (fs : List Entry) : Bool :=
  (fs.dropWhile isPseudo).all (fun e => !isPseudo e)

/-- The values of the pseudo-header field named `n`. -/
def pseudoValues (fs : List Entry) (n : String) : List (List UInt8) :=
  (fs.filter fun e => e.name == ascii n).map Entry.value

/-- The pseudo-header names allowed in requests (§8.3.1) and responses (§8.3.2). -/
def requestPseudo : List (List UInt8) := [":method", ":scheme", ":authority", ":path"].map ascii
def responsePseudo : List (List UInt8) := [":status"].map ascii

/-- Every pseudo-header field is one of `allowed` and none is repeated (§8.3). -/
def pseudoKnownOnce (allowed : List (List UInt8)) (fs : List Entry) : Bool :=
  let ps := (fs.filter isPseudo).map Entry.name
  ps.all allowed.contains && allowed.all (fun n => ps.count n ≤ 1)

/-- Regular fields valid, pseudo fields first and valid in value. -/
def validSection (allowed : List (List UInt8)) (fs : List Entry) : Bool :=
  pseudoFirst fs && pseudoKnownOnce allowed fs &&
    fs.all (fun e => if isPseudo e then validValue e.value else validRegular e)

/-- A well-formed request header section (§8.3.1, §8.5). -/
def validRequest (fs : List Entry) : Bool :=
  validSection requestPseudo fs &&
    match pseudoValues fs ":method" with
    | [m] =>
      if m == ascii "CONNECT" then
        (pseudoValues fs ":authority").length == 1 && (pseudoValues fs ":scheme").isEmpty &&
          (pseudoValues fs ":path").isEmpty
      else
        match pseudoValues fs ":scheme", pseudoValues fs ":path" with
        | [s], [p] => !((s == ascii "http" || s == ascii "https") && p.isEmpty)
        | _, _ => false
    | _ => false

/-- A well-formed response header section (§8.3.2): exactly one `:status`. -/
def validResponse (fs : List Entry) : Bool :=
  validSection responsePseudo fs && (pseudoValues fs ":status").length == 1

/-- §8.1.1: a `content-length` (if any) equals the total DATA payload length. Values that are
not a decimal number are malformed. -/
def contentLengthMatches (fs : List Entry) (dataLength : Nat) : Bool :=
  (fs.filter fun e => e.name == ascii "content-length").all fun e =>
    !e.value.isEmpty && e.value.all (fun b => 0x30 ≤ b && b ≤ 0x39) &&
      e.value.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0 == dataLength

/-! ## Translation to HTTP/1.1 field lines -/

/-- An HTTP/1.1 field line for a regular field: `name ": " value` (RFC 9112 §5), without the
CRLF. -/
def h1Line (e : Entry) : List UInt8 := e.name ++ [colon, 0x20] ++ e.value

/-- Split at the first colon (how an HTTP/1.1 recipient finds the field name, RFC 9112 §5). -/
def breakColon : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | b :: bs => if b == colon then ([], bs) else
    let (n, r) := breakColon bs
    (b :: n, r)

end Silmaril.Net.Http2
