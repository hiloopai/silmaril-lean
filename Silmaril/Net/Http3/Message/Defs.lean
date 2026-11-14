module

public import Silmaril.Net.Http3.Stream.Defs
public import Silmaril.Net.Http2.Fields.Defs
public import Silmaril.Net.Http.Message.Defs

@[expose] public section

/-!
# HTTP/3 messages and the version-independent HTTP semantics (RFC 9114 §4.1–§4.3)

An HTTP/3 request stream carries one header section, the content and an optional trailer
section (`Silmaril.Net.Http3.Stream`). Once QPACK has decoded the field sections into field
lists (`Hpack.Entry`, shared with HPACK/QPACK), this module maps them to the RFC 9110
messages of `Silmaril.Net.Http` and back.

**Field and pseudo-header rules.** RFC 9114 §4.2 and §4.3 impose on HTTP/3 the same rules as
RFC 9113 §8.2–§8.3 for HTTP/2: lower-case field names without forbidden octets, field values
without NUL/CR/LF or surrounding whitespace, no connection-specific fields (including
`Transfer-Encoding`, §4.1: "the Transfer-Encoding header field MUST NOT be used"), `te` only
with `trailers`, pseudo-header fields first and known, the request pseudo-headers
`:method`/`:scheme`/`:authority`/`:path` with the CONNECT exception (§4.4), and exactly one
`:status` in a response. This module therefore *reuses* `Http2.validRequest`,
`Http2.validResponse` and `Http2.validRegular` rather than restating them; a request or
response that breaks them is malformed (§4.1.2). Pseudo-header fields MUST NOT appear in
trailer sections (§4.3): `trailersValid`. A `content-length` that differs from the content
length is malformed (§4.1.2): `Http2.contentLengthMatches`.

**Field section size (§4.2.2).** "The size of a field list is calculated based on the
uncompressed size of fields, including the length of the name and value in bytes plus an
overhead of 32 bytes for each field" — HPACK's `tableSize`. `withinLimit` checks it against
`SETTINGS_MAX_FIELD_SECTION_SIZE`.

**Mapping.** `requestOf` turns a valid header section, content and trailer section into an
`Http.Request` (method from `:method`, the target pieces from `:scheme`, `:authority` and
`:path`, the regular fields as field lines); `requestFields` is its inverse direction. The
extended CONNECT `:protocol` pseudo-header (RFC 9220) is not part of `Http2.validRequest`;
it is handled by `Silmaril.Net.Http3.ExtendedConnect`. `responseOf`/`responseFields` do the
same for responses, with `:status` as three decimal digits.

`requestOfParts` composes this with the request-stream reader through any field-section
decoder (QPACK in practice).
-/

namespace Silmaril.Net.Http3

open Silmaril.Net.Hpack Silmaril.Net.Http2 Silmaril.Net.Http

/-- The value of the first field named `n`. -/
def firstValue (fs : List Entry) (n : String) : Option (List UInt8) :=
  (fs.find? (·.name == ascii n)).map (·.value)

/-- The scheme named by a `:scheme` value. -/
def schemeOf (v : List UInt8) : Scheme :=
  if v = ascii "http" then .http else if v = ascii "https" then .https else .other v

/-- The `:scheme` value of a scheme. -/
def schemeBytes : Scheme → List UInt8
  | .http => ascii "http"
  | .https => ascii "https"
  | .other v => v

/-- A canonical scheme: `other v` is not `http` or `https`. -/
def schemeCanonical : Scheme → Prop
  | .other v => v ≠ ascii "http" ∧ v ≠ ascii "https"
  | _ => True

/-- A field line from a field. -/
def toLine (e : Entry) : Field.Line := ⟨e.name, e.value⟩

/-- A field from a field line. -/
def ofLine (l : Field.Line) : Entry := ⟨l.name, l.value⟩

/-- The regular (non-pseudo) fields, in order. -/
def regularFields (fs : List Entry) : List Entry := fs.filter fun e => !isPseudo e

/-- A trailer section: regular fields only, each valid (§4.3, §4.2). -/
def trailersValid (ts : List Entry) : Bool := ts.all validRegular

/-- The field list fits `SETTINGS_MAX_FIELD_SECTION_SIZE` (§4.2.2). -/
def withinLimit (s : Settings) (fs : List Entry) : Bool :=
  s.maxFieldSectionSize.all (tableSize fs ≤ ·)

/-- The request a valid header section, content and trailer section carry. -/
def requestOf (fs : List Entry) (content : List UInt8) (ts : List Entry) : Option Request :=
  if validRequest fs && trailersValid ts && contentLengthMatches fs content.length then
    (firstValue fs ":method").map fun m =>
      { control := ⟨Method.ofToken m, ⟨(firstValue fs ":scheme").map schemeOf,
          firstValue fs ":authority", firstValue fs ":path"⟩⟩
        headers := (regularFields fs).map toLine
        content := content
        trailers := ts.map toLine }
  else none

/-- An optional pseudo-header field. -/
def optField (n : String) : Option (List UInt8) → List Entry
  | none => []
  | some v => [⟨ascii n, v⟩]

/-- The pseudo-header fields of a request's control data, in the order `requestFields` puts
them. -/
def requestPseudoFields (r : Request) : List Entry :=
  ⟨ascii ":method", r.method.toToken⟩ :: optField ":scheme" (r.target.scheme.map schemeBytes) ++
    optField ":authority" r.target.authority ++ optField ":path" r.target.pathWithQuery

/-- The header section of a request: pseudo-header fields, then the field lines. -/
def requestFields (r : Request) : List Entry := requestPseudoFields r ++ r.headers.map ofLine

/-- The trailer section of a request. -/
def requestTrailers (r : Request) : List Entry := r.trailers.map ofLine

/-- Three decimal digits of a status code. -/
def statusDigits (s : Nat) : List UInt8 :=
  [(0x30 + s / 100 % 10).toUInt8, (0x30 + s / 10 % 10).toUInt8, (0x30 + s % 10).toUInt8]

/-- The status code of a `:status` value: exactly three decimal digits (RFC 9110 §15). -/
def parseStatus (v : List UInt8) : Option Nat :=
  match v with
  | [a, b, c] =>
    if [a, b, c].all (fun d => 0x30 ≤ d && d ≤ 0x39) then
      some ((a.toNat - 0x30) * 100 + (b.toNat - 0x30) * 10 + (c.toNat - 0x30))
    else none
  | _ => none

/-- The response a valid header section, content and trailer section carry. -/
def responseOf (fs : List Entry) (content : List UInt8) (ts : List Entry) : Option Response :=
  if validResponse fs && trailersValid ts && contentLengthMatches fs content.length then
    match (firstValue fs ":status").bind parseStatus with
    | none => none
    | some s => some
      { control := s, headers := (regularFields fs).map toLine, content := content,
        trailers := ts.map toLine }
  else none

/-- The header section of a response. -/
def responseFields (r : Response) : List Entry :=
  ⟨ascii ":status", statusDigits r.status⟩ :: r.headers.map ofLine

/-- A request stream's received parts, through a field-section decoder (QPACK in practice),
as an `Http.Request`. -/
def requestOfParts (decode : List UInt8 → Option (List Entry)) (p : Parts) : Option Request :=
  match decode p.header, p.trailer.map decode with
  | some fs, none => requestOf fs p.content []
  | some fs, some (some ts) => requestOf fs p.content ts
  | _, _ => none

end Silmaril.Net.Http3
