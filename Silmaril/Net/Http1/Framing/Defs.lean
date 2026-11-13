module

public import Silmaril.Net.Http1.Chunked.Defs

/-!
# HTTP/1.1 message framing: the message body length (RFC 9112 §6)

Where does a message body end? RFC 9112 §6.3 answers from the head (and, for responses,
the request method). `requestBodyLength` and `responseBodyLength` transcribe its rules, in
order:

1. A response to `HEAD`, and any `1xx`, `204` or `304` response, has no body (rule 1).
2. A `2xx` response to `CONNECT` turns the connection into a tunnel (rule 2).
3. `Transfer-Encoding` overrides `Content-Length` (rule 3). If its final coding is
   `chunked`, the body is chunked (rule 4); otherwise a response is read until the
   connection closes and a request is invalid (`400`, rule 4).
4. An invalid `Content-Length` makes the message invalid (rule 5); a list of identical
   values counts as one (RFC 9110 §8.6, the "MAY ... replace that invalid field value with a
   single instance" option).
5. A valid `Content-Length` gives the length (rule 6).
6. Otherwise a request has no body (rule 7) and a response is read until close (rule 8).

`Content-Length` and `Transfer-Encoding` are found case-insensitively (RFC 9110 §5.1); their
values are comma-separated lists (RFC 9110 §5.3, §5.6.1) whose elements are trimmed and whose
empty elements are ignored. A transfer coding is compared by its name, case-insensitively
(RFC 9112 §7, "transfer-coding names are case-insensitive"), ignoring parameters.

`parseRequest` and `parseResponse` read a whole message (head and body) from a buffer and
return the position after it, where the next message on a persistent connection starts
(RFC 9112 §9.3). Not modelled yet: the HTTP/1.0 rules of §6.1 (a message with
`Transfer-Encoding` from an HTTP/1.0 sender "MUST be treated as if the message were
faulty"), the `Connection` header and connection management (§9), and transfer codings
other than `chunked` (§7.2–§7.4).
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

/-- `","`. -/
abbrev COMMA : UInt8 := 0x2C

/-- The values of the fields named `name`, compared case-insensitively, in order. -/
def fieldValues (fs : List FieldLine) (name : Bytes) : List Bytes :=
  fs.filterMap fun f => if lower f.name = lower name then some f.value else none

/-- Split at `sep`. -/
def splitOn (sep : UInt8) : Bytes → List Bytes
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitOn sep cs
    else match splitOn sep cs with
      | [] => [[c]]
      | w :: ws => (c :: w) :: ws

/-- The elements of a comma-separated list value (`#element`, RFC 9110 §5.6.1), trimmed,
empty elements dropped. -/
def listElements (v : Bytes) : List Bytes :=
  ((splitOn COMMA v).map trimOWS).filter (· ≠ [])

/-- All list elements of the fields named `name` (RFC 9110 §5.3: the field lines combine
into one comma-separated list). -/
def fieldElements (fs : List FieldLine) (name : Bytes) : List Bytes :=
  (fieldValues fs name).flatMap listElements

/-- `content-length`. -/
def contentLengthName : Bytes := ascii "content-length"
/-- `transfer-encoding`. -/
def transferEncodingName : Bytes := ascii "transfer-encoding"
/-- `chunked`. -/
def chunkedName : Bytes := ascii "chunked"

/-- The `Content-Length` (RFC 9110 §8.6): `some none` if absent, `some (some n)` if every
element is `1*DIGIT` of the same value `n`, `none` (invalid) otherwise. -/
def contentLength? (fs : List FieldLine) : Option (Option Nat) :=
  match fieldElements fs contentLengthName with
  | [] => some none
  | v :: vs =>
    if v.all isDigit && vs.all (· = v) then some (some (decValue v)) else none

/-- The transfer codings, in the order applied, by name (lowercase, parameters dropped). -/
def transferCodings (fs : List FieldLine) : List Bytes :=
  (fieldElements fs transferEncodingName).map fun e => lower (trimOWS (e.takeWhile (· ≠ SEMI)))

/-- The framing of a message body (RFC 9112 §6.3). -/
inductive BodyLength where
  /-- No body. -/
  | none
  /-- The connection becomes a tunnel (a `2xx` response to `CONNECT`). -/
  | tunnel
  /-- The chunked transfer coding (§7.1). -/
  | chunked
  /-- Exactly `n` octets (`Content-Length`). -/
  | length (n : Nat)
  /-- The octets until the connection closes (responses only). -/
  | close
  /-- The framing is invalid: the message must be rejected. -/
  | invalid
  deriving DecidableEq, Repr

/-- Rules 3–8 of §6.3, for a message whose body is not excluded by rules 1–2; `noLength`
is what a message with neither header gets (no body for requests, until close for
responses), `badCoding` what a final coding other than `chunked` gives. -/
def bodyLengthOfFields (fs : List FieldLine) (noLength badCoding : BodyLength) : BodyLength :=
  match transferCodings fs with
  | [] =>
    match contentLength? fs with
    | none => .invalid
    | some none => noLength
    | some (some n) => .length n
  | tc => if tc.getLast? = some chunkedName then .chunked else badCoding

/-- The body length of a request (RFC 9112 §6.3 rules 3–7). -/
def requestBodyLength (fs : List FieldLine) : BodyLength :=
  bodyLengthOfFields fs .none .invalid

/-- `HEAD` and `CONNECT`. -/
def methodHEAD : Bytes := ascii "HEAD"
def methodCONNECT : Bytes := ascii "CONNECT"

/-- The body length of a response to a request with method `method` (§6.3 rules 1–8). -/
def responseBodyLength (method : Bytes) (code : Nat) (fs : List FieldLine) : BodyLength :=
  if method = methodHEAD ∨ code / 100 = 1 ∨ code = 204 ∨ code = 304 then .none
  else if method = methodCONNECT ∧ code / 100 = 2 then .tunnel
  else bodyLengthOfFields fs .close .close

/-! ## Whole messages -/

/-- A message body as framed on the wire. -/
inductive Body where
  | none
  | content (b : Bytes)
  | chunked (c : Chunked)
  /-- A close-delimited body (the rest of the input), or the start of tunnel data. -/
  | close (b : Bytes)
  deriving DecidableEq, Repr

/-- The content a body carries (RFC 9110 §6.4). -/
def Body.payload : Body → Bytes
  | .none => []
  | .content b => b
  | .chunked c => c.content
  | .close b => b

/-- Read the body framed by `len`, starting at `j`. -/
def parseBody (len : BodyLength) (bs : ByteArray) (j : Nat) : Res Body :=
  match len with
  | .none | .tunnel => .ok .none j
  | .length n => if j + n ≤ bs.size then .ok (.content (bs.extract j (j + n)).data.toList) (j + n)
    else .err ⟨j, .eof⟩
  | .chunked =>
    match parseChunked bs j with
    | .ok c k => .ok (.chunked c) k
    | .err e => .err e
  | .close => .ok (.close (bs.extract j bs.size).data.toList) bs.size
  | .invalid => .err ⟨j, .other "invalid message framing (RFC 9112 §6.3)"⟩

/-- Read a request (head and body) starting at position `i`: the request and the position
after it, where the next request of a persistent connection starts (RFC 9112 §9.3). -/
def parseRequestAt (bs : ByteArray) (i : Nat) : Res (RequestHead × Body) :=
  match (Grammar.requestHead (bs.size + 1)).parse bs bs.size i with
  | .err e => .err e
  | .ok h j =>
    match parseBody (requestBodyLength h.fields) bs j with
    | .ok b k => .ok (h, b) k
    | .err e => .err e

/-- Read a response, starting at position `i`, to a request with method `method`. -/
def parseResponseAt (method : Bytes) (bs : ByteArray) (i : Nat) : Res (ResponseHead × Body) :=
  match (Grammar.responseHead (bs.size + 1)).parse bs bs.size i with
  | .err e => .err e
  | .ok h j =>
    match parseBody (responseBodyLength method h.line.code h.fields) bs j with
    | .ok b k => .ok (h, b) k
    | .err e => .err e

/-- Read a request at the start of `bs`. -/
def parseRequest (bs : ByteArray) : Res (RequestHead × Body) := parseRequestAt bs 0

/-- Read a response at the start of `bs`. -/
def parseResponse (method : Bytes) (bs : ByteArray) : Res (ResponseHead × Body) :=
  parseResponseAt method bs 0

/-- The octets of a body. -/
def encBody : Body → Bytes
  | .none => []
  | .content b => b
  | .chunked c => encChunked c
  | .close b => b

/-- A body agrees with the framing its head announces. -/
def Body.Fits : BodyLength → Body → Prop
  | .none, .none => True
  | .length n, .content b => b.length = n
  | .chunked, .chunked c => c.Valid
  | _, _ => False

def encRequest (h : RequestHead) (b : Body) : Bytes := encRequestHead h ++ encBody b

def encResponse (h : ResponseHead) (b : Body) : Bytes := encResponseHead h ++ encBody b

end Silmaril.Net.Http1
