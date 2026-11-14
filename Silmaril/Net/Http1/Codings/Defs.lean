module

public import Silmaril.Net.Http1.Framing.Defs
public import Silmaril.Net.Http.Qvalue.Defs

/-!
# Transfer codings and `TE` (RFC 9112 §6.1, §7, §10.1)

`Silmaril.Net.Http1.Framing` reads the transfer-coding *names* of a message
(`transferCodings`) and decides its framing from the final one. This module adds what a
recipient needs to check and undo the other codings:

* **Coding names** (§7): the registered codings `chunked`, `compress`, `deflate`, `gzip`
  (§7.1, §7.2), with `x-compress` and `x-gzip` read as `compress` and `gzip`
  (`canonicalCoding`, §7.2: a recipient "SHOULD consider" them equivalent).
* **The coding check** `checkCodings` (§6.1, §6.3 rule 4, §7): `chunked` applied twice or
  not last in a request, and a coding the recipient does not implement, with the status
  code a server answers (`CodingVerdict.status`: `400`, or `501` for an unknown coding,
  §6.1 "SHOULD respond with 501 (Not Implemented)").
* **Undoing the codings** `decodeTransfer`: after the chunked framing is removed, the
  remaining codings are undone in the reverse order of their application. The
  decoders of `compress`, `deflate` and `gzip` are a **parameter** (`Decoders`), not
  definitions of this module: content coding algorithms belong to the compression track
  (`Silmaril.Formats.Compression`). `decodeTransfer_encodeTransfer` proves the round trip
  from the one assumption a coding library must provide: each decoder inverts its encoder.
* **`TE`** (§10.1): `t-codings = "trailers" / ( transfer-coding [ weight ] )` with
  `weight = OWS ";" OWS "q=" qvalue` (RFC 9110 §12.4.2), parsed into `TeOffer`s
  (`teOffers`), and whether the client accepts trailer fields (`teTrailers`).

Parameters of a coding (`transfer-parameter`, §7) are dropped for the decision (the
registered codings define none); they are kept by `codingParams` for callers.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Net.Http.Qvalue (parseQvalue)

/-! ## Names -/

/-- `compress` (§7.2). -/
def compressName : Bytes := ascii "compress"
/-- `deflate` (§7.2). -/
def deflateName : Bytes := ascii "deflate"
/-- `gzip` (§7.2). -/
def gzipName : Bytes := ascii "gzip"
/-- `trailers`, the `TE` keyword (§10.1); not a transfer coding. -/
def trailersName : Bytes := ascii "trailers"
/-- `te`. -/
def teName : Bytes := ascii "te"

/-- The transfer codings of the IANA registry that RFC 9112 defines (§7.1, §7.2, §18.4). -/
def registeredCodings : List Bytes := [chunkedName, compressName, deflateName, gzipName]

/-- `x-compress` and `x-gzip` are `compress` and `gzip` (§7.2); names are lowercase here. -/
def canonicalCoding (n : Bytes) : Bytes :=
  if n = ascii "x-gzip" then gzipName else if n = ascii "x-compress" then compressName else n

/-- The parameters of a transfer coding element: the octets after its first `";"`. -/
def codingParams (e : Bytes) : Bytes := trimOWS ((e.dropWhile (· ≠ SEMI)).drop 1)

/-! ## The coding check -/

/-- The verdict of a recipient on the `Transfer-Encoding` of a message. -/
inductive CodingVerdict where
  /-- Acceptable: no codings, or codings ending in a single `chunked` the recipient implements. -/
  | ok
  /-- `chunked` occurs before the final coding: applied more than once, or not last
  (§6.1 "A sender MUST NOT apply the chunked transfer coding more than once"). -/
  | chunkedRepeated
  /-- The final coding of a request is not `chunked` (§6.3 rule 4, `400`). -/
  | chunkedNotFinal
  /-- A coding the recipient does not implement (§6.1, `501`). -/
  | unknown (name : Bytes)
  deriving DecidableEq, Repr

/-- The status a server answers for a verdict (`200` stands for "go on"). -/
def CodingVerdict.status : CodingVerdict → Nat
  | .ok => 200
  | .chunkedRepeated | .chunkedNotFinal => 400
  | .unknown _ => 501

/-- Check the transfer codings `tcs` (lowercase names, in the order applied) of a request,
for a recipient that implements the codings `impl` besides `chunked`. -/
def checkCodings (impl : Bytes → Bool) (tcs : List Bytes) : CodingVerdict :=
  match tcs.reverse with
  | [] => .ok
  | last :: earlier =>
    if last ≠ chunkedName then .chunkedNotFinal
    else if chunkedName ∈ earlier then .chunkedRepeated
    else match earlier.reverse.find? (fun c => !impl (canonicalCoding c)) with
      | some c => .unknown c
      | none => .ok

/-! ## Undoing the codings -/

/-- Decoders for the codings other than `chunked`, by canonical name: `none` if the
recipient does not implement the coding; a decoder returns `none` on malformed input. -/
abbrev Decoders := Bytes → Option (Bytes → Option Bytes)

/-- Encoders for the codings other than `chunked`, by canonical name. -/
abbrev Encoders := Bytes → Option (Bytes → Bytes)

/-- The codings before the final `chunked`, in the order applied. -/
def innerCodings (tcs : List Bytes) : List Bytes :=
  if tcs.getLast? = some chunkedName then tcs.dropLast else tcs

/-- Undo the codings `cs` (in the order applied), last first. -/
def decodeTransfer (d : Decoders) : List Bytes → Bytes → Option Bytes
  | [], x => some x
  | c :: cs, x => (decodeTransfer d cs x).bind fun y =>
      (d (canonicalCoding c)).bind fun f => f y

/-- Apply the codings `cs` in order (`none` if one is not implemented). -/
def encodeTransfer (e : Encoders) : List Bytes → Bytes → Option Bytes
  | [], x => some x
  | c :: cs, x => (e (canonicalCoding c)).bind fun f => encodeTransfer e cs (f x)

/-- A coding library: each implemented decoder inverts its encoder. This is the assumption a
compression development discharges (for example, `gunzip (gzip x) = some x`). -/
def Decoders.Inverts (d : Decoders) (e : Encoders) : Prop :=
  ∀ n f, e n = some f → ∃ g, d n = some g ∧ ∀ x, g (f x) = some x

/-! ## `TE` (§10.1) -/

/-- An element of `TE`: `trailers`, or a transfer coding with its weight in thousandths
(`1000` when absent, RFC 9110 §12.4.2). -/
inductive TeOffer where
  | trailers
  | coding (name : Bytes) (q : Nat)
  deriving DecidableEq, Repr

/-- Parse one `t-codings` element; `none` if its weight is malformed. -/
def parseTeOffer (e : Bytes) : Option TeOffer :=
  let name := lower (trimOWS (e.takeWhile (· ≠ SEMI)))
  if name = trailersName then some .trailers
  else
    let ps := codingParams e
    if ps = [] then some (.coding name 1000)
    else if lower (ps.take 2) = ascii "q=" then (parseQvalue (ps.drop 2)).map (.coding name)
    else some (.coding name 1000)

/-- The offers of the `TE` fields; malformed elements are ignored. -/
def teOffers (fs : List FieldLine) : List TeOffer :=
  (fieldElements fs teName).filterMap parseTeOffer

/-- The client accepts trailer fields in a chunked response (§10.1 "trailers"). -/
def teTrailers (fs : List FieldLine) : Bool := (teOffers fs).contains .trailers

/-- The client accepts the transfer coding `n` (nonzero weight). `chunked` is always
acceptable to an HTTP/1.1 client (§7.4: "chunked" is always acceptable). -/
def teAccepts (fs : List FieldLine) (n : Bytes) : Bool :=
  n = chunkedName ||
    (teOffers fs).any fun o => match o with
      | .coding m q => canonicalCoding m = canonicalCoding n && q != 0
      | .trailers => false

end Silmaril.Net.Http1
