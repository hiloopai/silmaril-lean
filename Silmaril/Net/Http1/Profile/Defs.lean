module

public import Silmaril.Net.Http1.Connection.Defs

/-!
# Recipient profiles: compliant latitude, common noncompliance and request smuggling

RFC 9112 leaves a recipient some latitude in how it frames a request, and real
implementations take more. Request smuggling (RFC 9112 §11.2) happens when two
recipients on one path (a front end and a back end) frame the same octets differently, so
the back end sees a request the front end never saw. This module makes the framing choices
explicit as a `Profile`, so that compliant and noncompliant recipients are values of one type:

| Knob | Compliant values | Common noncompliance |
| --- | --- | --- |
| `clTe`: `Transfer-Encoding` and `Content-Length` both present (§6.3 rule 3) | `reject` (400), `teWins` (`Transfer-Encoding` overrides) | `clWins`: `Content-Length` wins (the CL.TE attack) |
| `dupCl`: several `Content-Length` values (§6.3 rule 5, RFC 9110 §8.6) | `strict`: equal values count as one, different ones are an error | `first`, `last`: pick one |
| `teMatch`: is the final coding `chunked`? (§7, §6.3 rule 4) | `final`: case-insensitive name of the final coding | `substring`: any element containing `chunked` (`xchunked`, `chunked-false`); `caseSensitive`: `Chunked` is not recognised, so `Transfer-Encoding` is ignored (the TE.TE attacks) |
| `http10Te`: `Transfer-Encoding` in an HTTP/1.0 message (§6.1) | `false`: the framing is faulty | `true`: honour it |
| `ignoreTe`: no `Transfer-Encoding` support (§6.1, a server MUST implement `chunked`) | `false` | `true` |

`Profile.frame p v fs` is the framing that a recipient with profile `p` gives a request with
version `v` and fields `fs`, and `rfcRequestFraming` the reference: RFC 9112 §6.3 with the
HTTP/1.0 rule of §6.1. `Profile.Compliant p` is the conjunction of the compliant columns.
`parseRequestWith p` reads a whole request as `p` frames it.

The laws (`Profile.Thms`):

* `frame_compliant`: a compliant profile frames every request as the reference does, or rejects it.
* `compliant_iff_safe`: conversely, **a profile is compliant exactly when it never accepts a
  request with a framing other than the reference one**. Each noncompliant knob has a
  witness request (`violationWitnesses`), so the table above is complete for this profile type.
* `parseRequestWith_compliant_agree`: two compliant recipients reading the same octets
  either agree on the request and on where it ends, or one of them rejects it. **Smuggling is
  impossible between compliant recipients** (at the framing level; the head grammar is the
  strict one of `Silmaril.Net.Http1.Message`, so line-level leniencies such as bare `LF`,
  `obs-fold` or whitespace before `:` are rejected before framing).
* `desync_clte`, `desync_tete`: concrete octets on which a noncompliant front end and a
  back end end the first request at different positions.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

/-- Both `Transfer-Encoding` and `Content-Length` (§6.3 rule 3). -/
inductive ClTe where
  | reject | teWins | clWins
  deriving DecidableEq, Repr

/-- Several `Content-Length` values (§6.3 rule 5). -/
inductive DupCl where
  | strict | first | last
  deriving DecidableEq, Repr

/-- Recognising the chunked coding. -/
inductive TeMatch where
  | final | substring | caseSensitive
  deriving DecidableEq, Repr

/-- The framing choices of a recipient. -/
structure Profile where
  clTe : ClTe
  dupCl : DupCl
  teMatch : TeMatch
  http10Te : Bool
  ignoreTe : Bool
  deriving DecidableEq, Repr

namespace Profile

/-- The compliant profiles (RFC 9112 §6.1, §6.3, RFC 9110 §8.6). -/
def Compliant (p : Profile) : Prop :=
  p.clTe ≠ .clWins ∧ p.dupCl = .strict ∧ p.teMatch = .final ∧ p.http10Te = false ∧
    p.ignoreTe = false

instance (p : Profile) : Decidable p.Compliant := inferInstanceAs (Decidable (_ ∧ _))

/-- The strictest recipient: reject both headers. -/
def strict : Profile := ⟨.reject, .strict, .final, false, false⟩
/-- A compliant recipient that lets `Transfer-Encoding` override `Content-Length`. -/
def teWins : Profile := ⟨.teWins, .strict, .final, false, false⟩
/-- `Content-Length` wins (a CL.TE front end). -/
def clWins : Profile := ⟨.clWins, .strict, .final, false, false⟩
/-- Any element containing `chunked` means chunked. -/
def teSubstring : Profile := ⟨.teWins, .strict, .substring, false, false⟩
/-- `Transfer-Encoding` is not implemented. -/
def teIgnored : Profile := ⟨.teWins, .strict, .final, false, true⟩
/-- The first of several `Content-Length` values. -/
def clFirst : Profile := ⟨.teWins, .first, .final, false, false⟩
/-- The last of several `Content-Length` values. -/
def clLast : Profile := ⟨.teWins, .last, .final, false, false⟩

/-- All profiles. -/
def all : List Profile := do
  let a ← [ClTe.reject, .teWins, .clWins]
  let b ← [DupCl.strict, .first, .last]
  let c ← [TeMatch.final, .substring, .caseSensitive]
  let d ← [false, true]
  let e ← [false, true]
  pure ⟨a, b, c, d, e⟩

/-- The value of one `Content-Length` element. -/
def clValue (v : Bytes) : Option (Option Nat) :=
  if v.all isDigit then some (some (decValue v)) else none

/-- `Content-Length` as the profile reads it. -/
def contentLength (p : Profile) (fs : List FieldLine) : Option (Option Nat) :=
  match p.dupCl, fieldElements fs contentLengthName with
  | .strict, _ => contentLength? fs
  | _, [] => some none
  | .first, v :: _ => clValue v
  | .last, v :: vs => clValue ((v :: vs).getLast (by simp))

/-- The framing from `Content-Length` alone (rules 5–7). -/
def clFrame (p : Profile) (fs : List FieldLine) : BodyLength :=
  match p.contentLength fs with
  | none => .invalid
  | some none => .none
  | some (some n) => .length n

/-- `l` occurs as a contiguous part of `m`. -/
def isInfixOf (l m : Bytes) : Bool := (List.range (m.length + 1)).any fun i => (m.drop i).take l.length = l

/-- Does the profile see the chunked coding? `none`: it does not recognise
`Transfer-Encoding` at all and ignores the field. -/
def teChunked (p : Profile) (fs : List FieldLine) : Option Bool :=
  match p.teMatch with
  | .final => some ((transferCodings fs).getLast? = some chunkedName)
  | .substring => some ((fieldElements fs transferEncodingName).any fun e => isInfixOf chunkedName (lower e))
  | .caseSensitive =>
    if ((fieldElements fs transferEncodingName).map fun e => trimOWS (e.takeWhile (· ≠ SEMI))).getLast?
        = some chunkedName then some true else none

/-- The framing of a request with version `v` and fields `fs`, as profile `p` reads it. -/
def frame (p : Profile) (v : Version) (fs : List FieldLine) : BodyLength :=
  if (transferCodings fs).isEmpty || p.ignoreTe then p.clFrame fs
  else if v.is10 && !p.http10Te then .invalid
  else match p.teChunked fs with
    | none => p.clFrame fs
    | some ch =>
      if (fieldElements fs contentLengthName).isEmpty then (if ch then .chunked else .invalid)
      else match p.clTe with
        | .reject => .invalid
        | .clWins => p.clFrame fs
        | .teWins => if ch then .chunked else .invalid

end Profile

/-- The reference request framing: RFC 9112 §6.3 rules 3–7 (`requestBodyLength`) with the
HTTP/1.0 rule of §6.1. -/
def rfcRequestFraming (v : Version) (fs : List FieldLine) : BodyLength :=
  if !(transferCodings fs).isEmpty && v.is10 then .invalid else requestBodyLength fs

/-- The profile accepts the framing of `(v, fs)` only as the reference does. -/
def Profile.SafeOn (p : Profile) (v : Version) (fs : List FieldLine) : Prop :=
  p.frame v fs = rfcRequestFraming v fs ∨ p.frame v fs = .invalid

instance (p : Profile) (v : Version) (fs : List FieldLine) : Decidable (p.SafeOn v fs) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- One witness request per noncompliant knob. -/
def violationWitnesses : List (Version × List FieldLine) :=
  [ -- `Content-Length` wins over `Transfer-Encoding`
    (Version.http11, [⟨ascii "Transfer-Encoding", ascii "chunked"⟩, ⟨ascii "Content-Length", ascii "5"⟩]),
    -- differing `Content-Length` values
    (Version.http11, [⟨ascii "Content-Length", ascii "5"⟩, ⟨ascii "Content-Length", ascii "6"⟩]),
    -- `xchunked`
    (Version.http11, [⟨ascii "Transfer-Encoding", ascii "xchunked"⟩]),
    -- `Chunked`
    (Version.http11, [⟨ascii "Transfer-Encoding", ascii "Chunked"⟩]),
    -- `Transfer-Encoding` in HTTP/1.0
    (⟨1, 0⟩, [⟨ascii "Transfer-Encoding", ascii "chunked"⟩]),
    -- `Transfer-Encoding` ignored
    (Version.http11, [⟨ascii "Transfer-Encoding", ascii "chunked"⟩]) ]

/-! ## Whole requests as a profile reads them -/

/-- Read a request at `i`, framed by profile `p`. -/
def parseRequestWith (p : Profile) (bs : ByteArray) (i : Nat) : Res (RequestHead × Body) :=
  match (Grammar.requestHead (bs.size + 1)).parse bs bs.size i with
  | .err e => .err e
  | .ok h j =>
    match parseBody (p.frame h.line.version h.fields) bs j with
    | .ok b k => .ok (h, b) k
    | .err e => .err e

/-- Two recipients **desynchronise** on `bs`: both accept a first request but end it at
different positions, so the next request each sees starts elsewhere. -/
def Desync (p q : Profile) (bs : ByteArray) : Prop :=
  ∃ r r' k k', parseRequestWith p bs 0 = .ok r k ∧ parseRequestWith q bs 0 = .ok r' k' ∧ k ≠ k'

/-! ## Smuggling witnesses -/

/-- A request with `Content-Length: 6` and `Transfer-Encoding: chunked`. -/
def clteHead : RequestHead :=
  ⟨⟨ascii "POST", ascii "/", Version.http11⟩,
    [⟨ascii "Host", ascii "a"⟩, ⟨ascii "Content-Length", ascii "6"⟩,
      ⟨ascii "Transfer-Encoding", ascii "chunked"⟩]⟩

/-- The empty chunked body `0 CRLF CRLF`. -/
def emptyChunked : Chunked := ⟨[], [], []⟩

/-- The CL.TE attack: the head, the empty chunked body, then `G` (the start of a request the
back end sees and the front end does not). -/
def clteOctets : Bytes := encRequestHead clteHead ++ encChunked emptyChunked ++ ascii "G"

/-- A request with `Content-Length: 6` and `Transfer-Encoding: xchunked`. -/
def teteHead : RequestHead :=
  ⟨⟨ascii "POST", ascii "/", Version.http11⟩,
    [⟨ascii "Host", ascii "a"⟩, ⟨ascii "Content-Length", ascii "6"⟩,
      ⟨ascii "Transfer-Encoding", ascii "xchunked"⟩]⟩

/-- The TE.TE attack with an obfuscated coding name. -/
def teteOctets : Bytes := encRequestHead teteHead ++ encChunked emptyChunked ++ ascii "G"

end Silmaril.Net.Http1
