module

public import Silmaril.Net.Http1.Scan.Thms
public import Silmaril.Net.Http1.Syntax.Defs

/-!
# HTTP/1.1 message heads: syntax, parser and serializer

RFC 9112 §2.1:

```
HTTP-message   = start-line CRLF
                 *( field-line CRLF )
                 CRLF
                 [ message-body ]
start-line     = request-line / status-line
```

This module covers everything before the body: the *head*. A server parses request heads and
a client response heads (RFC 9112 §2.2: "a client knows which"), so there are two entry
points, `parseRequestHead` and `parseResponseHead`, with serializers `encRequestHead` and
`encResponseHead`.

| Element | ABNF | RFC 9112 |
| --- | --- | --- |
| `Version` | `HTTP-version = HTTP-name "/" DIGIT "." DIGIT`, `HTTP-name = %s"HTTP"` | §2.3 |
| `RequestLine` | `request-line = method SP request-target SP HTTP-version` | §3 |
| `StatusLine` | `status-line = HTTP-version SP status-code SP [ reason-phrase ]` | §4 |
| `FieldLine` | `field-line = field-name ":" OWS field-value OWS` | §5 |

Choices, each allowed by RFC 9112:

* **Line endings.** Only `CRLF` is accepted. §2.2 lets a recipient also accept a bare `LF`;
  this parser does not (stricter, so sound for the RFC grammar).
* **Leading empty lines** before a request line (§2.2, "SHOULD ignore at least one") are not
  skipped: a caller can strip them first.
* **Obsolete line folding** (`obs-fold`, §5.2) is rejected (a server "MUST either reject the
  message … or replace each received obs-fold with one or more SP"; we reject).
* **Whitespace between the start line and the first field** (§2.2) is rejected, as required
  of servers; for responses the RFC says clients MUST either reject or discard such lines,
  and we reject.
* **Request target.** §3.2 defines four forms by the URI grammar of RFC 3986; here the target
  is any nonempty run of `VCHAR` (all four forms are such runs, so this is a superset). The
  form is classified separately (`RequestTarget.form`), and its URI grammar belongs to the
  semantics track (`Silmaril.Net.Http`, RFC 3986).
* **Field values** are returned without their surrounding `OWS` (`trimOWS`), as §5 says
  (`OWS` "is not part of the field value"). Names keep their case; comparison is
  case-insensitive (`lower`).
* **Method** is a `token` (RFC 9110 §9.1), **status code** three `DIGIT`s (RFC 9110 §15: the
  range 100–599 is a semantic constraint, checked by the semantics track).

The grammars are `Silmaril.Parse.ByteParse` bundles, so the parsers are sound and complete by
construction; `Silmaril.Net.Http1.Message.Thms` proves the round trips
(`parseRequestHead (encRequestHead h ++ rest) = ok h |encRequestHead h|` for valid `h`), that
parsed heads are valid, and that the depth-indexed field-section grammar agrees with a
depth-free one.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

/-! ## Abstract syntax -/

/-- `HTTP-version` (RFC 9112 §2.3): a major and minor version digit. -/
structure Version where
  major : Nat
  minor : Nat
  deriving DecidableEq, Repr, Inhabited

/-- HTTP/1.1. -/
def Version.http11 : Version := ⟨1, 1⟩

/-- A field line (RFC 9112 §5), its value without surrounding whitespace. -/
structure FieldLine where
  name : Bytes
  value : Bytes
  deriving DecidableEq, Repr, Inhabited

/-- `request-line` (RFC 9112 §3). -/
structure RequestLine where
  method : Bytes
  target : Bytes
  version : Version
  deriving DecidableEq, Repr, Inhabited

/-- `status-line` (RFC 9112 §4). The reason phrase may be empty. -/
structure StatusLine where
  version : Version
  code : Nat
  reason : Bytes
  deriving DecidableEq, Repr, Inhabited

/-- A request head: request line and header section. -/
structure RequestHead where
  line : RequestLine
  fields : List FieldLine
  deriving DecidableEq, Repr, Inhabited

/-- A response head: status line and header section. -/
structure ResponseHead where
  line : StatusLine
  fields : List FieldLine
  deriving DecidableEq, Repr, Inhabited

/-! ## Validity (what the serializer can write and the parser returns) -/

/-- Single digits. -/
def Version.Valid (v : Version) : Prop := v.major < 10 ∧ v.minor < 10

/-- `field-name = token` (RFC 9110 §5.1), a `field-value` (RFC 9110 §5.5). -/
def FieldLine.Valid (f : FieldLine) : Prop := IsToken f.name ∧ IsFieldValue f.value

/-- A token method, a nonempty `VCHAR` target, a valid version. -/
def RequestLine.Valid (r : RequestLine) : Prop :=
  IsToken r.method ∧ r.target ≠ [] ∧ (∀ b ∈ r.target, isVchar b = true) ∧ r.version.Valid

/-- A valid version, three digits of status code, reason-phrase octets. -/
def StatusLine.Valid (s : StatusLine) : Prop :=
  s.version.Valid ∧ s.code < 1000 ∧ ∀ b ∈ s.reason, isFieldByte b = true

def RequestHead.Valid (h : RequestHead) : Prop := h.line.Valid ∧ ∀ f ∈ h.fields, f.Valid

def ResponseHead.Valid (h : ResponseHead) : Prop := h.line.Valid ∧ ∀ f ∈ h.fields, f.Valid

instance (v : Version) : Decidable v.Valid := inferInstanceAs (Decidable (_ ∧ _))
instance (f : FieldLine) : Decidable f.Valid := inferInstanceAs (Decidable (_ ∧ _))
instance (r : RequestLine) : Decidable r.Valid := inferInstanceAs (Decidable (_ ∧ _))
instance (s : StatusLine) : Decidable s.Valid := inferInstanceAs (Decidable (_ ∧ _))
instance (h : RequestHead) : Decidable h.Valid := inferInstanceAs (Decidable (_ ∧ _))
instance (h : ResponseHead) : Decidable h.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Serializer -/

/-- `HTTP-name "/"`: the octets of `HTTP/`. -/
def httpSlash : Bytes := [0x48, 0x54, 0x54, 0x50, 0x2F]

/-- `HTTP-version`. -/
def encVersion (v : Version) : Bytes :=
  httpSlash ++ [digitByte v.major, 0x2E, digitByte v.minor]

/-- `status-code = 3DIGIT`. -/
def encCode (c : Nat) : Bytes := [digitByte (c / 100), digitByte (c / 10 % 10), digitByte (c % 10)]

def encRequestLine (r : RequestLine) : Bytes :=
  r.method ++ [SP] ++ r.target ++ [SP] ++ encVersion r.version ++ CRLF

def encStatusLine (s : StatusLine) : Bytes :=
  encVersion s.version ++ [SP] ++ encCode s.code ++ [SP] ++ s.reason ++ CRLF

/-- `field-name ": " field-value CRLF` (one `SP` of `OWS`, as RFC 9112 §5.1 recommends). -/
def encField (f : FieldLine) : Bytes := f.name ++ [COLON, SP] ++ f.value ++ CRLF

/-- The field lines and the empty line ending the section. -/
def encFields : List FieldLine → Bytes
  | [] => CRLF
  | f :: fs => encField f ++ encFields fs

def encRequestHead (h : RequestHead) : Bytes := encRequestLine h.line ++ encFields h.fields

def encResponseHead (h : ResponseHead) : Bytes := encStatusLine h.line ++ encFields h.fields

/-! ## Grammars and parsers -/

namespace Grammar

open Silmaril.Parse.ByteParse.Grammar (lit then_)

/-- `Parse.ByteParse.Grammar.expect`. -/
abbrev PG.expect := Silmaril.Parse.ByteParse.Grammar.expect

/-- One `DIGIT`, as its value. -/
@[inline] def digit : Grammar Nat :=
  Silmaril.Parse.ByteParse.Grammar.byte.filterMap "DIGIT" fun b => if isDigit b then some (digitVal b) else none

/-- `HTTP-version` (RFC 9112 §2.3). -/
@[inline] def version : Grammar Version :=
  (lit httpSlash).then_ <| digit.bind fun ma =>
    (PG.expect "." 0x2E).then_ <| digit.map fun mi => ⟨ma, mi⟩

/-- `status-code = 3DIGIT` (RFC 9112 §4). -/
@[inline] def code : Grammar Nat :=
  digit.bind fun a => digit.bind fun b => digit.map fun c => 100 * a + 10 * b + c

/-- `request-line` (RFC 9112 §3), with its `CRLF`. -/
@[inline] def requestLine : Grammar RequestLine :=
  (delim "method" isTchar SP true).bind fun m =>
    (delim "request-target" isVchar SP true).bind fun t =>
      version.bind fun v => (lit CRLF).map fun _ => ⟨m, t, v⟩

/-- `status-line` (RFC 9112 §4), with its `CRLF`. -/
@[inline] def statusLine : Grammar StatusLine :=
  version.bind fun v => (PG.expect "SP" SP).then_ <| code.bind fun c =>
    (PG.expect "SP" SP).then_ <| (delim "reason-phrase" isFieldByte CR false).bind fun r =>
      (PG.expect "LF" LF).map fun _ => ⟨v, c, r⟩

/-- `field-line CRLF` (RFC 9112 §5): the name up to `:`, then field octets up to `CR`, then
`LF`; the value is the octets without surrounding `OWS`. -/
@[inline] def fieldLine : Grammar FieldLine :=
  (delim "field-name" isTchar COLON true).bind fun n =>
    (delim "field-value" isFieldByte CR false).bind fun raw =>
      (PG.expect "LF" LF).map fun _ => ⟨n, trimOWS raw⟩

/-- The end of a field section: `CRLF`. -/
@[inline] def endFields : Grammar (List FieldLine) := (lit CRLF).map fun _ => []

theorem tchar_ne_CR : ∀ b : UInt8, isTchar b = true → (b == CR) = false := by decide

theorem endFields_startsWith : StartsWith (fun b => (b == CR) = true) endFields.G := by
  rintro l a ⟨u, hl, -⟩
  exact ⟨CR, [LF], lit_G_eq hl, rfl⟩

theorem fieldLine_startsWith : StartsWith (fun b => (b == CR) = false) fieldLine.G := by
  rintro l a ⟨l₁, l₂, n, rfl, hn, -⟩
  obtain ⟨rfl, hall, -, hne⟩ := delim_G_iff.1 hn
  obtain ⟨b, n', rfl⟩ := List.exists_cons_of_ne_nil (hne rfl)
  have hb : isTchar b = true := hall b (by simp)
  exact ⟨b, _, rfl, tchar_ne_CR b hb⟩

/-- `*( field-line CRLF ) CRLF`, at most `k - 1` field lines (recursion depth `k`). -/
def fields : Nat → Grammar (List FieldLine)
  | 0 => Silmaril.Parse.ByteParse.Grammar.fail
  | k + 1 => Silmaril.Parse.ByteParse.Grammar.choice (· == CR) endFields
      (fieldLine.bind fun f => (fields k).map (f :: ·)) endFields_startsWith
      (by
        rintro l a ⟨l₁, l₂, f, rfl, hf, -⟩
        obtain ⟨b, l', hl, hb⟩ := fieldLine_startsWith hf
        exact ⟨b, l' ++ l₂, by rw [hl]; rfl, hb⟩)

def requestHead (k : Nat) : Grammar RequestHead :=
  requestLine.bind fun r => (fields k).map fun fs => ⟨r, fs⟩

def responseHead (k : Nat) : Grammar ResponseHead :=
  statusLine.bind fun s => (fields k).map fun fs => ⟨s, fs⟩

end Grammar

/-- The depth-free field section grammar (RFC 9112 §2.1, `*( field-line CRLF ) CRLF`): field
lines, each related by `Grammar.fieldLine`, then the empty line. `Grammar.fields k` is this
grammar restricted to fewer than `k` lines (`fields_G_iff`). -/
def FieldSection : Bytes → List FieldLine → Prop
  | l, [] => l = CRLF
  | l, f :: fs => ∃ l₁ l₂, l = l₁ ++ l₂ ∧ Grammar.fieldLine.G l₁ f ∧ FieldSection l₂ fs

/-- Parse a request head at the start of `bs`; on success, the head and the position of the
first octet after it (where the body starts). Depth `bs.size + 1` bounds the field lines,
each of which takes at least one octet. -/
def parseRequestHead (bs : ByteArray) : Res RequestHead :=
  (Grammar.requestHead (bs.size + 1)).parse bs bs.size 0

/-- Parse a response head at the start of `bs`. -/
def parseResponseHead (bs : ByteArray) : Res ResponseHead :=
  (Grammar.responseHead (bs.size + 1)).parse bs bs.size 0

end Silmaril.Net.Http1
