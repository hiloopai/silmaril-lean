module

public import Silmaril.Net.Http.Field.Defs
public import Silmaril.Formats.Compression.Registry.Defs

/-!
# Content codings in HTTP: Content-Encoding and Accept-Encoding (RFC 9110 §8.4, §12.5.3)

The HTTP side of the content-coding registry (`Formats.Compression.Registry`):

* **list syntax** (§5.6.1): `listElements` splits a field value at commas, trims
  `OWS` around each element and drops empty elements, which a recipient ignores
  (§5.6.1.2). Neither field below admits quoted strings, so splitting at commas is
  exact for them;
* **Content-Encoding** (§8.4: `Content-Encoding = #content-coding`,
  `content-coding = token`): `parseContentEncoding` checks the tokens and
  lowercases them; `resolve` maps them to registry codings (aliases included);
  `decodeContent` decodes a body under a `Profile`, in reverse order of
  application, with every stage bounded;
* **quality values** (§12.4.2): `weight = OWS ";" OWS "q=" qvalue`,
  `qvalue = ( "0" [ "." 0*3DIGIT ] ) / ( "1" [ "." 0*3("0") ] )`, as thousandths
  (`parseQvalue`: `"0.5"` is `500`, `"1"` is `1000`); the parameter name `q` is
  case-insensitive;
* **Accept-Encoding** (§12.5.3: `Accept-Encoding = #( codings [ weight ] )`,
  `codings = content-coding / "identity" / "*"`): `parseAcceptEncoding`;
  `qOf field c` is the weight the field gives coding `c` under the three rules of
  §12.5.3 (`none` is an absent field); `acceptable`, `select` (the acceptable
  coding with the highest weight, server preference breaking ties) and
  `selectFor` (only codings a `Profile` supports).

**Weights not fixed by the RFC.** An unlisted `identity` that is not excluded is
acceptable (rule 2) with the least positive weight `1` (0.001), so that any
coding the client listed is preferred to no coding; with no field at all every
coding has weight `1000` (rule 1). When a coding is listed more than once, its
first entry counts. Unregistered coding names are kept (lowercased) and simply
match nothing the server supports.

**Content versus transfer codings.** Transfer codings (`Transfer-Encoding`, `TE`,
`chunked`, RFC 9112 §6.1, §7) are a property of an HTTP/1.1 message, not of the
representation, and are owned by the HTTP/1.1 track (`Silmaril.Net.Http1`). This
module never decodes them: a Content-Encoding naming `chunked` or `trailers`
resolves to no content coding (`Registry.ofName?_chunked`) and is reported as
unsupported. A recipient removes transfer codings first, then content codings.
-/

@[expose] public section

namespace Silmaril.Net.Http.ContentCoding

open Silmaril.Net.Http.Abnf Silmaril.Net.Http.Field
open Silmaril.Formats.Compression (Encoder)
open Silmaril.Formats.Compression.Registry

/-! ## Lists (§5.6.1) -/

/-- Split at every comma. -/
def splitComma : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: bs =>
    match splitComma bs with
    | [] => [[b]]
    | first :: more => if b = 0x2C then [] :: first :: more else (b :: first) :: more

/-- Drop leading `OWS`. -/
def dropOws (xs : List UInt8) : List UInt8 := xs.dropWhile isWsp

/-- Drop leading and trailing `OWS`. -/
def trimOws (xs : List UInt8) : List UInt8 := (dropOws (dropOws xs).reverse).reverse

/-- The non-empty elements of a comma-separated list, trimmed. -/
def listElements (v : List UInt8) : List (List UInt8) :=
  ((splitComma v).map trimOws).filter (fun e => !e.isEmpty)

/-! ## Content-Encoding (§8.4) -/

/-- `Content-Encoding = #content-coding`: the coding names in the order they
were applied, lowercased; `none` if an element is not a token. -/
def parseContentEncoding (v : List UInt8) : Option (List Name) :=
  let es := listElements v
  if es.all isToken then some (es.map Formats.Compression.Registry.lower) else none

/-- Resolve names to registry content codings; an unregistered or transfer-only
name is returned as the error. -/
def resolve : List Name → Except Name (List Coding)
  | [] => .ok []
  | n :: ns =>
    match ofName? n, resolve ns with
    | none, _ => .error n
    | some _, .error m => .error m
    | some c, .ok cs => .ok (c :: cs)

/-- Why a coded body could not be decoded. -/
inductive ContentError where
  /-- The Content-Encoding field value is not a list of tokens. -/
  | badField
  /-- A name that is not a registered content coding (RFC 9110 §8.4: 415). -/
  | unknownCoding (name : Name)
  /-- More codings than the profile's `maxChain`. -/
  | tooManyCodings
  /-- A decoding stage failed. -/
  | stage (e : DecodeError Coding)
  deriving DecidableEq, Repr

/-- Decode a body given its Content-Encoding field value (`none`: no field, the
body is not coded), under a profile. -/
def decodeContent (p : Profile) (ext : Externals) (field : Option (List UInt8))
    (body : List UInt8) : Except ContentError (List UInt8) :=
  match field with
  | none => .ok body
  | some v =>
    match parseContentEncoding v with
    | none => .error .badField
    | some names =>
      match resolve names with
      | .error n => .error (.unknownCoding n)
      | .ok cs =>
        if p.maxChain < cs.length then .error .tooManyCodings
        else
          match p.decode ext cs body with
          | .error e => .error (.stage e)
          | .ok out => .ok out

/-- The Content-Encoding field value for a list of codings: `c1, c2, …`. -/
def renderContentEncoding (cs : List Coding) : List UInt8 :=
  commaSp.intercalate (cs.map Coding.name)

/-! ## Quality values (§12.4.2) -/

/-- The value of an ASCII digit. -/
def digit? (b : UInt8) : Option Nat := if isDigit b then some (b.toNat - 0x30) else none

/-- Up to three decimals after the point, as thousandths. -/
def thousandths : List UInt8 → Option Nat
  | [] => some 0
  | [a] => (digit? a).map (· * 100)
  | [a, b] => (digit? a).bind fun x => (digit? b).map fun y => x * 100 + y * 10
  | [a, b, c] =>
    (digit? a).bind fun x => (digit? b).bind fun y => (digit? c).map fun z => x * 100 + y * 10 + z
  | _ => none

/-- `qvalue = ( "0" [ "." 0*3DIGIT ] ) / ( "1" [ "." 0*3("0") ] )`, in thousandths. -/
def parseQvalue : List UInt8 → Option Nat
  | [0x30] => some 0
  | [0x31] => some 1000
  | 0x30 :: 0x2E :: ds => thousandths ds
  | 0x31 :: 0x2E :: ds => if ds.length ≤ 3 ∧ ds.all (· == 0x30) then some 1000 else none
  | _ => none

/-- The text of `weight` after its `";"`: `OWS "q=" qvalue` (the trailing `OWS` of
the list element is already trimmed). -/
def parseWeightAfterSemicolon (w : List UInt8) : Option Nat :=
  match dropOws w with
  | q :: 0x3D :: qv =>
    if Formats.Compression.Registry.lowerOctet q = 0x71 then parseQvalue qv else none
  | _ => none

/-! ## Accept-Encoding (§12.5.3) -/

/-- `codings = content-coding / "identity" / "*"`; a content coding (or
`identity`) is kept as its lowercase canonical name (aliases resolved). -/
inductive Codings where
  | named (name : Name)
  | any
  deriving DecidableEq, Repr

/-- One element `codings [ weight ]`, with the weight in thousandths (default 1000). -/
structure Pref where
  codings : Codings
  q : Nat
  deriving DecidableEq, Repr

/-- The canonical name of a coding name: the registry token if registered (so
`x-gzip` is `gzip`), otherwise its lowercase form. -/
def canonical (n : Name) : Name :=
  match ofName? n with
  | some c => c.name
  | none => Formats.Compression.Registry.lower n

/-- `codings`: `*`, or a token (canonicalised). -/
def parseCodings (nm : List UInt8) : Option Codings :=
  if nm = [0x2A] then some .any else if isToken nm then some (.named (canonical nm)) else none

/-- The optional weight after `codings`: `rest` is empty or starts with `";"`. -/
def withWeight (c : Codings) : List UInt8 → Option Pref
  | [] => some ⟨c, 1000⟩
  | _ :: w => (parseWeightAfterSemicolon w).map (⟨c, ·⟩)

/-- Parse one list element `codings [ weight ]`. -/
def parseElement (e : List UInt8) : Option Pref :=
  (parseCodings (trimOws (e.takeWhile (· ≠ 0x3B)))).bind
    (withWeight · (e.dropWhile (· ≠ 0x3B)))

/-- Parse an Accept-Encoding field value; an empty value is the empty list. -/
def parseAcceptEncoding (v : List UInt8) : Option (List Pref) :=
  (listElements v).mapM parseElement

/-- The weight of the first entry naming `n`. -/
def lookupQ (prefs : List Pref) (n : Name) : Option Nat :=
  (prefs.find? (·.codings == .named n)).map Pref.q

/-- The weight of the first `*` entry. -/
def anyQ (prefs : List Pref) : Option Nat := (prefs.find? (·.codings == .any)).map Pref.q

/-- The weight the field gives coding `c` (`none`: no Accept-Encoding field).

1. No field: every coding is acceptable (`1000`).
2. `identity`: its own entry if listed; otherwise excluded (`0`) by `*;q=0`, and
   acceptable with the least weight `1` otherwise.
3. Another coding: its own entry if listed, else the `*` entry, else `0`. -/
def qOf (field : Option (List Pref)) (c : Coding) : Nat :=
  match field with
  | none => 1000
  | some prefs =>
    match lookupQ prefs c.name with
    | some q => q
    | none =>
      if c = .identity then (if anyQ prefs = some 0 then 0 else 1)
      else (anyQ prefs).getD 0

/-- A coding is acceptable when its weight is positive (a qvalue of 0 means "not
acceptable", §12.4.2). -/
def acceptable (field : Option (List Pref)) (c : Coding) : Bool := decide (0 < qOf field c)

/-- The first candidate with the highest weight. -/
def best (w : Coding → Nat) : List Coding → Option Coding
  | [] => none
  | c :: cs =>
    match best w cs with
    | none => some c
    | some d => if w c < w d then some d else some c

/-- **Selection**: among the server's codings (in its order of preference) and
then `identity`, the acceptable one with the highest weight; `none` when nothing
is acceptable (the server may answer 406, or send `identity` anyway). -/
def select (field : Option (List Pref)) (supported : List Coding) : Option Coding :=
  match best (qOf field) (supported ++ [.identity]) with
  | some c => if 0 < qOf field c then some c else none
  | none => none

/-- Selection among the codings a profile supports. -/
def selectFor (p : Profile) (ext : Externals) (field : Option (List Pref)) : Option Coding :=
  select field (p.allowed.filter (p.supports ext))

end Silmaril.Net.Http.ContentCoding
