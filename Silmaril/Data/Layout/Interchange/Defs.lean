module

public import Silmaril.Data.Layout.Record.Defs
public import Silmaril.Data.Layout.Source.Defs
public import Silmaril.Formats.JsonWire.Defs

/-!
# Observed record layouts as JSON: the `silmaril.c-record-layout` schema, version 1

Clang has no JSON record-layout output. It prints record layouts as text, for the
`-cc1` flags `-fdump-record-layouts` (byte offsets with member names and types, nested
records expanded) and `-fdump-record-layouts-simple` (one `ASTRecordLayout` per record:
`Size`, `DataSize`, `Alignment` and the `FieldOffsets` list, all in bits, without member
names). Its JSON AST dump (`-ast-dump=json`) has member names and declaration order but no
offsets. A Clang "layout JSON" is therefore always an adapter's output; this module fixes the
format that adapter writes and the reader the Lean side trusts:

```json
{ "schema": "silmaril.c-record-layout", "version": 1, "unit": "bit",
  "provenance": { "producer": "clang", "producerVersion": "…", "method": "…",
                  "target": "x86_64-unknown-linux-gnu", "adapter": "…", "source": "…" },
  "records": [ { "kind": "struct", "name": "S", "size": 64, "dataSize": 64, "align": 32,
                 "fields": [ { "name": "a", "offset": 0 }, { "name": "b", "offset": 32 } ] } ] }
```

* Units are bits, as Clang reports them; `unit` must be `"bit"`.
* `provenance.source` is the exact C text given to the producer, so an import can be tied to
  a source by equality (`Report.Matches`), with no hash to trust. `target` is the producer's
  target triple. `producerVersion`, `method` (the command line) and `adapter` are recorded,
  not interpreted.
* `records` are the records defined in `source`, in definition order, with members in
  declaration order (the adapter's normalization: Clang's own dump order is the order it lays
  records out in).
* Readers are strict: every listed member is required, numbers must be non-negative integers,
  member names must be unique within an object, and an object may contain no other members.
  A later version changes `version`; a v1 reader rejects it.

The reader is the composition of the RFC 8259 reader `Silmaril.Formats.JsonWire.parse?`
(bytes to an ordered JSON tree) and `decode` (tree to `Report`). `Thms` proves
`decode (encode r) = .ok r` for every report; no theorem relates the byte printer to the byte
reader, so the byte-level round trip is checked on concrete reports only.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Interchange

open Silmaril.Data.Layout Silmaril.Data.Layout.Record
open Silmaril.Formats.JsonWire

/-- Where an observation came from. -/
structure Provenance where
  producer : String
  producerVersion : String
  method : String
  target : String
  adapter : String
  source : String
  deriving DecidableEq, Repr

/-- A version-1 report: provenance and the observed records. -/
structure Report where
  provenance : Provenance
  records : List ObservedRecord
  deriving DecidableEq, Repr

def schemaName : String := "silmaril.c-record-layout"
def schemaVersion : Nat := 1

/-- The report is about this source, for this target, and agrees with these layouts. -/
def Report.Matches (r : Report) (src : String) (t : Target) (Ls : List RecordLayout) : Prop :=
  r.provenance.source = src ∧ r.provenance.target = t.triple ∧ Agrees Ls r.records

instance (r : Report) (src : String) (t : Target) (Ls : List RecordLayout) :
    Decidable (r.Matches src t Ls) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The whole chain for one source, target and imported report: `src` parses to some `env`,
which resolves on `t` to well-formed layouts that the report (about `src`, for `t`) agrees
with. What it does not say: that the report is what the producer printed (that is the
adapter's job), or anything about compilers other than through such reports. -/
def CrossChecked (src : String) (t : Target) (r : Report) : Prop :=
  ∃ env, Source.Parses src env ∧ ∃ Ls, resolveEnv t.model env = .ok Ls ∧
    (∀ R ∈ Ls, R.WF) ∧ r.Matches src t Ls

/-! ## Encoding -/

abbrev Json := Ast Decimal

def jstr (s : String) : Json := .scalar (some (.string (stringUnits s)))
def jnat (n : Nat) : Json := .scalar (some (.number ⟨false, n, 0⟩))
def jarr (xs : List Json) : Json := .list (Silmaril.Formats.RawSyn.ofList xs)
def jobj (es : List (String × Json)) : Json :=
  .map (Silmaril.Formats.RawSyn.ofEntries (es.map fun e => (stringUnits e.1, e.2)))

def kindName : Kind → String
  | .struct => "struct"
  | .union => "union"

def encodeField (f : ObservedField) : Json :=
  jobj [("name", jstr f.name), ("offset", jnat f.offset)]

def encodeRecord (r : ObservedRecord) : Json :=
  jobj [("kind", jstr (kindName r.kind)), ("name", jstr r.name), ("size", jnat r.size),
    ("dataSize", jnat r.dataSize), ("align", jnat r.align),
    ("fields", jarr (r.fields.map encodeField))]

def encodeProvenance (p : Provenance) : Json :=
  jobj [("producer", jstr p.producer), ("producerVersion", jstr p.producerVersion),
    ("method", jstr p.method), ("target", jstr p.target), ("adapter", jstr p.adapter),
    ("source", jstr p.source)]

def encode (r : Report) : Json :=
  jobj [("schema", jstr schemaName), ("version", jnat schemaVersion), ("unit", jstr "bit"),
    ("provenance", encodeProvenance r.provenance),
    ("records", jarr (r.records.map encodeRecord))]

/-- The report as JSON text (every string character written as a `\uXXXX` escape). -/
def encodeText (r : Report) : String := render Decimal.literal (encode r)

/-! ## Decoding -/

/-- The entries of an object whose member names are all among `keys`, without duplicates. -/
def objectOf (keys : List String) (what : String) : Json →
    Except String (List (Units × Json))
  | .map es =>
    let es := es.toEntries
    if !es.all (fun e => keys.any (fun k => stringUnits k == e.1)) then
      .error s!"{what}: unknown member"
    else if !(es.map (·.1)).Nodup then .error s!"{what}: duplicate member"
    else .ok es
  | _ => .error s!"{what}: expected an object"

/-- The value of member `key`. -/
def member (es : List (Units × Json)) (key : String) : Except String Json :=
  match es.find? (·.1 == stringUnits key) with
  | some (_, v) => .ok v
  | none => .error s!"missing member `{key}`"

def asString (what : String) : Json → Except String String
  | .scalar (some (.string us)) => match unitsString? us with
    | some s => .ok s
    | none => .error s!"{what}: not a Unicode string"
  | _ => .error s!"{what}: expected a string"

def asNat (what : String) : Json → Except String Nat
  | .scalar (some (.number d)) => match d.toInt? with
    | some i => if 0 ≤ i then .ok i.toNat else .error s!"{what}: expected a non-negative integer"
    | none => .error s!"{what}: expected an integer"
  | _ => .error s!"{what}: expected a number"

def asList (what : String) : Json → Except String (List Json)
  | .list xs => .ok xs.toList
  | _ => .error s!"{what}: expected an array"

def stringMember (es : List (Units × Json)) (key : String) : Except String String :=
  match member es key with
  | .ok v => asString key v
  | .error e => .error e

def natMember (es : List (Units × Json)) (key : String) : Except String Nat :=
  match member es key with
  | .ok v => asNat key v
  | .error e => .error e

def kindOf? : String → Except String Kind
  | "struct" => .ok .struct
  | "union" => .ok .union
  | k => .error s!"unsupported record kind `{k}` (v1 has struct and union)"

def decodeField (j : Json) : Except String ObservedField := do
  let es ← objectOf ["name", "offset"] "field" j
  return { name := (← stringMember es "name"), offset := (← natMember es "offset") }

def decodeRecord (j : Json) : Except String ObservedRecord := do
  let es ← objectOf ["kind", "name", "size", "dataSize", "align", "fields"] "record" j
  let kind ← kindOf? (← stringMember es "kind")
  let name ← stringMember es "name"
  let size ← natMember es "size"
  let dataSize ← natMember es "dataSize"
  let align ← natMember es "align"
  let fields ← traverse decodeField (← asList "fields" (← member es "fields"))
  return { kind, name, size, dataSize, align, fields }

def decodeProvenance (j : Json) : Except String Provenance := do
  let es ← objectOf ["producer", "producerVersion", "method", "target", "adapter", "source"]
    "provenance" j
  let producer ← stringMember es "producer"
  let producerVersion ← stringMember es "producerVersion"
  let method ← stringMember es "method"
  let target ← stringMember es "target"
  let adapter ← stringMember es "adapter"
  let source ← stringMember es "source"
  return { producer, producerVersion, method, target, adapter, source }

def decode (j : Json) : Except String Report := do
  let es ← objectOf ["schema", "version", "unit", "provenance", "records"] "report" j
  if (← stringMember es "schema") != schemaName then throw "not a silmaril.c-record-layout report"
  if (← natMember es "version") != schemaVersion then throw "unsupported schema version"
  if (← stringMember es "unit") != "bit" then throw "unsupported unit (v1 uses bits)"
  let provenance ← decodeProvenance (← member es "provenance")
  let records ← traverse decodeRecord (← asList "records" (← member es "records"))
  return { provenance, records }

/-- Read a report from JSON text: RFC 8259 bytes, then `decode`. -/
def decodeText (s : String) : Except String Report :=
  match parse? ⟨s.toUTF8⟩ with
  | none => .error "not RFC 8259 JSON"
  | some j => decode j

end Silmaril.Data.Layout.Interchange
