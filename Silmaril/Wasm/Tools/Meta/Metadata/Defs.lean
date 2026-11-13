module

public import Silmaril.Wasm.Tools.Meta.Producers.Defs
public import Silmaril.Wasm.Tools.Meta.Table.Defs
public import Silmaril.Wasm.Tools.Meta.Spdx.Defs
public import Silmaril.Wasm.Tools.Meta.Url.Defs
public import Silmaril.Wasm.Tools.Meta.DepV0.Defs

/-!
# `wasm-tools metadata show` and `metadata add`: the cores

The metadata of a binary (wasm-metadata 0.262, `Payload::from_binary`) and its two renderings,
and the rewrite of `AddMetadata::to_wasm`.

**Reading** (`payloadOf`): every module and component of the binary, nested ones included, with
its byte range (the whole file for the outer one, the contents of its section for a nested one),
and from its own custom sections (later ones win):

| section | field | read |
|---|---|---|
| `name` | name | the module name subsection (`scanNames`) |
| `component-name` | name | the component name subsection (`scanCompNames`) |
| `producers` (when its field count reads) | producers | `readProducers` |
| `authors`, `description`, `revision`, `version` | the field | UTF-8 |
| `licenses` | licenses | UTF-8 and a valid SPDX expression (`Spdx.checkLicense`) |
| `source`, `homepage` | the field | UTF-8 and a URL, normalised (`Url.normalizeUrl`) |
| `.dep-v0` | dependencies | zlib, UTF-8, JSON, `VersionInfo` (`DepV0.readDeps`) |

A malformed one of these is an error of the command, as upstream.

**Showing**: `showJson` is serde_json's compact output of the `Payload` (no final newline);
`showText` is the summary table and then one detail table per module and component
(`write_summary_table`, `write_details_table`).

**Adding** (`addMetadata`): the binary is rebuilt from its sections (minimal size fields; nested
units re-encoded), and only the outer unit's custom sections change: the producers section is
merged with the new values (`Producers.merge`), the name section gets the new name (or loses it), the
`authors`…`version` sections are re-encoded, dropped (`--clear-…`) or kept, and then the missing
name and producers sections and every set field are appended, as `rewrite_wasm` does. (Upstream
keeps an existing `authors`… section when the field is set, and appends the new one; so does
this.)
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Metadata

open Silmaril.Wasm.Tools.Meta

/-- The metadata of one module or component. -/
structure Meta where
  name : Option String := none
  producers : Option Producers := none
  authors : Option String := none
  description : Option String := none
  licenses : Option String := none
  source : Option String := none
  homepage : Option String := none
  revision : Option String := none
  version : Option String := none
  range : Nat × Nat := (0, 0)
  dependencies : Option DepV0.VersionInfo := none
  deriving Inhabited, Repr

/-- A module, or a component and what it contains. -/
inductive Payload where
  | module (m : Meta)
  | component (m : Meta) (children : List Payload)
  deriving Inhabited, Repr

def Payload.meta : Payload → Meta
  | .module m => m
  | .component m _ => m

def Payload.kind : Payload → String
  | .module _ => "module"
  | .component .. => "component"

/-- `String::from_utf8` of a custom section's data. -/
def utf8Str (d : List UInt8) : Except String String :=
  match String.fromUTF8? (ByteArray.mk d.toArray) with
  | some s => .ok s
  | none => .error "invalid utf-8 sequence"

/-- The effect of one custom section (name and data) on the metadata. -/
def readCustom (m : Meta) (name data : List UInt8) : Except String Meta := do
  let n := strOf name
  if n == "name" then
    match ← scanNames data with
    | some x => pure { m with name := some (strOf x) }
    | none => pure m
  else if n == "component-name" then
    match ← scanCompNames data with
    | some x => pure { m with name := some (strOf x) }
    | none => pure m
  else if n == "producers" then
    if !producersCountOk data then pure m else
    pure { m with producers := some (← readProducers data) }
  else if n == "authors" then pure { m with authors := some (← utf8Str data) }
  else if n == "description" then pure { m with description := some (← utf8Str data) }
  else if n == "revision" then pure { m with revision := some (← utf8Str data) }
  else if n == "version" then pure { m with version := some (← utf8Str data) }
  else if n == "licenses" then
    let s ← utf8Str data
    match Spdx.checkLicense s with
    | some e => throw (s ++ "\n" ++ e)
    | none => pure { m with licenses := some s }
  else if n == "source" then pure { m with source := some (← Url.normalizeUrl (← utf8Str data)) }
  else if n == "homepage" then pure { m with homepage := some (← Url.normalizeUrl (← utf8Str data)) }
  else if n == ".dep-v0" then
    pure { m with dependencies := some (← DepV0.readDeps (ByteArray.mk data.toArray)) }
  else pure m

mutual
/-- The payloads of the items of a unit starting at offset `off`, updating the unit's own
metadata `m`; the children found. -/
def walkItems (off : Nat) (m : Meta) : List Item → Except String (Meta × List Payload)
  | [] => .ok (m, [])
  | .sec s :: is => do
    let m ← if s.id == 0 then
        match customOf s.body with
        | .ok (nm, data) => readCustom m nm data
        | .error e => throw e
      else pure m
    walkItems (off + s.bytes.length) m is
  | .nest _ size enc items :: is => do
    let start := off + 1 + size.length
    let p ← walkUnit start (start + (enc.header ++ Item.listBytes items).length) enc items
    let (m, cs) ← walkItems (start + (enc.header ++ Item.listBytes items).length) m is
    pure (m, p :: cs)
/-- The payload of a unit with range `[a, b)`. -/
def walkUnit (a b : Nat) (enc : Enc) (items : List Item) : Except String Payload := do
  let (m, cs) ← walkItems (a + 8) { range := (a, b) } items
  match enc with
  | .module => pure (.module m)
  | .component => pure (.component m cs)
end

/-- **`Payload::from_binary`.** -/
def payloadOf (bs : List UInt8) : Except String Payload := do
  let (enc, items) ← parseBinary bs
  walkUnit 0 bs.length enc items

/-! ## JSON -/

def hex4 (n : Nat) : String :=
  let d := "0123456789abcdef".toList
  String.ofList [d[n / 4096 % 16]!, d[n / 256 % 16]!, d[n / 16 % 16]!, d[n % 16]!]

/-- serde_json's string escaping. -/
def jsonStr (s : String) : String :=
  "\"" ++ s.toList.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\"" | '\\' => acc ++ "\\\\" | '\n' => acc ++ "\\n" | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t" | '\x08' => acc ++ "\\b" | '\x0c' => acc ++ "\\f"
    | c => if c.toNat < 0x20 then acc ++ "\\u" ++ hex4 c.toNat else acc.push c) "" ++ "\""

def jsonOpt (o : Option String) : String := (o.map jsonStr).getD "null"

def jsonMap (m : OMap String) : String :=
  "{" ++ ",".intercalate (m.map fun (k, v) => jsonStr k ++ ":" ++ jsonStr v) ++ "}"

def jsonProd (p : Option Producers) : String :=
  match p with
  | none => "null"
  | some p => "[" ++ ",".intercalate (p.map fun (f, vals) => "[" ++ jsonStr f ++ "," ++ jsonMap vals ++ "]") ++ "]"

def jsonMeta (m : Meta) : String :=
  "{\"name\":" ++ jsonOpt m.name ++ ",\"producers\":" ++ jsonProd m.producers ++
  ",\"authors\":" ++ jsonOpt m.authors ++ ",\"description\":" ++ jsonOpt m.description ++
  ",\"licenses\":" ++ jsonOpt m.licenses ++ ",\"source\":" ++ jsonOpt m.source ++
  ",\"homepage\":" ++ jsonOpt m.homepage ++ ",\"revision\":" ++ jsonOpt m.revision ++
  ",\"version\":" ++ jsonOpt m.version ++ ",\"range\":{\"start\":" ++ toString m.range.1 ++
  ",\"end\":" ++ toString m.range.2 ++ "},\"dependencies\":" ++
  (match m.dependencies with
    | some d => jsonStr d.toJson
    | none => "null") ++ "}"

/-- **`serde_json::to_string(&payload)`**. -/
def showJson : Payload → String
  | .module m => "{\"module\":" ++ jsonMeta m ++ "}"
  | .component m cs => "{\"component\":{\"metadata\":" ++ jsonMeta m ++ ",\"children\":[" ++
      ",".intercalate (cs.attach.map fun ⟨c, _⟩ => showJson c) ++ "]}}"

/-! ## Tables -/

/-- The largest range end of the tree. -/
def rangeMax : Payload → Nat
  | .module m => m.range.2
  | .component m cs => cs.attach.foldl (fun mx ⟨c, _⟩ => max mx (rangeMax c)) m.range.2

/-- The `SIZE%` cell. -/
def usePct (size rmax endv : Nat) : String :=
  let p := Table.roundAway (Table.f64MulNat (Table.f64Of size rmax) 100)
  let p := if size == 0 then 0 else min p 255
  if p ≤ 1 then "<1%" else if p == 100 && endv != rmax then ">99%" else toString p ++ "%"

/-- The `LANGUAGES` cell. -/
def languages (m : Meta) : String :=
  match m.producers with
  | some p => match p.lookup "language" with
    | some vals => ", ".intercalate (vals.map (·.1))
    | none => "-"
  | none => "-"

/-- The rows of the summary table (pre-order), with the unknown-name counter. -/
def summaryRows (rmax : Nat) (parent : String) (k : Nat) (p : Payload) : List (List String) × Nat :=
  let m := p.meta
  let (name, k) := match m.name with
    | some n => (n, k)
    | none => ("unknown(" ++ toString k ++ ")", k + 1)
  let size := m.range.2 - m.range.1
  let row := [p.kind, name, Table.siShort size, usePct size rmax m.range.2, languages m, parent]
  match p with
  | .module _ => ([row], k)
  | .component _ cs =>
    let (rows, k) := cs.attach.foldl (fun (rows, k) ⟨c, _⟩ =>
      let (r, k) := summaryRows rmax name k c
      (rows ++ r, k)) ([], k)
    (row :: rows, k)
termination_by p
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ cs›
  omega

def hexRange (r : Nat × Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 r.1) ++ "..0x" ++ String.ofList (Nat.toDigits 16 r.2)

/-- The producers rows: `language` first, then the other fields by name. -/
def producerRows (p : Producers) : List (List String) :=
  let lang := p.filter (·.1 == "language")
  let others := (p.filter (·.1 != "language")).mergeSort (le := fun a b => decide (a.1.toUTF8.toList ≤ b.1.toUTF8.toList))
  (lang ++ others).flatMap fun (f, vals) =>
    vals.map fun (n, v) => [f, if v.isEmpty then n else n ++ " [" ++ v ++ "]"]

/-- The rows of one detail table. -/
def detailRows (p : Payload) : List (List String) :=
  let m := p.meta
  let opt (k : String) (o : Option String) : List (List String) := (o.map fun v => [[k, v]]).getD []
  [["name", m.name.getD "<unknown>"], ["kind", p.kind], ["range", hexRange m.range]] ++
  opt "description" m.description ++ opt "authors" m.authors ++ opt "version" m.version ++
  opt "revision" m.revision ++ opt "licenses" m.licenses ++ opt "source" m.source ++
  opt "homepage" m.homepage ++ ((m.producers.map producerRows).getD []) ++
  (match p with
    | .module _ => []
    | .component _ cs => cs.map fun c => ["child", c.meta.name.getD "<unknown>" ++ " [" ++ c.kind ++ "]"]) ++
  (match m.dependencies with
    | some d => d.packages.map fun pk => ["dependency", pk.name ++ " [" ++ pk.version ++ "]"]
    | none => [])

/-- The detail tables, pre-order. -/
def detailTables (p : Payload) : List String :=
  let t := Table.renderTable ["KIND", "VALUE"] (detailRows p) [.left, .left]
  match p with
  | .module _ => [t]
  | .component _ cs => t :: (cs.attach.flatMap fun ⟨c, _⟩ => detailTables c)
termination_by p
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ cs›
  omega

/-- **The text output of `metadata show`**: the summary table, then the detail tables, each
followed by a newline. -/
def showText (p : Payload) : String :=
  let (rows, _) := summaryRows (rangeMax p) "<root>" 0 p
  let summary := Table.renderTable ["KIND", "NAME", "SIZE", "SIZE%", "LANGUAGES", "PARENT"] rows
    [.left, .left, .right, .right, .left, .left]
  String.join ((summary :: detailTables p).map (· ++ "\n"))

/-! ## `metadata add` -/

/-- A field of `AddMetadata`. -/
inductive Field where
  | keep
  | clear
  | set (v : String)
  deriving Inhabited, DecidableEq, Repr

/-- `AddMetadata`. -/
structure Add where
  name : Field := .keep
  language : List (String × String) := []
  processedBy : List (String × String) := []
  sdk : List (String × String) := []
  authors : Field := .keep
  description : Field := .keep
  licenses : Field := .keep
  source : Field := .keep
  homepage : Field := .keep
  revision : Field := .keep
  version : Field := .keep
  deriving Inhabited, DecidableEq, Repr

/-- `Producers::from_meta`. -/
def Add.producers (a : Add) : Producers :=
  let p := a.language.foldl (fun (p : Producers) (n, v) => Producers.add p "language" n v) ([] : Producers)
  let p := a.processedBy.foldl (fun (p : Producers) (n, v) => Producers.add p "processed-by" n v) p
  a.sdk.foldl (fun (p : Producers) (n, v) => Producers.add p "sdk" n v) p

/-- The OCI annotation fields, in the order `rewrite_wasm` appends them. -/
def ociFields (a : Add) : List (String × Field) :=
  [("authors", a.authors), ("description", a.description), ("licenses", a.licenses),
   ("source", a.source), ("homepage", a.homepage), ("revision", a.revision), ("version", a.version)]

/-- The stored text of an OCI field value (licenses checked, URLs normalised). -/
def ociValue (k v : String) : Except String String :=
  if k == "licenses" then
    match Spdx.checkLicense v with
    | some e => .error (v ++ "\n" ++ e)
    | none => .ok v
  else if k == "source" || k == "homepage" then Url.normalizeUrl v
  else .ok v

/-- A custom section holding a string. -/
def strSec (name v : String) : List UInt8 := customSec (sBytes name) (sBytes v)

/-- The name section after `--name`/`--clear-name` (`ModuleNames`/`ComponentNames`: the
lazy read, then the full decode of the other subsections, the name first). -/
def rewriteNames (comp : Bool) (f : Field) (data : List UInt8) : Except String (List UInt8) := do
  let name ← if comp then scanCompNames data else scanNames data
  let subs ← if comp then decodeCompNames data else decodeNames false data
  let others := subs.filter fun s => match s with | .name _ => false | _ => true
  let (name, others) := match f with
    | .keep => (name, others)
    | .set v => (some (sBytes v), others)
    | .clear => (none, [])
  let subs := (match name with | some n => [NSub.name n] | none => []) ++ others
  pure (customSec (if comp then compNameName else nameName) (encNames subs))

/-- The flags `rewrite_wasm` keeps while walking the outer unit. -/
structure AddSt where
  /-- The output so far, as chunks in reverse order (appending a chunk is constant time). -/
  out : List (List UInt8) := []
  producersFound : Bool := false
  namesFound : Bool := false

mutual
/-- The bytes of the items of a nested unit: every section raw (minimal size fields). -/
def rawItems : List Item → List UInt8
  | [] => []
  | .sec s :: is => rawSec s.id s.body ++ rawItems is
  | .nest id _ enc items :: is =>
    let inner := enc.header ++ rawItems items
    (id :: (encU32 inner.length ++ inner)) ++ rawItems is
end

/-- One outer section of `rewrite_wasm`. -/
def addSec (a : Add) (comp : Bool) (st : AddSt) (s : Sec) : Except String AddSt := do
  let raw := { st with out := rawSec s.id s.body :: st.out }
  if s.id != 0 then return raw
  let (nm, data) ← customOf s.body
  let n := strOf nm
  if n == "producers" && producersCountOk data then
    let p ← readProducers data
    return { st with out := encProducers (Producers.merge p a.producers) :: st.out, producersFound := true }
  if n == "name" then
    return { st with out := (← rewriteNames false a.name data) :: st.out, namesFound := true }
  if n == "component-name" then
    return { st with out := (← rewriteNames true a.name data) :: st.out, namesFound := true }
  match (ociFields a).lookup n with
  | some .keep =>
    let v ← utf8Str data
    let v ← ociValue n v
    return { st with out := strSec n v :: st.out }
  | some .clear => return st
  | _ => return raw
  where _comp := comp

/-- The custom sections of the OCI fields `a` sets, appended to `out` (the last loop of
`AddMetadata::to_wasm`). -/
def addOci (a : Add) (out : List UInt8) : Except String (List UInt8) := do
  let mut out := out
  for (k, f) in ociFields a do
    if let .set v := f then
      out := out ++ strSec k (← ociValue k v)
  pure out

/-- **`AddMetadata::to_wasm`** on the bytes of a binary. -/
def addMetadata (a : Add) (bs : List UInt8) : Except String (List UInt8) := do
  let (enc, items) ← parseBinary bs
  let comp := enc == .component
  let st ← items.foldlM (fun st it =>
    match it with
    | .sec s => addSec a comp st s
    | .nest id _ enc' items' =>
      let inner := enc'.header ++ rawItems items'
      pure { st with out := (id :: (encU32 inner.length ++ inner)) :: st.out }) ({} : AddSt)
  let mut out := enc.header ++ st.out.reverse.flatten
  if !st.namesFound then
    if let .set v := a.name then
      out := out ++ customSec (if comp then compNameName else nameName) (encNames [.name (sBytes v)])
  if !st.producersFound && !a.producers.isEmpty then
    out := out ++ encProducers (Producers.merge [] a.producers)
  addOci a out

end Silmaril.Wasm.Tools.Meta.Metadata

end
