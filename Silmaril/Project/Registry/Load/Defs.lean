module

public import Silmaril.Project.Registry.Value.Defs
public import Silmaril.Project.Registry.Predicate.Defs
public meta import Lake.Toml

/-!
# Silmaril projects: records in TOML (`silmaril load`)

`silmaril load "silmaril/example/inputs.toml"` reads a **records file** (or, for a directory,
every `*.toml` below it, sorted by path) at elaboration time and adds its records. The path is
relative to the package root. A records file is another way to write the `silmaril <kind> …`
commands: each table runs the same kind handler as the command would, so the two spellings give
the same records (`docs/projects/silmaril-projects.md`).

```toml
schema = "silmaril.records.v0.2"
root = "demo.all"                     # optional: `silmaril root demo.all`

[defaults.judgement]                  # optional: keys every `[[judgement]]` below gets
model = "demo.models.reader"

[[judgement]]                         # `silmaril judgement demo.greets (expect := "THM") …`
name = "demo.greets"
expect = "THM"
```

**The schema** is defined once, in Rust (`tools/silmaril-project/src/project/schema/records.rs`):
`sil project lint` checks records files without Lean, `sil project schema` prints it as JSON
Schema, and `sil project check` also checks that every record of every local records file is in
the dump (so a file that is not loaded, or a module not rebuilt after an edit, is reported).
This reader only knows the order of the kinds (`loadKinds`, compared with Rust's by a Rust test)
and three spellings:

* a key in `constKeys` (`decl`, `proof`, `rel`) names a Lean constant, resolved as an identifier
  would be in the command; `module` names an imported module;
* `[[value]]`: `format` and `source` (a CID, a registry path or a registry name), plus
  `sources = [{ format, source }]` for the sources that must agree with it;
* `[[instance]]`: `of` (the problem) and `args = { <binder or position> = <reference> }`, where
  a reference is a constant or value name (a string), an integer, a boolean, `{ str = "…" }`,
  or an application `["f", <reference>, …]`. Anything else (binders, `match`, notation) is
  written as a Lean definition and named.

Every other key is a field of the record, as in the command, except `meta`: any table of
tool-only data (where a record was converted from, provenance notes), which this reader skips, so
it never reaches the record or the dump. Tables run in the order of
`loadKinds`, then project-defined kinds (any other `[[kind]]` with a registered handler), then
`root`; within a kind, in file order. So a group may come before its children in the file.

**Errors** name the TOML position (`silmaril/example/dag.toml:12:1: silmaril judgement: …`) and
are reported on the `silmaril load` command. Each table's errors are reported and the next table
still runs.

**Rebuilds.** Lake does not see the files a module reads. A project that keeps its records
files in a directory declares it as a Lake `[[input_dir]]` of the library whose modules load it;
put it in that library's `needs` (`docs/projects/silmaril-projects.md`). `sil project check` reports a
stale dump (rule R11).
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command

/-- The schema string of a records file. -/
def recordsSchema : String := "silmaril.records.v0.2"

/-- The record kinds of a records file, in the order `silmaril load` runs them. Mirrored by
`RECORD_KINDS` in `tools/silmaril-project/src/project/schema/records.rs` (a Rust test compares the two). -/
def loadKinds : List String :=
  ["artifact_type", "format", "format_default", "format_law", "value", "model", "spec", "room",
    "machine", "machine_binding", "instance", "tasks", "judgement", "detached", "decomposition",
    "refutation_route", "group",
    "children"]

/-- The top-level keys of a records file that are not kinds. -/
def recordsFileKeys : List String := ["schema", "root", "defaults"]

/-- A TOML value as JSON: strings, integers, booleans, and arrays and tables of those. -/
partial def tomlJsonDeep? : Lake.Toml.Value → Option Json
  | .table _ t => (t.items.toList.mapM fun (k, v) => (leanToName k, ·) <$> tomlJsonDeep? v).map Json.mkObj
  | .array _ xs => (xs.toList.mapM tomlJsonDeep?).map (Json.arr ∘ List.toArray)
  | v => tomlJson? v

/-- A parsed records file. -/
structure RecordsFile where
  /-- The path, relative to the package root. -/
  path : String
  /-- The text, for positions. -/
  fileMap : FileMap
  /-- The top-level table. -/
  table : Lake.Toml.Table

/-- `path:line:col` of a TOML value. -/
def RecordsFile.loc (f : RecordsFile) (v : Lake.Toml.Value) : String :=
  match v.ref.getPos? with
  | some p => let pos := f.fileMap.toPosition p; s!"{f.path}:{pos.line}:{pos.column + 1}"
  | none => f.path

/-- Read and parse a TOML file (relative to the package root). -/
def readTomlFile (root : System.FilePath) (path : String) : CommandElabM RecordsFile := do
  let text ← try IO.FS.readFile (root / path) catch _ =>
    throwError "silmaril load: cannot read {path} (relative to the package root {root})"
  let ictx := Parser.mkInputContext text path
  match ← (Lake.Toml.loadToml ictx).toBaseIO with
  | .ok table => return { path, fileMap := ictx.fileMap, table }
  | .error log =>
    let msgs ← log.toList.mapM (·.toString)
    throwError "silmaril load: {path} is not TOML:\n{"\n".intercalate msgs}"

/-- The `schema` string of a TOML table, if any. -/
def tomlSchema? (t : Lake.Toml.Table) : Option String :=
  match t.find? `schema with | some (.string _ s) => some s | _ => none

/-- The records files of a load path: the file, or every `*.toml` below the directory (sorted by
path) except other silmaril files (`silmaril.artifacts.*`, `silmaril.project.*`). -/
def recordsFiles (root : System.FilePath) (path : String) : CommandElabM (Array RecordsFile) := do
  unless ← (root / path).isDir do return #[← readTomlFile root path]
  let base := (root / path).toString
  let found ← (root / path).walkDir
  let rels := (found.filter (·.extension == some "toml")).map fun p =>
    path ++ "/" ++ ((p.toString.dropPrefix? (base ++ "/")).map (·.toString)).getD p.toString
  let mut out := #[]
  for rel in rels.qsort (· < ·) do
    let f ← readTomlFile root rel
    let other := match tomlSchema? f.table with
      | some s => s.startsWith "silmaril.artifacts." || s.startsWith "silmaril.project."
      | none => false
    unless other do out := out.push f
  if out.isEmpty then throwError "silmaril load: {path} has no records file (`*.toml`)"
  return out

/-- A field from TOML: a constant for the keys in `constKeys`, an imported module for
`module`, else the value as JSON. -/
def tomlField (kind key : String) (v : Lake.Toml.Value) : CoreM (Json × Option Name) := do
  let some j := tomlJsonDeep? v
    | throwError "silmaril {kind}: `{key}`: floats and dates are not record values"
  match key, j with
  | "module", .str m =>
    let n := m.toName
    let env ← getEnv
    unless env.header.moduleNames.contains n || n == env.mainModule do
      throwError "silmaril {kind}: module {m} is not imported"
    return (j, some n)
  | "expect", .str e => return (.str (normExpect e), none)
  | k, .str c =>
    unless constKeys.contains k do return (j, none)
    let n ← try realizeGlobalConstNoOverload (mkIdent c.toName) catch e =>
      throwError "silmaril {kind}: `{k} = {c.quote}`: {e.toMessageData}"
    return (.str n.toString, some n)
  | _, _ => return (j, none)

/-- A reference as a term (`[[instance]]` arguments): a name (a constant, or a registered
value), an integer, a boolean, `{ str = "…" }`, or an application `["f", ref, …]`. -/
partial def tomlTerm (v : Lake.Toml.Value) : CoreM Term := do
  match v with
  | .string _ s => return mkIdent (nameToLean s)
  | .integer _ n =>
    let lit := Syntax.mkNumLit (toString n.natAbs)
    if n ≥ 0 then return lit else `(- $lit)
  | .boolean _ b => return mkIdent (if b then `true else `false)
  | .table _ t =>
    match t.items.toList with
    | [(`str, .string _ s)] => return Syntax.mkStrLit s
    | _ => throwError "silmaril instance: a table reference is `\{ str = \"…\" }`"
  | .array _ xs =>
    match xs.toList with
    | .string _ f :: args@(_ :: _) =>
      return Syntax.mkApp (mkIdent (nameToLean f)) (← args.toArray.mapM tomlTerm)
    | _ => throwError "silmaril instance: an application is `[\"f\", <argument>, …]`"
  | _ => throwError "silmaril instance: floats and dates are not references"

/-- A table's keys, with the kind's defaults (`[defaults.<kind>]`) for the missing ones. -/
def withDefaults (defaults? : Option Lake.Toml.Table) (t : Lake.Toml.Table) :
    Array (String × Lake.Toml.Value) := Id.run do
  let own := t.items.map fun (k, v) => (leanToName k, v)
  let some d := defaults? | return own
  let extra := (d.items.filter fun (k, _) => !t.contains k).map fun (k, v) => (leanToName k, v)
  return extra ++ own

/-- An error message that already names its TOML position (a field's). -/
def locatedTag : Name := `silmaril.load.located

/-- Throw an error at a TOML position. -/
def throwAtToml {α} (loc : String) (msg : MessageData) : CommandElabM α :=
  throwError (MessageData.tagged locatedTag m!"{loc}: {msg}")

/-- Run `act`, prefixing the errors it reports (thrown or logged) with `loc`, unless they
already name a position. -/
def withLoc (loc : String) (act : CommandElabM Unit) : CommandElabM Unit := do
  let saved := (← get).messages
  modify fun s => { s with messages := {} }
  let restore : CommandElabM Unit := modify fun s =>
    let new := { s.messages with unreported := s.messages.unreported.map fun m =>
      if m.severity == .error && !m.data.hasTag (· == locatedTag) then
        { m with data := m!"{loc}: " ++ m.data } else m }
    { s with messages := saved ++ new }
  try act catch e =>
    if e.isInterrupt || e.isRuntime then restore; throw e
    logException e
  restore

/-- One table of a records file: run its kind. -/
def loadTable (f : RecordsFile) (kind : String) (keys : Array (String × Lake.Toml.Value)) :
    CommandElabM Unit := do
  let get? (k : String) : Option Lake.Toml.Value := (keys.find? (·.1 == k)).map (·.2)
  let str? (k : String) : CommandElabM (Option String) := do
    match get? k with
    | none => return none
    | some (.string _ s) => return some s
    | some v => throwAtToml (f.loc v) m!"silmaril {kind}: `{k}` must be a string"
  let name? ← str? "name"
  -- the remaining keys are fields, in file order
  let fields (skip : List String) : CommandElabM Fields := do
    let mut fs : Fields := {}
    for (k, v) in keys do
      if k == "name" || k == "meta" || skip.contains k then continue
      let (j, c) ← try liftCoreM (tomlField kind k v) catch e =>
        throwAtToml (f.loc v) e.toMessageData
      fs ← liftCoreM (fs.push kind k j c)
    return fs
  match kind with
  | "value" =>
    let name ← liftCoreM (needName kind name?)
    let some fmt ← str? "format" | throwError "silmaril value: `format` is required"
    let some src ← str? "source" | throwError "silmaril value: `source` is required"
    let ref ← getRef
    let mut sources := #[(fmt, SourceRef.auto src, ref)]
    match get? "sources" with
    | none => pure ()
    | some (.array _ xs) =>
      for x in xs do
        let .table _ t := x | throwError "{f.loc x}: silmaril value: `sources` entries are \
          `\{ format = \"…\", source = \"…\" }`"
        let (some (.string _ fmt), some (.string _ src)) := (t.find? `format, t.find? `source)
          | throwError "{f.loc x}: silmaril value: a `sources` entry needs `format` and `source`"
        sources := sources.push (fmt, .auto src, ref)
    | some v => throwError "{f.loc v}: silmaril value: `sources` is an array of tables"
    declareValue name sources (← fields ["format", "source", "sources"])
  | "instance" =>
    let name ← liftCoreM (needName kind name?)
    let some of ← str? "of" | throwError "silmaril instance: `of` (the problem) is required"
    let ref ← getRef
    let args ← match get? "args" with
      | some (.table _ t) => t.items.mapM fun (k, v) => do
        let k := leanToName k
        let key : String ⊕ Nat := match k.toNat? with | some n => .inr n | none => .inl k
        let t ← try liftCoreM (tomlTerm v) catch e => throwAtToml (f.loc v) e.toMessageData
        return (key, t.raw, ref)
      | some v => throwError "{f.loc v}: silmaril instance: `args` is a table \
          `\{ <binder or position> = <reference> }`"
      | none => pure #[]
    declareInstance name (← fields ["of", "args"]) of args
  | _ => runRecord kind name? (← fields [])

/-- `silmaril load "PATH"`: add the records of a records file, or of every records file below a
directory. -/
def loadRecords (path : String) : CommandElabM Unit := do
  let (root, _) ← packageRoot
  let files ← recordsFiles root path
  let env ← getEnv
  -- (file, kind, defaults, table) for every table, and the roots
  let mut tables : Array (RecordsFile × String × Lake.Toml.Value × Array (String × Lake.Toml.Value)) := #[]
  let mut roots : Array (RecordsFile × Lake.Toml.Value × String) := #[]
  for f in files do
    match f.table.find? `schema with
    | some (.string _ s) =>
      unless s == recordsSchema do
        throwError "{f.path}: schema {s.quote} is not {recordsSchema.quote}"
    | _ => throwError "{f.path}: a records file starts with `schema = {recordsSchema.quote}`"
    let defaults ← match f.table.find? `defaults with
      | none => pure {}
      | some (.table _ d) => d.items.mapM fun (k, v) => do
        let .table _ t := v
          | throwError "{f.loc v}: `defaults.{leanToName k}` must be a table of keys"
        pure (leanToName k, t)
      | some v => throwError "{f.loc v}: `defaults` must be a table `[defaults.<kind>]`"
    for (k, v) in f.table.items do
      let k := leanToName k
      if k == "schema" || k == "defaults" then continue
      if k == "root" then
        let .string _ r := v | throwError "{f.loc v}: `root` must be a group name"
        roots := roots.push (f, v, r)
        continue
      unless loadKinds.contains k || (handledKinds env).contains k do
        throwError "{f.loc v}: unknown key or kind `{k}`; a records file has `schema`, `root`, \
          `[defaults.<kind>]` and `[[<kind>]]` tables for the kinds {", ".intercalate loadKinds} \
          (or a kind with a registered handler)"
      let .array _ xs := v | throwError "{f.loc v}: `{k}` must be an array of tables `[[{k}]]`"
      let d := (defaults.find? (·.1 == k)).map (·.2)
      for x in xs do
        let .table _ t := x | throwError "{f.loc x}: `{k}` entries must be tables `[[{k}]]`"
        tables := tables.push (f, k, x, withDefaults d t)
    for (k, _) in defaults do
      unless tables.any (fun (g, kind, _) => g.path == f.path && kind == k) do
        logWarning m!"{f.path}: `[defaults.{k}]` applies to no `[[{k}]]` table"
  -- run the tables kind by kind: the built-in order, then project kinds in file order
  let builtin := loadKinds.toArray
  let extra := tables.foldl (init := #[]) fun acc (_, k, _) =>
    if builtin.contains k || acc.contains k then acc else acc.push k
  for kind in builtin ++ extra do
    for (f, k, x, keys) in tables do
      if k == kind then withLoc (f.loc x) (loadTable f kind keys)
  for (f, v, r) in roots do
    withLoc (f.loc v) (runRecord "root" r {})

/-- `silmaril load "PATH"`: read records from TOML (a file, or every records file below a
directory), relative to the package root. -/
@[silmaril_kind load] def loadHandler : Handler where
  run? := some fun _ name? fs => do
    let some path := name? | throwError "silmaril load: give the path: `silmaril load \"silmaril/records.toml\"`"
    unless fs.values.isEmpty do throwError "silmaril load: takes no fields"
    loadRecords path
    return #[]

end Silmaril.Project
