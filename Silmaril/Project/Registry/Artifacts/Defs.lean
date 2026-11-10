module

public import Silmaril.Project.Registry.Defs
public meta import Lake.Toml

/-!
# Silmaril projects: artifacts (layer 2)

`silmaril artifacts "silmaril/artifacts.toml"` reads the package's TOML artifact registry (path
relative to the package root) and adds one `artifact` record per entry. `silmaril artifact` is not a command: artifacts are listed
in the registry file, which `sil project lock` writes. Build provenance (`[[derivation]]`, schema
`silmaril.artifacts.v0.2`) is checked by `sil project check` only; Lean ignores it.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command
open Silmaril.Problems (validId problems solutions problemDecl? moduleOf allEntries)

/-- The schema string of the TOML artifact registry. -/
def artifactsSchema : String := "silmaril.artifacts.v0.2"

/-- The schema strings `silmaril artifacts` reads: v0.2 adds build provenance (`[[derivation]]`
tables and an artifact's `derivation`), which `sil project check` checks and Lean ignores. -/
def artifactsSchemas : List String := ["silmaril.artifacts.v0.1", artifactsSchema]

/-- A TOML value as JSON (strings, integers, booleans, arrays of those). -/
partial def tomlJson? : Lake.Toml.Value → Option Json
  | .string _ s => some (.str s)
  | .integer _ n => some (Lean.toJson n)
  | .boolean _ b => some (.bool b)
  | .array _ xs => (xs.toList.mapM tomlJson?).map (Json.arr ∘ List.toArray)
  | _ => none

/-- The registry keys an `artifact` record carries; the digests (`sha256`, `git_sha1`) are
checked by `sil project check` against the files and are not copied. -/
def artifactKeys : List String := ["cid", "type", "package", "paths", "size", "doc"]

/-- Read a TOML artifact registry into `artifact` records (named by their `name`, or keyed by
their `cid` when unnamed). -/
def importArtifacts (path : String) (fs : Fields) : CommandElabM Unit := do
  let (root, _) ← packageRoot
  let file := root / path
  let text ← try IO.FS.readFile file catch _ =>
    throwError "silmaril artifacts: cannot read {path} (relative to the package root {root})"
  let ictx := Parser.mkInputContext text path
  let table ← match ← (Lake.Toml.loadToml ictx).toBaseIO with
    | .ok t => pure t
    | .error log =>
      let msgs ← log.toList.mapM (·.toString)
      throwError "silmaril artifacts: {path} is not TOML:\n{"\n".intercalate msgs}"
  unless (match table.find? `schema with | some (.string _ s) => artifactsSchemas.contains s | _ => false) do
    throwError "silmaril artifacts: {path} must start with `schema = {artifactsSchema.quote}`"
  let entries := match table.find? `artifact with
    | some (.array _ xs) => xs
    | _ => #[]
  let module := (← getEnv).mainModule
  for e in entries do
    let .table _ t := e | throwError "silmaril artifacts: {path}: `[[artifact]]` entries are tables"
    let mut out := fs
    let mut name? := none
    for (k, v) in t.items do
      let k := leanToName k
      -- tool-only keys: `meta` (any table) is not read here
      unless k == "name" || artifactKeys.contains k do continue
      let some j := tomlJson? v | throwError "silmaril artifacts: {path}: unsupported value for `{k}`"
      if k == "name" then name? := some j
      else if artifactKeys.contains k then out ← liftCoreM (out.push "artifact" k j)
    let some (.str cid) := out.get? "cid"
      | throwError "silmaril artifacts: {path}: an entry has no `cid`; run `sil project lock`"
    unless cid.startsWith "bafkr4i" && cid.length == 59 &&
        cid.all (fun c => c.isLower || ('2' ≤ c && c ≤ '7')) do
      throwError "silmaril artifacts: {path}: {cid.quote} is not a raw BLAKE3 CIDv1 \
        (`bafkr4i…`, 59 characters)"
    if (out.get? "sid").isSome then
      throwError "silmaril artifacts: {path}: an artifact's sid is its content digest; no `sid`"
    let ty := (out.get? "type").getD (.str "blob")
    let env ← getEnv
    unless (match ty with | .str s => (findRecord? env "artifact_type" s).isSome | _ => false) do
      throwError "silmaril artifacts: {path}: {ty.compress} is not a registered artifact_type"
    let name ← match name? with
      | none => pure cid
      | some (.str n) => pure n
      | some j => throwError "silmaril artifacts: {path}: `name` must be a string, not {j.compress}"
    liftCoreM (addRecord { kind := "artifact", name, module, fields := out.values })


/-- `artifacts "PATH"`: import a TOML registry. -/
@[silmaril_kind artifacts] def artifactsHandler : Handler where
  run? := some fun _ name? fs => do
    let some path := name? | throwError "silmaril artifacts: give the registry path"
    importArtifacts path fs
    return #[]

/-- Artifacts come from the registry file. -/
@[silmaril_kind artifact] def artifactHandler : Handler where
  run? := some fun _ _ _ =>
    throwError "silmaril artifact: list artifacts in the TOML registry (`silmaril/artifacts.toml`) \
      and import it with `silmaril artifacts \"silmaril/artifacts.toml\"`"

end Silmaril.Project
