module

public import Silmaril.Project.Registry.Artifacts.Defs
public meta import Lake.Toml

/-!
# Silmaril projects: artifacts added after the registry was imported

`silmaril_artifacts_refresh "silmaril/artifacts.toml"` reads the package's artifact registry
like `silmaril artifacts` (`Silmaril.Project.Registry.Artifacts.Defs`) and adds an `artifact`
record for each entry that no imported module declared yet; entries already declared are left
alone. Lake does not see the registry file, so a cached build of `Silmaril.Project.Defs` (which
imports Silmaril's registry) can predate entries that `sil project components add` wrote since. A
module whose values come from such entries runs this command first; on a fresh build it adds
nothing. The records are the ones `silmaril artifacts` writes, and `sil project check` checks
them against the same file.
-/

public meta section

namespace Silmaril.Project

open Lean Elab Command Silmaril.Project

/-- Add the registry entries at `path` that have no `artifact` record yet; returns how many. -/
def refreshArtifacts (path : String) : CommandElabM Nat := do
  let (root, _) ← packageRoot
  let text ← try IO.FS.readFile (root / path) catch _ =>
    throwError "silmaril_artifacts_refresh: cannot read {path} (relative to the package root {root})"
  let ictx := Parser.mkInputContext text path
  let table ← match ← (Lake.Toml.loadToml ictx).toBaseIO with
    | .ok t => pure t
    | .error _ => throwError "silmaril_artifacts_refresh: {path} is not TOML"
  unless (match table.find? `schema with
      | some (.string _ s) => artifactsSchemas.contains s | _ => false) do
    throwError "silmaril_artifacts_refresh: {path} must start with `schema = {artifactsSchema.quote}`"
  let entries := match table.find? `artifact with
    | some (.array _ xs) => xs
    | _ => #[]
  let module := (← getEnv).mainModule
  let mut added := 0
  for e in entries do
    let .table _ t := e | throwError "silmaril_artifacts_refresh: {path}: entries are tables"
    let mut out : Fields := {}
    let mut name? := none
    for (k, v) in t.items do
      let k := leanToName k
      unless k == "name" || artifactKeys.contains k do continue
      let some j := tomlJson? v
        | throwError "silmaril_artifacts_refresh: {path}: unsupported value for `{k}`"
      if k == "name" then name? := some j
      else out ← liftCoreM (out.push "artifact" k j)
    let some (.str cid) := out.get? "cid"
      | throwError "silmaril_artifacts_refresh: {path}: an entry has no `cid`; run `sil project lock`"
    let name := match name? with
      | some (.str n) => n
      | _ => cid
    if (findRecord? (← getEnv) "artifact" name).isSome then continue
    liftCoreM (addRecord { kind := "artifact", name, module, fields := out.values })
    added := added + 1
  return added

/-- `silmaril_artifacts_refresh "PATH"`: add the registry entries not declared yet. -/
syntax (name := artifactsRefresh) "silmaril_artifacts_refresh " str : command

@[command_elab artifactsRefresh] def elabArtifactsRefresh : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwError "silmaril_artifacts_refresh: give the registry path"
  discard <| refreshArtifacts path

end Silmaril.Project
