module

public import Silmaril.Project.Registry.Dag.Defs
public import Silmaril.Project.Registry.Artifacts.Defs
public import Silmaril.Data.IncludeBytes
public import Silmaril.Project.Core.Thms

/-!
# Silmaril projects: formats and values (layer 3)

The kinds over `Silmaril.Project.Core` (`ArtifactType`, `Format`, `Value`):

| kind | Lean checks | Lean fills |
|---|---|---|
| `artifact_type` | `decl : ArtifactType` | |
| `format` | `decl : Format T V`, an `artifact_type` with decl `T`; not a family | `input`, `value_type`, `printer` |
| `format_default` | the target is a format `<family>.…`; the family is not a format | |
| `format_law` | `proof : RoundTrip F` or `SoundFor F rel` | |

and the sugar forms:

* `silmaril format_law F law := proof (rel := R)`;
* `silmaril value N : fmt := src (| fmt := src)* (k := v)*`: a named value, its
  `include_bytes` declarations, the obligation `N.parses` and one `N.agrees.k` per extra
  source;
* `silmaril problem N about X (k := v)* : P [:= proof]`: the problem `X.Satisfies P`, its
  `children` edges to X's obligations and the proved route `¬ X.parses → ¬ N`; with a proof,
  the solutions `N.sol` and `N.parses_sol`.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command
open Silmaril.Problems (validId problems solutions problemDecl? moduleOf allEntries)

/-- `(T, V)` of a constant of type `Format T V`. -/
def formatArgs (kind : String) (F : Name) : MetaM (Expr × Expr) := do
  let ty ← whnfR (← constType F)
  unless ty.isAppOfArity ``Format 2 do
    throwError "silmaril {kind}: {F} has type{indentExpr ty}\nbut a format is a `Silmaril.Project.Format T V`"
  return (ty.getArg! 0, ty.getArg! 1)

/-- `artifact_type N := decl`, `decl : ArtifactType`. -/
@[silmaril_kind artifact_type] def artifactTypeHandler : Handler where
  run? := some fun kind name? fs => liftTermElabM do
    let d ← fs.const kind "decl"
    expectType kind m!"{d}" (← constType d) (mkConst ``ArtifactType)
    return #[(← needName kind name?, fs)]

/-- `format N := decl`, `decl : Format T V` for a registered artifact type `T`. -/
@[silmaril_kind format] def formatHandler : Handler where
  run? := some fun kind name? fs => liftTermElabM do
    let name ← needName kind name?
    if (findRecord? (← getEnv) "format_default" name).isSome then
      throwError "silmaril format: {name.quote} is a format family; a name is a format or a family"
    let F ← fs.const kind "decl"
    let (T, V) ← formatArgs kind F
    let mut input? := none
    for r in records (← getEnv) do
      if r.kind == "artifact_type" then
        if let some d := r.str? "decl" then
          if ← isDefEq T (mkConst d.toName) then input? := some r.name
    let some input := input?
      | throwError "silmaril format: {F} reads{indentExpr T}\nwhich is no registered `artifact_type`"
    let print ← whnf (mkApp3 (mkConst ``Format.print) T V (mkConst F))
    let printer ← match print.getAppFn.constName? with
      | some ``Option.some => pure true
      | some ``Option.none => pure false
      | _ => throwError "silmaril format: cannot tell whether {F} has a printer \
          (is its value exposed?){indentExpr print}"
    let fs ← fs.push kind "input" (.str input)
    let fs ← fs.push kind "value_type" (.str (← ppOneLine V))
    let fs ← fs.push kind "printer" (.bool printer)
    return #[(name, fs)]

/-- `format_default FAMILY := FORMAT`. -/
@[silmaril_kind format_default] def formatDefaultHandler : Handler where
  mainKey := "format"
  formatRef := false
  run? := some fun kind name? fs => do
    let family ← liftCoreM (needName kind name?)
    let target ← liftCoreM (fs.str kind "format")
    if (findRecord? (← getEnv) "format" family).isSome then
      throwError "silmaril format_default: {family.quote} is a format; a name is a format or a family"
    unless (findRecord? (← getEnv) "format" target).isSome do
      throwError "silmaril format_default: no `silmaril format {target}` is declared or imported"
    unless target.startsWith (family ++ ".") do
      throwError "silmaril format_default: the default of family {family.quote} must be named \
        `{family}.…`, not {target.quote}"
    return #[(family, fs)]

/-- `format_law (format := F) (law := roundtrip|sound) := proof (rel := R)`. -/
@[silmaril_kind format_law] def formatLawHandler : Handler where
  mainKey := "proof"
  run? := some fun kind name? fs => liftTermElabM do
    let proof ← fs.const kind "proof"
    let F ← recordDecl kind "format" (← fs.str kind "format")
    let (T, V) ← formatArgs kind F
    let expected ← match ← fs.str kind "law" with
      | "roundtrip" => pure (mkApp3 (mkConst ``Format.RoundTrip) T V (mkConst F))
      | "sound" => pure (mkApp4 (mkConst ``Format.SoundFor) T V (mkConst F) (mkConst (← fs.const kind "rel")))
      | law => throwError "silmaril format_law: unknown law {law.quote}; expected `roundtrip` or `sound`"
    expectType kind m!"{proof}" (← constType proof) expected
    return #[(name?.getD proof.toString, fs)]

/-- `silmaril format_law F law := proof (rel := R)`. -/
syntax (name := silmarilLawCmd) "silmaril " &"format_law" ppSpace silmarilName ppSpace ident " := " ident
  (ppSpace silmarilField)* : command

@[command_elab silmarilLawCmd]
def elabSilmarilLaw : CommandElab := fun stx => do
  let proof ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[5])
  let fs : Fields := { values := #[("format", .str (nameOf stx[2])), ("law", .str stx[3].getId.toString),
    ("proof", .str proof.toString)], consts := #[("proof", proof)] }
  runRecord "format_law" none (← liftCoreM (elabFields "format_law" stx[6].getArgs fs))

/-- One source of a value: `format := path | cid | registry-name`. -/
syntax silmarilSource := silmarilName " := " silmarilValue

/-- `silmaril value N : fmt := src (| fmt := src)* (k := v)*`. -/
syntax (name := silmarilValueCmd) "silmaril " &"value" ppSpace silmarilName " : " silmarilSource
  (" | " silmarilSource)* (ppSpace silmarilField)* : command

/-- How a value source names its registry entry. -/
inductive SourceRef where
  /-- A CID (`bafkr…`) or a path relative to the package root (a string in a command). -/
  | text (s : String)
  /-- A registry name (an identifier in a command). -/
  | name (n : String)
  /-- Any of the three (TOML): a CID, else a registry path, else a registry name. -/
  | auto (s : String)

/-- The registry entry of a source: `(cid, path, size)`. -/
def findArtifact (src : SourceRef) : CommandElabM (String × String × Nat) := do
  let arts := (records (← getEnv)).filter (·.kind == "artifact")
  let pathsOf (r : Record) : List String := match r.get? "paths" with
    | some (.arr ps) => ps.toList.filterMap fun | .str p => some p | _ => none
    | _ => []
  let byText (s : String) :=
    if s.startsWith "bafkr" then
      let r := arts.find? (·.str? "cid" == some s)
      (r, r.bind (pathsOf · |>.head?))
    else (arts.find? (pathsOf · |>.contains s), some s)
  let byName (n : String) :=
    let r := arts.find? fun r => r.name == n && r.str? "cid" != some n
    (r, r.bind (pathsOf · |>.head?))
  let (want, found, path?) := match src with
    | .text s => (s, byText s)
    | .name n => (n, byName n)
    | .auto s => (s, match byText s with | (some r, p) => (some r, p) | _ => byName s)
  let some r := found
    | throwError "silmaril value: {want.quote} is in no imported artifact registry \
        (add it to `silmaril/artifacts.toml` and run `sil project lock`)"
  if (r.get? "package").isSome then
    throwError "silmaril value: v0.1 reads values only from the package's own blobs; \
      {want.quote} has `package` set"
  let some path := path? | throwError "silmaril value: {want.quote} has no `paths`"
  let some (.num ⟨size, 0⟩) := r.get? "size"
    | throwError "silmaril value: {want.quote} has no `size`; run `sil project lock`"
  return ((r.str? "cid").getD "", path, size.toNat)

/-- Declare the value `name` from its sources `(format, source, ref)`: the first is the value,
the others must agree with it, and errors about a source are reported at its `ref`. Adds the
`include_bytes` declarations, the obligations `name.parses` and `name.agrees.k`, and the `value`
record with the fields `fs`. Shared by `silmaril value` and `silmaril load`. -/
def declareValue (name : String) (sources : Array (String × SourceRef × Syntax)) (fs : Fields) :
    CommandElabM Unit := do
  let (root, up) ← packageRoot
  let decl ← fullName name
  let altName (k : Nat) := subName (name ++ ".alt") (.inr (k - 1))
  let mut out := #[]
  let mut formats := #[]
  for h : k in [0:sources.size] do
    let (fmt, src, ref) := sources[k]
    let vname := if k == 0 then name else altName k
    let (fmt, source) ← withRef ref do
      let fmt ← liftCoreM (resolveFormat fmt)
      let fdecl ← liftCoreM (recordDecl "value" "format" fmt)
      let (cid, path, size) ← findArtifact src
      let bytes ← try IO.FS.readBinFile (root / path) catch _ =>
        throwError "silmaril value: cannot read {path} (relative to the package root {root})"
      unless bytes.size == size do
        throwError "silmaril value: {path} has {bytes.size} bytes, the registry says {size}; \
          run `sil project lock`"
      elabDef false (nameToLean vname) #[] none
        (← `(Silmaril.Project.Value.mk $(mkCIdent fdecl) ⟨include_bytes $(quote (up ++ path))⟩))
      -- named in messages about the value (`silmaril_decide`)
      addDocStringCore (← fullName vname) s!"`{path}`, read as `{fmt}`"
      return (fmt, Json.mkObj [("cid", .str cid), ("path", .str path), ("format", .str fmt),
        ("decl", .str (← fullName vname).toString)])
    formats := formats.push fmt
    out := out.push source
  -- the obligations: `N.parses`, and `N.agrees.k` for each extra source
  let parses := name ++ ".parses"
  elabDef false (nameToLean parses) #[← problemAttr parses] (some (← `(Prop)))
    (← `(Silmaril.Project.Value.Parses $(mkCIdent decl)))
  let mut agrees := #[]
  for k in [1:sources.size] do
    let a := subName (name ++ ".agrees") (.inr (k - 1))
    elabDef false (nameToLean a) #[← problemAttr a] (some (← `(Prop)))
      (← `(Silmaril.Project.Value.Agrees $(mkCIdent decl) $(mkCIdent (← fullName (altName k)))))
    agrees := agrees.push (Json.str a)
  let mut fs := fs
  for (k, v) in [("decl", Json.str decl.toString), ("format", .str formats[0]!),
      ("parses", .str parses), ("agrees", .arr agrees), ("sources", .arr out)] do
    fs ← liftCoreM (fs.push "value" k v)
  runRecord "value" name fs

/-- A source in a command: a string is a CID or a path, an identifier a registry name. -/
def sourceRefOf (src : Syntax) : CommandElabM SourceRef :=
  match src with
  | `(silmarilValue| $s:str) => return .text s.getString
  | `(silmarilValue| $i:ident) => return .name (leanToName i.getId)
  | _ => throwErrorAt src "silmaril value: a source is a CID or path (a string) or a registry name"

@[command_elab silmarilValueCmd]
def elabSilmarilValue : CommandElab := fun stx => do
  let sources ← (#[stx[4]] ++ stx[5].getArgs.map (·[1])).mapM fun s =>
    return (nameOf s[0], ← sourceRefOf s[2], s)
  declareValue (nameOf stx[2]) sources (← liftCoreM (elabFields "value" stx[6].getArgs))

/-- `silmaril problem N about X (k := v)* : P [:= proof]`: the problem `X.Satisfies P`. -/
syntax (name := silmarilAboutCmd) "silmaril " "problem " silmarilName ppSpace &"about" ppSpace silmarilName
  (ppSpace silmarilField)* " : " term (" := " term)? : command

@[command_elab silmarilAboutCmd]
def elabSilmarilAbout : CommandElab := fun stx => do
  let name := nameOf stx[2]
  let x := nameOf stx[4]
  let some v := findRecord? (← getEnv) "value" x
    | throwErrorAt stx[4] "silmaril problem: no `silmaril value {x}` is declared or imported"
  let some xdecl := v.str? "decl" | throwError "silmaril problem: value {x} has no `decl`"
  let parses := (v.str? "parses").getD (x ++ ".parses")
  let some parsesDecl := problemDecl? (← getEnv) parses
    | throwError "silmaril problem: the obligation {parses} of {x} is not a problem"
  let obligations := #[Json.str parses] ++ (match v.get? "agrees" with | some (.arr a) => a | _ => #[])
  let decl ← fullName name
  elabDef false (nameToLean name) #[← problemAttr name] (some (← `(Prop)))
    (← `(Silmaril.Project.Value.Satisfies $(mkCIdent xdecl.toName) $(⟨stx[7]⟩)))
  -- the proved route: a refuted parse refutes the problem
  let route := name ++ ".parses_route"
  elabDef true (nameToLean route) #[] (some (← `(¬ $(mkCIdent parsesDecl) → ¬ $(mkCIdent decl))))
    (← `(fun h hp => h (Silmaril.Project.Value.parses_of_satisfies hp)))
  if stx[8].getNumArgs == 2 then
    elabDef true (nameToLean (name ++ ".sol")) #[] (some (mkCIdent decl)) ⟨stx[8][1]⟩
    let sol ← fullName (name ++ ".sol")
    -- A failed proof is already reported: do not add "depends on `sorryAx`" errors about the
    -- solutions it would have given.
    unless ((← getEnv).find? sol |>.bind (·.value? (allowOpaque := true))).all (·.hasSyntheticSorry) do
      elabCommand (← `(attribute [solves $(quote name):str] $(mkCIdent sol)))
      -- a solved problem about `X` also solves `X.parses`
      elabDef true (nameToLean (name ++ ".parses_sol"))
        #[← `(Lean.Parser.Term.attrInstance| solves $(quote parses):str)] (some (mkCIdent parsesDecl))
        (← `(Silmaril.Project.Value.parses_of_satisfies $(mkCIdent sol)))
  let fs ← liftCoreM (elabFields "problem" stx[5].getArgs)
  runRecord "judgement" name (← liftCoreM (fs.push "judgement" "values" (.arr #[.str x])))
  runRecord "children" name { values := #[("children", .arr obligations)] }
  let routeDecl ← fullName route
  runRecord "refutation_route" none
    { values := #[("proof", .str routeDecl.toString)], consts := #[("proof", routeDecl)] }

end Silmaril.Project
