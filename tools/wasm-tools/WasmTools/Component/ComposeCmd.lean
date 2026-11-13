import WasmTools.Component.Run
import Silmaril.Wasm.Tools.Component.Compose.Defs

/-!
# `wasm-tools compose` (deprecated upstream), mapped to `wasm-wac`

The IO half of `Silmaril.Wasm.Tools.Component.Compose`: read the root and the definition
components, resolve every instance import as `wasm-compose`'s `CompositionGraphBuilder` does
(definitions first, then `NAME.wasm`/`NAME.wat` in the root's directory and the search paths,
breadth first, one instance per name), and hand the resolved graph to the pure core
(`Compose.wacText`, `Compose.compose`). Messages are upstream's. `-c`/`--config` reads
wasm-compose's configuration (`Compose.parseConfig`); `import-components: true` is refused.
-/

namespace WasmTools.Component

open Silmaril.Wasm.Tools.Component
open Silmaril.Wasm.Wac (Kind Externs PkgType)

/-- Rust's `Path::set_extension`: replace the extension of the file name (after its last `.`,
not a leading one), else append it. -/
def setExtension (p : System.FilePath) (ext : String) : System.FilePath :=
  let s := p.toString
  let (dir, file) := match s.splitOn "/" with
    | [] => ("", s)
    | parts => ("/".intercalate parts.dropLast, parts.getLastD s)
  let stem := match file.splitOn "." with
    | [] | [_] => file
    | parts => if parts.headD "" == "" && parts.length == 2 then file
      else ".".intercalate parts.dropLast
  let file' := stem ++ "." ++ ext
  if dir.isEmpty && !(s.startsWith "/") then file' else dir ++ "/" ++ file'

/-- `dir.join(name)` (an empty directory is the name itself). -/
def joinDir (dir : String) (name : String) : System.FilePath :=
  if dir.isEmpty then name else System.FilePath.mk dir / name

/-- `Component::from_file`: the component's bytes (text assembled) and its kinds. -/
def readComponent (path : String) : M (ByteArray × PkgType) := do
  let raw ← match ← (IO.FS.readBinFile path).toBaseIO with
    | .ok b => pure b
    | .error e => fail s!"failed to parse component `{path}`\n\nCaused by:\n    0: failed to read from `{path}`\n    1: {osCause e}"
  let b ← match Text.toBinary raw with
    | .ok b => pure b
    | .error e => fail s!"failed to parse component `{path}`\n\nCaused by:\n    {e}"
  if !Cmd.isComponent b then
    fail s!"failed to parse component `{path}`\n\nCaused by:\n    the file is not a WebAssembly component"
  let (p, _) ← match Silmaril.Wasm.Wac.TypeOf.decodeAnyX b with
    | .ok r => pure r
    | .error e => fail s!"failed to parse component `{path}`\n\nCaused by:\n    {e}"
  pure (b, p)

/-- The instance imports of a component. -/
def instImports (p : PkgType) : List (String × Kind) :=
  p.imports.filterMap fun (n, k) => match k.promote with
    | k@(.inst ..) => some (n, k)
    | _ => none

/-- One instance being built: its name, its component (index), and its arguments. -/
structure BInst where
  name : String
  comp : Nat
  args : List (String × Compose.Target) := []
  deriving Inhabited

/-- A component of the composition: its dependency name, path, bytes and kinds. -/
structure BComp where
  name : String
  path : String
  bytes : ByteArray
  ty : PkgType
  deriving Inhabited

/-- One dependency to process: the dependent instance, the import, and the instance (and export)
that should satisfy it. -/
structure Dep where
  dependent : Nat
  imp : String
  kind : Kind
  inst : String
  exp : Option String
  deriving Inhabited

def composeBody (a : ComposeArgs) : M Unit := do
  let quiet := a.quiet
  if !quiet then
    let err ← IO.getStderr
    err.putStrLn "WARNING: `wasm-tools compose` has been deprecated."
    err.putStrLn ""
    err.putStrLn "Please use `wac` instead. You can find more information about `wac` at https://github.com/bytecodealliance/wac."
  let rootPath := a.component
  let parentOf (p : String) : String := match (System.FilePath.mk p).parent with
    | some d => d.toString
    | none => ""
  -- the configuration: `-c FILE` (paths relative to its directory), else a default one next to
  -- the root component
  let (cfg, dir) ← match a.config with
    | none => pure (({} : Compose.Config), parentOf rootPath)
    | some c =>
      match ← (IO.FS.readFile c).toBaseIO with
      | .ok t => pure (Compose.parseConfig t, parentOf c)
      | .error e => fail s!"failed to read configuration file `{c}`\n\nCaused by:\n    {osCause e}"
  if cfg.importComponents then
    fail "configuration `import-components: true` (components imported rather than defined) is not implemented by this wasm-tools (see docs/projects/wasm-components.md)"
  let disallow := a.noImports || cfg.disallowImports
  let cwd ← IO.currentDir
  let defPaths := cfg.definitions.map (fun p => (joinDir dir p).toString) ++
    a.definitions.map fun p => (cwd / p).toString
  let searchDirs := dir :: cfg.searchPaths.map (fun p => (joinDir dir p).toString) ++
    a.searchPath.map fun p => (cwd / p).toString
  let (rb, rt) ← readComponent rootPath
  let mut defs : Array (String × ByteArray × PkgType) := #[]
  for p in defPaths do
    let (b, t) ← readComponent p
    defs := defs.push (p, b, t)
  let mut comps : Array BComp := #[⟨"root", rootPath, rb, rt⟩]
  let mut insts : Array BInst := #[{ name := "root", comp := 0 }]
  let mut queue : List Dep := []
  let mut opened : List (String × Kind × String) := []
  -- `push_dependencies` of instance `i`
  let pushDeps (insts : Array BInst) (comps : Array BComp) (i : Nat) : M (List Dep) := do
    let x := insts[i]!
    let c := comps[x.comp]!
    let args := cfg.arguments x.name
    for (a, _) in args do
      if !c.ty.imports.any (·.1 == a) then
        fail s!"component `{c.path}` has no import named `{a}`"
    pure ((instImports c.ty).map fun (m, k) =>
      match args.lookup m with
      | some arg => ⟨i, m, k, arg.instance_, arg.exp⟩
      | none => ⟨i, m, k, m, none⟩)
  queue ← pushDeps insts comps 0
  if queue.isEmpty then fail s!"component `{rootPath}` does not import any instances"
  let mut fuel := 100000
  while !queue.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let d := queue.head!
    queue := queue.tail
    let dependent := insts[d.dependent]!
    let dcomp := comps[dependent.comp]!
    -- 1. an instance export of a definition component
    match (defs.toList.zipIdx.find? fun ((_, _, t), _) =>
        t.exports.any fun (m, k') => m == d.imp && (match k'.promote with | .inst .. => true | _ => false)) with
    | some ((dp, _, dt), di) =>
      let ek := ((dt.exports.find? (·.1 == d.imp)).map (·.2)).getD d.kind
      if !Silmaril.Wasm.Wac.sub ek d.kind then
        fail s!"failed to connect instance `{dependent.name}` to definition component `{dp}`"
      insts := insts.modify d.dependent fun x => { x with args := x.args ++ [(d.imp, .defn di d.imp)] }
    | none =>
      -- 2. the instance `d.inst` of the component `dependency_name(d.inst)`
      let cname := cfg.dependencyName d.inst
      let found ← match insts.toList.zipIdx.find? (fun (x, _) => x.name == d.inst) with
        | some (_, i) => pure (some (i, false))
        | none => do
          -- the component: already read, an explicit dependency, or found on the search paths
          let ci ← match comps.toList.zipIdx.find? (fun (c, _) => c.name == cname) with
            | some (_, ci) => pure (some ci)
            | none => do
              let path ← match cfg.dependencies.lookup cname with
                | some p => pure (some (joinDir dir p).toString)
                | none => do
                  let mut hit : Option String := none
                  for sd in searchDirs do
                    if hit.isNone then
                      for ext in ["wasm", "wat"] do
                        let p := setExtension (joinDir sd cname) ext
                        if hit.isNone && (← p.pathExists) && !(← p.isDir) then hit := some p.toString
                  pure hit
              match path with
              | none => pure none
              | some p =>
                let (b, t) ← readComponent p
                comps := comps.push ⟨cname, p, b, t⟩
                pure (some (comps.size - 1))
          match ci with
          | none => pure none
          | some ci =>
            insts := insts.push { name := d.inst, comp := ci }
            pure (some (insts.size - 1, true))
      match found with
      | none =>
        if disallow then
          fail s!"a dependency named `{cname}` could not be found and instance imports are not allowed"
        if let some e := d.exp then
          fail s!"an explicit export `{e}` cannot be specified for imported instance `{d.inst}`"
        opened := opened ++ [(d.imp, d.kind, (comps[dependent.comp]!).name)]
      | some (i, fresh) =>
        let x := insts[i]!
        let c := comps[x.comp]!
        let tgt ← match d.exp with
          | some e =>
            match c.ty.exports.find? (fun (m, k) => m == e && (match k.promote with | .inst .. => true | _ => false)) with
            | none => fail s!"component `{c.path}` does not export an instance named `{e}`"
            | some (_, k) =>
              if Silmaril.Wasm.Wac.sub k.promote d.kind then pure (Compose.Target.inst i (some e))
              else fail s!"component `{c.path}` exports an instance named `{e}` but it is not compatible with import `{d.imp}` of component `{dcomp.path}`"
          | none =>
            match Compose.argTarget c.ty.exports d.kind with
            | none => fail s!"component `{c.path}` is not compatible with import `{d.imp}` of component `{dcomp.path}`"
            | some e => pure (Compose.Target.inst i e)
        insts := insts.modify d.dependent fun y => { y with args := y.args ++ [(d.imp, tgt)] }
        if fresh then queue := queue ++ (← pushDeps insts comps i)
  let xs : List Compose.Inst := insts.toList.map fun x => ⟨Compose.instKey x.comp, x.args⟩
  if insts.size == 1 && (Compose.usedDefs xs).isEmpty then
    fail s!"no dependencies of component `{rootPath}` were found"
  let src ← match Compose.wacText xs (defs.toList.zipIdx.map fun (_, d) => Compose.defKey d)
      (!rt.exports.isEmpty) with
    | .ok t => pure t
    | .error _ =>
      -- a cycle: the first instance that cannot be ordered
      let bad := ((Compose.order xs).isNone, insts.toList.find? (fun x => x.name != "root"))
      let n := (bad.2.map fun x => (comps[x.comp]!).name).getD "root"
      fail s!"an instantiation of component `{n}` and its dependencies form a cycle in the instantiation graph"
  let used := Compose.usedDefs xs
  let raw := comps.toList.zipIdx.map (fun (c, i) => (Compose.instKey i, c.bytes)) ++
    (defs.toList.zipIdx.filter (fun (_, d) => used.contains d)).map fun ((_, b, _), d) => (Compose.defKey d, b)
  let b ← match Compose.compose src raw with
    | .ok b => pure b
    | .error e =>
      -- two open imports of one name that wac cannot merge: upstream's message
      match opened.find? (fun (n, _, _) => (e.splitOn s!"importTypeMergeConflict \"{n}\"").length > 1) with
      | some (n, _, owner) =>
        let later := ((opened.filter (·.1 == n)).drop 1).head?.map (·.2.2)
        fail s!"cannot import instance with name `{n}` for an instantiation argument of component `{later.getD owner}` because it conflicts with an imported instantiation argument of component `{owner}`"
      | none => fail e
  writeWasm a.output b a.wat
  if let some o := a.output then
    if !quiet then (← IO.getStdout).putStrLn s!"composed component `{o}`"

end WasmTools.Component
