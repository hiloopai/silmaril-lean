import Silmaril.Wasm.Wac.Tool.Defs
import Silmaril.Wasm.Wac.Targets.Defs
import Silmaril.Wasm.Wac.Bridge.ComposeXV.Defs
import Silmaril.Wasm.Wac.Emit.Defs
import Silmaril.Wasm.Wac.TypeOf.Defs
import Silmaril.Wasm.Wac.TargetsT.Defs
import Silmaril.Wasm.Wac.TypeOfX.Defs
import Silmaril.Wasm.Wac.EmitX.Defs
import Silmaril.Wasm.Wac.EndToEnd.Defs
import Silmaril.Wasm.Wac.StreamFn.Defs
import Silmaril.Wasm.Wac.PlugCheck.Defs
import Silmaril.Wasm.Wac.WatOut.Defs
import Silmaril.Wasm.Wac.WatX.Defs
import Silmaril.Wasm.Wac.WitDir.Defs
import Silmaril.Wasm.Wac.WitOrder.Defs
import Silmaril.Wasm.Wac.DocWit.Defs
import Silmaril.Wasm.Wac.AsyncNames.Defs
import Silmaril.Wasm.Wac.NameAttrs.Defs
import Silmaril.Wasm.Wac.EndToEndR.Defs
import Silmaril.Wasm.Wit.Tool.Defs
import Silmaril.Wasm.Wit.Tool.Source.Defs
import Silmaril.Cli.Spec.Wac.Defs

/-!
# `wasm-wac`

Command-line front end of `Silmaril.Wasm.Wac.Tool`. This file only reads the input files,
calls one pure function of the core and writes its result. See `docs/projects/wasm-components.md`.

```
wasm-wac json   IN.wac [-o OUT.json]   the JSON of `wac parse`, without spans
wasm-wac print  IN.wac [-o OUT.wac]    the document, one space between tokens
wasm-wac pretty IN.wac [-o OUT.wac]    the document, with line breaks
wasm-wac check  IN.wac                 well-formedness and the print/parse round trip
wasm-wac targets COMP.wasm --wit WIT.wasm [--world W]
                                        does the component fit the world (by projection)
wasm-wac compose IN.wac --deps DIR [-o OUT.wat]
                                        elaborate, validate and encode as composition-profile WAT
wasm-wac compose IN.wac --deps DIR --wasm [--import-dependencies] -o OUT.wasm
                                        the composition as a component binary, packages
                                        embedded (as `wac compose`) or imported
wasm-wac plug SOCKET.wasm --plug P.wasm... [--import-dependencies] [--wac] -o OUT
                                        `wac plug`: the plugs' exports satisfy the socket's
                                        imports of the same name (`--wac`: print the document)
wasm-wac encode-wit DIR -o OUT.wasm    a WIT package of one or more files (`WitOrder.encodeTextO`)
wasm-wac parse-wat IN.wat -o OUT.wasm  component WAT with abbreviations (`WatX.parseWatX`)
wasm-wac shapes OUT.wasm [--core-dir D] the packages embedded in a composed binary, as
                                        `StreamFn.binShapes` reads them (`stream NAME CORE-BYTES`
                                        for a stream package, `other` otherwise), and whether
                                        the binary has the checked plug shape (`PlugCheck.plugShape`);
                                        `--core-dir`: write the main core module of stream
                                        package I (what `κ` is applied to) to D/I.wasm
```

The correctness theorem of `compose --wasm` and `plug` is `EndToEnd.composeText_correct`
(`Silmaril.Wasm.Wac.EndToEnd.Thms`): the tool reads the bytes of every package the document needs
and runs `EndToEnd.composeText` on the WAC text and those bytes. It reads the text with the
verified parser, decodes each package's type from its own bytes (`TypeOf.decodeAnyX`), checks
that the elaborated graph has no value nodes, and runs `Emit.composeWasmX`
(`Emit.composeWasmX_correct`, `Silmaril.Wasm.Wac.EmitX.Thms`), which splices the packages'
bytes in and checks that every package's bytes are the canonical encoding of what the parser
with the async built-ins reads (`SpliceX.canonTable`); when the check succeeds, the bytes parse
back (`parseX`) to the embedded composition, which lowers to the elaborated graph, and its
components are the packages. When it fails the tool still writes the bytes and prints a
`note:` on stderr (then only `Emit.composeWasmRaw_correct`, the frame and the graph, applies).
Without packages embedded (`--import-dependencies`) the tool runs `WatOut.composeImpText` on
the text and the package bytes, and the theorem is `Emit.composeWasm_correct`. Without `--wasm`
it prints `WatOut.composeWatText` of the same inputs: `WatOut.composeWatText_correct` (the text
reads back as the normal form of the composition, which lowers to the elaborated graph) and
`WatOut.composeWat_imp_same` (it is the text of the component the `--import-dependencies`
bytes parse to).

`compose` resolves each package `ns:name[@VERSION]` the document needs as wac's
`FileSystemPackageResolver` does: an override `--dep ns:name=PATH` (a `.wasm`, `.wat` or `.wit`
file, or a WIT directory) for a key without version; else `DIR/ns/name[/VERSION]` when it is a
directory (WIT text, encoded by the verified WIT encoder; single-file packages), else that path
with `.wat` when it exists (the verified component WAT reader, a subset of the text format),
else with `.wasm`. `--deps-dir DIR` is `--deps DIR`; the default is `deps`.

`WIT.wasm` is a WIT package in binary form (`wasm-wit encode` or
`wasm-tools component wit --wasm`).

Exit status: 0 on success (for `check`: every check passed), 1 on a failed command or
check, 2 on a usage error.

The command line is read by the grammar `Silmaril.Cli.Spec.Wac.tool` through
`Silmaril.Cli.Clap.Tool.main`: options in any order, `--` ends the options, `-h` prints the derived
help of a command, a usage error prints `error: …` with the derived usage line and exits 2; the
program refines `Wac.tool.spec` (`Silmaril.Cli.Clap.Tool.main_refines`; docs/projects/wasm-binaryen-tooling.md). The one
rule the grammar cannot state, `plug` needs `-o` unless `--wac`, is checked here (exit 2).
-/

open Silmaril.Wasm.Wac.Tool

/-- A usage error found by the program, in the front end's words (exit 2). -/
def usageError (path : List String) (msg : String) : IO UInt32 := do
  IO.eprintln (Silmaril.Cli.Spec.Wac.tool.errorText ("wasm-wac" :: path) msg)
  pure 2

def emitText (out : Option String) (t : String) : IO Unit :=
  match out with
  | some f => IO.FS.writeFile f t
  | none => IO.print t

def orFail {α} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"wasm-wac {what}: {e}")

def yesNo (b : Bool) : String := if b then "yes" else "no"

def run (cmd inp : String) (out : Option String) : IO UInt32 := do
  let src ← IO.FS.readFile inp
  match cmd with
  | "json" => emitText out ((← orFail cmd (parseJson src)) ++ "\n"); pure 0
  | "print" => emitText out ((← orFail cmd (printText src)) ++ "\n"); pure 0
  | "pretty" => emitText out (← orFail cmd (prettyText src)); pure 0
  | "check" =>
    let r ← orFail cmd (check src)
    IO.println s!"statements:  {r.statements}"
    IO.println s!"well-formed: {yesNo r.wellFormed}"
    IO.println s!"print:       {yesNo r.printRoundTrip}"
    IO.println s!"pretty:      {yesNo r.prettyRoundTrip}"
    let ok := r.wellFormed && r.printRoundTrip && r.prettyRoundTrip
    IO.println s!"ok:          {yesNo ok}"
    pure (if ok then 0 else 1)
  | _ => usageError [cmd] s!"unknown command {cmd}"

def targets (comp wit : String) (world : Option String) : IO UInt32 := do
  let cb ← IO.FS.readBinFile comp
  let wb ← IO.FS.readBinFile wit
  -- Typed (`TargetsT.fitsB`, WIT subtyping) when both types can be read; else by projection.
  match Silmaril.Wasm.Wac.TargetsX.check cb wb world with
  | .ok (true, _) => IO.println "ok: the component fits the world (typed)"; pure 0
  | .ok (false, ms) =>
    for m in ms do IO.println s!"misfit: {m}"
    if ms.isEmpty then IO.println "misfit: the component is not a subtype of the world"
    pure 1
  | .error e =>
    IO.eprintln s!"wasm-wac targets: typed check unavailable ({e}); checking names and sorts"
    let r ← orFail "targets" (Silmaril.Wasm.Wac.Targets.check cb wb world)
    match r with
    | [] => IO.println "ok: the component fits the world (names and sorts)"; pure 0
    | ms => for m in ms do IO.println s!"misfit: {m}"
            pure 1

/-- Where packages come from (`wac compose --deps-dir DIR --dep PKG=PATH`). -/
structure Deps where
  dir : String := "deps"
  overrides : List (String × String) := []

/-- The `.wit` files of a directory, sorted. -/
def witFilesOf (dir : String) : IO (List String) := do
  let es ← System.FilePath.readDir dir
  let fs ← es.filterM fun e => do pure (e.fileName.endsWith ".wit" && !(← e.path.isDir))
  pure ((fs.map (·.path.toString)).qsort (· < ·)).toList

/-- The bytes of a WIT package given as text: a `.wit` file, or a directory of `.wit` files
(several files form one package, as wit-parser's `parse_dir` reads them) and possibly `deps/`
(one package per `.wit` file and per subdirectory), encoded by the verified WIT encoder
(`WitOrder.encodeTextO`: `WitDir.encodeTextX`, which is `Wit.Tool.encodeText` for one file it
reads, on the packages with their interfaces in wit-parser's topological order: the bytes of
`wasm-tools component wit --wasm`). -/
def witBytes (key path : String) : IO ByteArray := do
  let isDir ← System.FilePath.isDir path
  let mains ← if isDir then witFilesOf path else pure [path]
  if mains.isEmpty then throw (IO.userError s!"wasm-wac: package `{key}`: no .wit file in {path}")
  let readAll (fs : List String) : IO (List (String × String)) := fs.mapM fun (f : String) => do
    pure (f, ← IO.FS.readFile (System.FilePath.mk f))
  let depDir := System.FilePath.mk path / "deps"
  let mut deps : List (List (String × String)) := []
  if isDir && (← depDir.isDir) then
    for f in ← witFilesOf depDir.toString do deps := deps ++ [← readAll [f]]
    let es ← System.FilePath.readDir depDir
    let subs ← es.filterM fun e => e.path.isDir
    for d in (subs.map (·.path.toString)).qsort (· < ·) do
      let fs ← witFilesOf d
      if !fs.isEmpty then deps := deps ++ [← readAll fs]
  orFail s!"package `{key}` ({path})" ((Silmaril.Wasm.Wac.WitOrder.encodeTextO (← readAll mains) deps).map Silmaril.Wasm.Wac.AsyncNames.fixBytes)

/-- The bytes of a package file: `.wit` text, `.wat` (the component WAT reader with abbreviations,
`WatX.parseWatX`, = `Wit.Tool.parseWat` where that reads the text) or a binary. -/
def fileBytes (key path : String) : IO ByteArray := do
  if (← System.FilePath.isDir path) || path.endsWith ".wit" then witBytes key path
  else if path.endsWith ".wat" then
    orFail s!"package `{key}` ({path})" (Silmaril.Wasm.Wac.WatX.parseWatX (← IO.FS.readFile path))
  else IO.FS.readBinFile path

/-- The bytes of a package, resolved as wac's `FileSystemPackageResolver` does: an override
`--dep ns:name=PATH` (for a key without version); else `DIR/ns/name[/VERSION]` as a directory
of WIT text, else that path with `.wat` when it exists, else with `.wasm`. -/
def depBytes (deps : Deps) (key : String) : IO ByteArray := do
  let (name, ver) := match key.splitOn "@" with
    | [n, v] => (n, some v)
    | _ => (key, none)
  if let (some f, none) := (deps.overrides.lookup name, ver) then
    if !(← System.FilePath.pathExists f) then
      throw (IO.userError s!"wasm-wac: local path `{f}` for package `{name}` does not exist")
    return ← fileBytes key f
  let base := (name.splitOn ":").foldl (fun acc s => acc ++ "/" ++ s) deps.dir
  let path := match ver with | some v => base ++ "/" ++ v | none => base
  if ← System.FilePath.isDir path then return ← witBytes key path
  if ← System.FilePath.pathExists (path ++ ".wat") then return ← fileBytes key (path ++ ".wat")
  if ← System.FilePath.pathExists (path ++ ".wasm") then return ← IO.FS.readBinFile (path ++ ".wasm")
  throw (IO.userError s!"wasm-wac: package `{key}` not found in {deps.dir}")

/-- The bytes of the packages a document needs, by key, read through `get`. -/
def readRaw (d : Silmaril.Wasm.Wac.FuncAlias.Document) (get : String → IO ByteArray) :
    IO (List (String × ByteArray)) := do
  let mut raw : List (String × ByteArray) := []
  for k in Silmaril.Wasm.Wac.Bridge.pkgKeysX d do
    raw := raw ++ [(k, ← get k)]
  pure raw

/-- `compose` without `--wasm`: the WAT is `WatOut.composeWatText src raw` for the bytes `raw`
of the packages (`WatOut.composeWatText_correct`). -/
def compose (inp : String) (deps : Deps) (out : Option String) : IO UInt32 := do
  let src ← IO.FS.readFile inp
  let d ← orFail "compose" (Silmaril.Wasm.Wac.Bridge.readDocX src)
  let raw ← readRaw d (depBytes deps)
  emitText out (← orFail "compose" (Silmaril.Wasm.Wac.EndToEndR.composeWatTextR src raw))
  pure 0

/-- Read a package binary and its type, decoded from the binary (`TypeOf.decodeAnyX`: the
world by projection, else inference over the extended parse with the async built-ins). -/
def readPkg (f : String) : IO (Silmaril.Wasm.Wac.PkgType × Silmaril.Wasm.Wac.Bridge.NomTable × ByteArray) := do
  let bytes ← IO.FS.readBinFile f
  let (p, n) ← orFail s!"({f})" (Silmaril.Wasm.Wac.TypeOf.decodeAnyX bytes)
  pure (p, n, bytes)

/-- Compose a document to a binary against packages read by `get`. With packages embedded,
the bytes written are `EndToEnd.composeText src raw` for the bytes `raw` of the packages. -/
def composeBin (src : String) (get : String → IO ByteArray) (embed : Bool) (out : String) :
    IO UInt32 := do
  let d ← orFail "compose" (Silmaril.Wasm.Wac.Bridge.readDocX src)
  -- a type-only document the main pipeline refuses (definitions that `use` types of other
  -- interfaces): the verified WIT elaborator and encoder (`DocWit.composeTypes`)
  let typesOnly : IO (Option ByteArray) := do
    if (Silmaril.Wasm.Wac.DocWit.defsOf d.forget.stmts).isSome then
      match Silmaril.Wasm.Wac.DocWit.composeTypes src (← readRaw d get) with
      | .ok b => pure (some b)
      | .error _ => pure none
    else
      match Silmaril.Wasm.Wac.DocWit.composeMixed src (← readRaw d get) with
      | .ok b => pure (some b)
      | .error _ => pure none
  let main : IO ByteArray := if embed then do
      let raw ← readRaw d get
      orFail "compose" (Silmaril.Wasm.Wac.TextCheck.checkText src)
      -- `composeTextF` is `EndToEnd.composeText` (`composeTextF_eq`); when it succeeds it is
      -- `composeTextR` (`composeTextR_of_ok`), else `composeTextR` uses the shared-resource encoder.
      let (b, tbl, nv) ← match Silmaril.Wasm.Wac.EndToEndR.composeTextF src raw with
        | .ok r => pure r
        | .error _ => do
          let r ← orFail "compose" (Silmaril.Wasm.Wac.EndToEndR.composeTextR src raw)
          IO.eprintln "wasm-wac: info: written by the shared-resource encoder (EncodeR); composeTextR_cases applies, composeText_correct does not"
          pure r
      if tbl.isNone then
        IO.eprintln "wasm-wac: note: a package's bytes are not the canonical encoding of their parse (parseX/encodeX); the output is spliced but composeText_correct does not apply"
      if !nv then
        IO.eprintln "wasm-wac: note: the composition has value nodes; composeText_correct does not apply"
      pure b
    else do
      orFail "compose" (Silmaril.Wasm.Wac.EndToEndR.composeImpTextR src (← readRaw d get))
  let b ← try main catch e => do
    match ← typesOnly with
    | some b =>
      IO.eprintln "wasm-wac: info: a type-only document written by the WIT elaborator and encoder (DocWit.composeTypes)"
      pure b
    | none => throw e
  -- `(implements …)` and other name attributes of the packages' imports and exports
  -- (`NameAttrs.patch`: the bytes are unchanged when no package name has attributes)
  let b := Silmaril.Wasm.Wac.NameAttrs.patch ((← readRaw d get).map (·.2)) b
  IO.FS.writeBinFile out b
  pure 0

/-- `plug`. -/
def plug (socket : String) (plugs : List String) (embed wac : Bool) (out : Option String) :
    IO UInt32 := do
  let (sp, _, _) ← readPkg socket
  let mut pts : List Silmaril.Wasm.Wac.PkgType := []
  for f in plugs do
    let (p, _, _) ← readPkg f
    pts := pts ++ [p]
  let src ← orFail "plug" (Silmaril.Wasm.Wac.Emit.plugDoc sp pts)
  if wac then emitText out src; return 0
  let files := (Silmaril.Wasm.Wac.Emit.socketKey, socket) ::
    plugs.zipIdx.map fun (f, i) => (Silmaril.Wasm.Wac.Emit.plugKey i, f)
  let get (k : String) : IO ByteArray := match files.lookup k with
    | some f => IO.FS.readBinFile f
    | none => throw (IO.userError s!"wasm-wac plug: unknown package {k}")
  match out with
  | some o => composeBin src get embed o
  | none => usageError ["plug"] "-o OUT is required unless --wac is given"

/-- `shapes`: the embedded packages of a binary (`StreamFn.binShapes`) and its plug shape
(`PlugCheck.plugShape`). -/
def shapes (f : String) (coreDir : Option String) : IO UInt32 := do
  let b ← IO.FS.readBinFile f
  let l ← orFail "shapes" (Silmaril.Wasm.Wac.StreamFn.binShapes b)
  for (o, i) in l.zipIdx do
    match o with
    | some s =>
      IO.println s!"package {i}: stream {s.name} {s.core.size}"
      if let some d := coreDir then IO.FS.writeBinFile s!"{d}/{i}.wasm" s.core
    | none => IO.println s!"package {i}: other"
  IO.println s!"plug shape: {yesNo (Silmaril.Wasm.Wac.PlugCheck.plugShape b)}"
  pure 0

/-- `compose`, on its matches. -/
def composeCmd (m : Silmaril.Cli.Matches) : IO UInt32 := do
  let str (k : String) : String := (m.str? k).getD ""
  -- `PKG=PATH` (the grammar's check: a `=` with a nonempty key)
  let split (kv : String) : Option (String × String) :=
    match kv.splitOn "=" with
    | k :: v :: vs => some (k, "=".intercalate (v :: vs))
    | _ => none
  let some overrides := (m.strs "dep").mapM split
    | usageError ["compose"] "invalid value for '--dep <PKG=PATH>'"
  let deps : Deps := { dir := (m.str? "deps").getD "deps", overrides }
  if m.flag "wasm" then
    -- `--wasm` requires `-o` (the grammar's rule)
    composeBin (← IO.FS.readFile (str "in")) (depBytes deps) (!m.flag "import-dependencies")
      (str "-o")
  else compose (str "in") deps (m.str? "-o")

/-- The commands, on the matches of `Silmaril.Cli.Spec.Wac.tool`. -/
def runMatches (m : Silmaril.Cli.Matches) : IO UInt32 := do
  let str (k : String) : String := (m.str? k).getD ""
  match m.path with
  | ["compose"] => composeCmd m
  | ["plug"] =>
    let embed := !m.flag "import-dependencies"
    plug (str "socket") (m.strs "plug") embed (m.flag "wac") (m.str? "-o")
  | ["encode-wit"] =>
    -- the WIT reader `compose` uses for packages given as text (`WitOrder.encodeTextO`)
    IO.FS.writeBinFile (str "-o") (← witBytes "encode-wit" (str "src"))
    pure 0
  | ["parse-wat"] =>
    -- the reader `compose` uses for `.wat` packages (`WatX.parseWatX`)
    IO.FS.writeBinFile (str "-o")
      (← orFail "parse-wat" (Silmaril.Wasm.Wac.WatX.parseWatX (← IO.FS.readFile (str "in"))))
    pure 0
  | ["shapes"] => shapes (str "bin") (m.str? "core-dir")
  | ["targets"] => targets (str "comp") (str "wit") (m.str? "world")
  | [cmd] => run cmd (str "in") (m.str? "-o")
  | p => usageError p "no such command"

def main : List String → IO UInt32 := Silmaril.Cli.Spec.Wac.tool.main runMatches
