import Silmaril.Wasm.JcoTool.ToolI.Defs
import Silmaril.Wasm.JcoTool.StreamSem.Defs
import Silmaril.Wasm.JcoTool.KCore.Defs
import Silmaril.Wasm.JcoTool.KCoreEmit.Defs
import Silmaril.Wasm.JcoTool.KDropEmit.Defs
import Silmaril.Wasm.JcoTool.KFitBuf.Defs
import Silmaril.Wasm.JcoTool.Layout.Defs
import Silmaril.Wasm.JcoTool.LayoutRef.Defs
import Silmaril.Wasm.JcoTool.AdaptorI.Defs
import Silmaril.Wasm.JcoTool.RefSimple.Defs
import Silmaril.Wasm.JcoTool.RefSimpleI.Defs
import Silmaril.Wasm.JcoTool.LayoutRefX.Defs
import Silmaril.Wasm.JcoTool.Front.Defs
import Silmaril.Wasm.JcoTool.Adapt.Defs
import Silmaril.Wasm.JcoTool.AdaptLayout.Defs
import Silmaril.Wasm.JcoTool.Cm32.Defs
import Silmaril.Wasm.Perf.JcoNew.Defs
import Silmaril.Wasm.Perf.JcoMain.Defs
import Silmaril.Wasm.JcoTool.NewMain.Defs
import Silmaril.Wasm.JcoTool.WitOf.Defs
import Silmaril.Wasm.Wit.Binary.Embed.Defs
import Silmaril.Wasm.Wac.WitDir.Defs
import Silmaril.Wasm.Perf.WatPrint.Defs
import Silmaril.Cli.Spec.Jco.Defs

/-!
# `wasm-jco`

Command-line front end of `Silmaril.Wasm.JcoTool.Tool`. This file only reads the input files,
calls one pure function of the core and writes its result. See `docs/projects/wasm-components.md`.

```
wasm-jco new CORE.wasm [--wit SRC --world W] [--adaptor [--alloc NAME]] [--lime] -o OUT.wasm
                       the component of a core module: by default a thin wrapper (the module
                       follows the canonical ABI); with --adaptor, the module follows the C
                       convention (alloc(size, align), out-pointers) and the verified adaptor
                       `Jco.adaptorLime` is placed next to it. The world comes from the
                       module's component-type section, or from WIT text (a .wit file, or a
                       directory with one .wit file). With --lime the module goes through the
                       verified 3.0 -> Lime compiler first and every output core module must
                       be in Lime1
wasm-jco new CORE.wasm --adapt NAME=ADAPTER.wasm [--adapt …] [--realloc-via-memory-grow]
                       [--wit SRC --world W] -o OUT.wasm
                       wit-component's `--adapt`: the module imports functions from the core
                       module NAME (e.g. wasi_snapshot_preview1), implemented by the adapter
                       (e.g. the official WASI preview 1 adapter); the adapter is reduced to what
                       is needed (`AdaptGC.run`) and placed next to the module (`Adapt.emit`);
                       the output is refused unless the reference validator accepts it
wasm-jco new CORE.wasm --ref [--wit SRC --world W] -o OUT.wasm
                       for a world of synchronous functions over bool, integers and char: the
                       component in the layout of the reference bridge `Simple.toRef` (no
                       imports) or `SimpleI.toRef` (the core module imports each world import
                       as "env" "name"), read back as that component (`RefSimple.newRef_correct`,
                       `RefSimpleI.newRefI_correct`), so the reference machine runs it as its IR
                       component (`newRef_sound`, `newRefI_sound`); parameter names are `a`, `ax`, …
wasm-jco component wit COMP.wasm [-o OUT.wit]
                       `wasm-tools component wit`: a WIT package's text, else the component's
                       world (`Project.projectX`) as the package `root:component` (`WitOf`)
wasm-jco embed WIT CORE.wasm [--world W] [--encoding utf8|utf16|compact-utf16] -o OUT.wasm
wasm-jco component embed …  `wasm-tools component embed`: the world's `component-type`
                       payload (`Source.embedText`) appended to the core module
wasm-jco component new …    the same as `new`
wasm-jco print COMP.wasm        component WAT (verified grammar only)
wasm-jco validate COMP.wasm     the verified parser, the IR reader and the reference validator
                       (`reference-valid: yes` when the bytes, read as a reference Core 3.0
                       component with core module types, pass `Reference.check?`:
                       `LayoutRefX.refCheckX_valid`)
wasm-jco kcore NAME KERNEL N [--baseline] [--canonical | --printer | -o OUT.wasm]
                       the core module generated from a byte kernel (map, filter, takeN,
                       lines, rechunkN) by the drop-aware generator `KDrop.genD`, reading up
                       to N bytes at a time (KDrop.Thms: `step_sim`, `kchain_correct` under
                       the Component Model's drop behaviour): the WAT of silmaril's proved
                       printer (`watOf_encodes`, for every program; `--canonical` is the
                       same), denoting `KCoreEmit.toModule (genD k N) NAME`
                       (`KDropEmit.kdrop_wat`); with --printer the text of `Prog.wat`, checked
                       per output (`watChecked_encodes`); with -o the bytes, by silmaril's
                       verified encoder (`KDropEmit.kdrop_bytes`). --baseline uses round 1's
                       `KCore.gen` instead (correct over the `Async` model; traps in some
                       chains under wasmtime: docs/projects/wasm-components.md)
```

`new` prints the plan, whether the output is in the verified grammar (`ast: yes`) and
whether it reads back as the thin wrapper of the input module (`ir: yes`; see
`Silmaril.Wasm.JcoTool.Tool.Thms`). Exit status: 0 on success, 1 on failure, 2 on a usage error.

The command line is read by the grammar `Silmaril.Cli.Spec.Jco.tool` through
`Silmaril.Cli.Clap.Tool.main`: options may come in any order and before or after the positionals,
`--` ends the options, `-h` prints the derived help of a command, and a usage error (an unknown
option, a missing `-o`, `--wit` without `--world`, …) prints `error: …` with the derived usage
line and exits 2; the program refines `Jco.tool.spec` (`Silmaril.Cli.Clap.Tool.main_refines`;
docs/projects/wasm-binaryen-tooling.md).
-/

open Silmaril.Wasm.JcoTool.Tool

def fail (msg : String) : IO UInt32 := do
  IO.eprintln s!"wasm-jco: {msg}"
  pure 1

def witFiles (dir : String) : IO (Array String) := do
  let es ← System.FilePath.readDir dir
  pure ((es.filter fun e => e.fileName.endsWith ".wit").map (·.path.toString))

/-- The main WIT document and its dependencies (`deps/*.wit` next to it). -/
def readWit (src : String) : IO ((String × String) × List (String × String)) := do
  let isDir ← System.FilePath.isDir src
  let main ← if isDir then
      match (← witFiles src).toList with
      | [f] => pure f
      | _ => throw (IO.userError s!"{src}: expected exactly one .wit file")
    else pure src
  let depDir := (System.FilePath.mk main).parent.getD "." / "deps"
  let deps : List (String × String) ← if ← depDir.isDir then
      (← witFiles depDir.toString).toList.mapM fun (f : String) => do pure (f, ← IO.FS.readFile f)
    else pure []
  pure ((main, ← IO.FS.readFile main), deps)

def yesNo (b : Bool) : String := if b then "yes" else "no"

/-- `wasm-jco component wit COMP.wasm [-o OUT]`. -/
def witCmd (f : String) (m : Silmaril.Cli.Matches) : IO UInt32 := do
  match Silmaril.Wasm.JcoTool.WitOf.componentWit (← IO.FS.readBinFile f) with
  | .ok t =>
    match m.str? "-o" with
    | some o => IO.FS.writeFile o t
    | none => IO.print t
    pure 0
  | .error e => fail e

/-- The `.wit` files of a directory (not subdirectories), sorted, with their text. -/
def witTexts (dir : String) : IO (List (String × String)) := do
  let es ← System.FilePath.readDir dir
  let fs ← es.filterM fun e => do pure (e.fileName.endsWith ".wit" && !(← e.path.isDir))
  let fs := (fs.map fun (e : IO.FS.DirEntry) => e.path.toString).qsort (fun (a b : String) => a < b)
  fs.toList.mapM fun (f : String) => do pure (f, ← IO.FS.readFile f)

/-- A WIT source as `wit-parser` reads a path: a file, or a directory of several files (one
package), with `deps/` (one package per `.wit` file and per subdirectory). -/
def readWitPkg (src : String) : IO (List (String × String) × List (List (String × String))) := do
  let isDir ← System.FilePath.isDir src
  let main ← if isDir then witTexts src else pure [(src, ← IO.FS.readFile src)]
  let depDir := if isDir then System.FilePath.mk src / "deps"
    else (System.FilePath.mk src).parent.getD "." / "deps"
  let deps ← if ← depDir.isDir then do
      let files ← witTexts depDir.toString
      let es ← System.FilePath.readDir depDir
      let subs ← es.filterM fun e => e.path.isDir
      let subs := (subs.map (·.path.toString)).qsort (fun (a b : String) => a < b)
      let mut ds := files.map ([·])
      for d in subs do ds := ds ++ [← witTexts d]
      pure ds
    else pure []
  pure (main, deps)

/-- The world of a package when `--world` is absent: its only world. -/
def onlyWorld (b : ByteArray) : Except String String := do
  let d ← Silmaril.Wasm.Wit.Tool.decode b
  match d.pkg.worlds with
  | [(n, _)] => pure n
  | [] => throw "the WIT package has no world"
  | _ => throw "the WIT package has several worlds: pass --world"

/-- `wasm-jco embed WIT CORE.wasm [--world W] [--encoding E] -o OUT`. -/
def embedCmd (src core : String) (m : Silmaril.Cli.Matches) : IO UInt32 := do
  let some out := m.str? "-o" | fail "-o is required"
  let se ← match m.str? "encoding" with
    | none | some "utf8" => pure Silmaril.Wasm.Wit.Binary.StringEncoding.utf8
    | some "utf16" => pure .utf16
    | some "compact-utf16" | some "latin1+utf16" => pure .compactUtf16
    | some e => do IO.eprintln s!"wasm-jco: unknown encoding {e}"; return 2
  let (mw, ds) ← readWitPkg src
  let m0 ← IO.FS.readBinFile core
  match (do
      -- the package's bytes (`WitDir.encodeTextX`: `encodeText` on one-file packages), then
      -- the world's payload from them (`Source.embedBytes`)
      let pb ← Silmaril.Wasm.Wac.WitDir.encodeTextX mw ds
      let w ← match m.str? "world" with
        | some w => pure w
        | none => onlyWorld pb
      let pl ← Silmaril.Wasm.Wit.Tool.embedBytes pb w se
      Silmaril.Wasm.Wit.Binary.embedPayload m0 pl : Except String _) with
  | .ok b => IO.FS.writeBinFile out b; pure 0
  | .error e => fail e

def newCmd (core : String) (m : Silmaril.Cli.Matches) : IO UInt32 := do
  let some out := m.str? "-o" | fail "-o is required"
  -- a module in the `cm32p2` naming scheme is renamed to the legacy one first (`Cm32.normalize`;
  -- other modules are unchanged)
  let bytes ← match Silmaril.Wasm.JcoTool.Cm32.prepare (← IO.FS.readBinFile core) with
    | .ok b => pure b
    | .error e => return (← fail e)
  let wit ← match m.str? "wit", m.str? "world" with
    | some src, some w => do
      let (m, ds) ← readWit src
      pure (.ok (some (m, ds, w)))
    | none, none => pure (.ok none)
    | _, _ => pure (.error "--wit and --world go together")
  -- --adapt NAME=FILE (repeatable)
  let adSpecs := m.strs "adapt"
  if !adSpecs.isEmpty then
    let mut ads : List (String × ByteArray) := []
    for sp in adSpecs do
      match sp.splitOn "=" with
      | [n, f] => ads := ads ++ [(n, ← IO.FS.readBinFile f)]
      | [f] =>
        -- the name from the file name, as wit-component does (`wasi_snapshot_preview1.command.wasm`)
        let base := ((System.FilePath.mk f).fileName.getD f).splitOn "." |>.head!
        ads := ads ++ [(base, ← IO.FS.readBinFile f)]
      | _ => return (← fail s!"--adapt {sp}: expected NAME=FILE")
    match (do
        let w ← (wit : Except String _)
        Silmaril.Wasm.JcoTool.AdaptLayout.newAdaptL bytes w ads (m.flag "realloc-via-memory-grow") : Except String _) with
    | .error e => return (← fail e)
    | .ok (b, ls) =>
      IO.FS.writeBinFile out b
      for l in ls do IO.println l
      IO.println s!"bytes: {b.size}"
      return 0
  if m.flag "ref" then
    match (do
        -- the `--ref` layouts import world functions from "env": the world is taken as written
        let wf ← (wit >>= Silmaril.Wasm.JcoTool.ToolI.worldFullOf bytes : Except String _)
        if wf.world.imports.isEmpty then
          let (b, s) ← Silmaril.Wasm.JcoTool.RefSimple.newRef bytes wf.world
          pure (b, Silmaril.Wasm.JcoTool.RefSimple.summary s)
        else
          let (b, s) ← Silmaril.Wasm.JcoTool.RefSimpleI.newRefI bytes wf.world
          pure (b, Silmaril.Wasm.JcoTool.RefSimpleI.summary s) : Except String _) with
    | .error e => return (← fail e)
    | .ok (b, ls) =>
      IO.FS.writeBinFile out b
      for l in ls do IO.println l
      IO.println s!"bytes: {b.size}"
      IO.println (Silmaril.Wasm.JcoTool.ToolV.refCheckXLine b)
      return 0
  let r := fun (_ : Unit) => do
    let wf ← (wit >>= Silmaril.Wasm.JcoTool.Front.worldFullOf bytes : Except String _)
    let w := wf.world
    let _ := w
    let alloc := (m.str? "alloc").getD "alloc"
    if m.flag "adaptor" then
      if (Silmaril.Wasm.JcoTool.NewI.ifaces wf).any (!·.imported) then
        if m.flag "lime" then throw "--lime with --adaptor and interfaces is not supported"
        else Silmaril.Wasm.JcoTool.AdaptorI.toToolOut <$> Silmaril.Wasm.JcoTool.AdaptorI.newAdaptorI bytes wf alloc
      else if m.flag "lime" then Silmaril.Wasm.JcoTool.Lime.newLime bytes w (some alloc)
      else newAdaptor bytes w alloc
    else Silmaril.Wasm.JcoTool.ToolV.newLimeFullV bytes wf
  -- the default mode: `Front.worldFullOf`, `Front.newValid` and `StreamSem.report` with each core
  -- module decoded once and validated once (`Perf.JcoMain.newDefault_eq`); then the
  -- component-level custom sections (`Adapt.withMeta_bytes`: the certified bytes, then the
  -- sections). Modules exporting `__wasm_task_hook` or `_initialize` go to the general layout.
  let dflt := !m.flag "adaptor" && !m.flag "lime"
  let rd : Except String (Silmaril.Wasm.JcoTool.Tool.Out × List String) :=
    if !dflt then .error ""
    -- = `if needsGeneral bytes then none else newDefault bytes wit`, one decode (`NewMain.newMain_eq`)
    else match (wit >>= Silmaril.Wasm.JcoTool.NewMain.newMain bytes : Except String _) with
      | .error e => .error e
      | .ok none => .error "the module exports __wasm_task_hook or _initialize"
      | .ok (some (o, rep)) =>
        .ok (Silmaril.Wasm.JcoTool.Adapt.withMeta o (Silmaril.Wasm.JcoTool.Adapt.certifiedNames o.cores.length), rep)
  -- outside the fragment of the certified layout (a memory import, `cabi_import_realloc` /
  -- `cabi_export_realloc`, …): the general layout of `Adapt.emit` with no adapter, its output
  -- checked by the reference validator (no layout certificate)
  let r : Except String Silmaril.Wasm.JcoTool.Tool.Out :=
    match (if dflt then Prod.fst <$> rd else r ()) with
    | .error e =>
      if !dflt then .error e
      else match (do
          let w ← (wit : Except String _)
          Silmaril.Wasm.JcoTool.AdaptLayout.newAdaptL bytes w [] : Except String _) with
        | .ok (b, ls) =>
          let o : Silmaril.Wasm.JcoTool.Tool.Out := ⟨b, none, false,
            ls ++ [s!"general layout (Adapt.emit): the certified layout refused the module ({((e.splitOn "\n").headD "").take 160})"], []⟩
          .ok o
        | .error e2 => .error (if e2 == e then e else s!"{e} (general layout: {e2})")
    | ok => ok
  match r with
  | .error e => fail e
  | .ok o =>
    IO.FS.writeBinFile out o.bytes
    for l in o.summary do IO.println l
    IO.println s!"bytes: {o.bytes.size}"
    IO.println s!"ast:   {yesNo o.ast.isSome} (in the verified component grammar)"
    IO.println s!"ir:    {yesNo o.ir} (reads back as the thin wrapper of the input)"
    if let .ok (_, rep) := rd then for l in rep do IO.println l
    else if !m.flag "adaptor" then
      match (wit >>= Silmaril.Wasm.JcoTool.Front.worldFullOf bytes : Except String _) with
      | .ok wf => for l in Silmaril.Wasm.JcoTool.StreamSem.report bytes wf.world do IO.println l
      | .error _ => pure ()
    pure 0

/-- `kcore NAME KERNEL N [--baseline] [--canonical | --printer | -o OUT.wasm]`. -/
def kcoreCmd (m : Silmaril.Cli.Matches) : IO UInt32 := do
  let str (k : String) : String := (m.str? k).getD ""
  let (name, k, n) := (str "name", str "kernel", str "n")
  match Silmaril.Wasm.JcoTool.KFitBuf.toolKernel k, n.toNat? with
  | some km, some b =>
    if 1 ≤ b ∧ b ≤ 256 then
      let P := Silmaril.Wasm.JcoTool.KDropEmit.toolGen (m.flag "baseline") km b
      -- `--canonical`, `--printer` and `-o` exclude each other (the grammar's rules)
      match m.str? "-o" with
      | some out => match Silmaril.Wasm.JcoTool.KCoreEmit.wasmOf P name with
        | .ok bs => IO.FS.writeBinFile out bs; pure 0
        | .error e => fail e
      | none =>
        if m.flag "printer" then
          match Silmaril.Wasm.JcoTool.KCoreEmit.watChecked P name with
          | .ok t => IO.print t; pure 0
          | .error e => fail e
        else match Silmaril.Wasm.JcoTool.KCoreEmit.watOf P name with
          | .ok t => IO.println t; pure 0
          | .error e => fail e
    else fail "kcore: N must be in 1..256"
  | _, _ => fail s!"kcore: unknown kernel {k} or bad N {n}"

/-- The commands, on the matches of `Silmaril.Cli.Spec.Jco.tool`. -/
def run (m : Silmaril.Cli.Matches) : IO UInt32 := do
  let str (k : String) : String := (m.str? k).getD ""
  match m.path with
  | ["new"] | ["component", "new"] => newCmd (str "core") m
  | ["component", "wit"] => witCmd (str "comp") m
  | ["embed"] | ["component", "embed"] => embedCmd (str "wit") (str "core") m
  | ["print"] =>
    match Silmaril.Wasm.Perf.WatPrint.printWatF (← IO.FS.readBinFile (str "comp")) with  -- = printWat
    | .ok t => IO.print t; pure 0
    | .error e => fail e
  | ["validate"] =>
    let b ← IO.FS.readBinFile (str "comp")
    -- = `validate b ++ [ToolV.refCheckXLine b]`, each core module decoded once
    -- (`Perf.JcoMain.validateLines_eq`)
    for l in Silmaril.Wasm.Perf.JcoMain.validateLines b do IO.println l
    pure 0
  | ["kcore"] => kcoreCmd m
  | p => fail s!"no command {p}"

def main : List String → IO UInt32 := Silmaril.Cli.Spec.Jco.tool.main run
