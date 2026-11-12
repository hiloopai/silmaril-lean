import Silmaril.Wasm.Tools.Wast.Check.Defs
import Silmaril.Wasm.Tools.Wast.Backend.Defs
import Silmaril.Wasm.Tools.Wast.Cli.Defs
import WasmTools.WastHelp
import WasmTools.Types

/-!
# `wasm-tools json-from-wast` and `wasm-tools wast`: the IO wrappers

Thin wrappers over the pure cores: `Silmaril.Wasm.Tools.Wast.Cli.jsonOpts?`/`wastOpts?`
(arguments), `Silmaril.Wasm.Tools.Wast.read` (lexing, checked against the WAT lexical
grammar), `Script.ofSExps?` (the script grammar), `scriptJson` (the JSON form) and
`checkScript` (the structural check). They read the input, write the auxiliary files and
the output, and map errors to `wasm-tools`'s exit statuses: 0 success, 1 failure (`error: …`
on stderr), 2 usage error (clap's message on stderr).

`subcommands` is the table the main `wasm-tools` dispatcher (`tools/wasm-tools/WasmTools.lean`)
imports.
-/

open Silmaril.Wasm.Tools.Wast
open Silmaril.Wasm.Tools.Wast.Cli

namespace WasmTools.Wast

def usageError (usage : String) (e : ArgError) : IO UInt32 := do
  let tip := match e with
    | .unknown a => if a.startsWith "-" then s!"\n  tip: to pass '{a}' as a value, use '-- {a}'\n" else ""
    | _ => ""
  IO.eprint s!"error: {e.message}\n{tip}\nUsage: {usage}\n\nFor more information, try '--help'.\n"
  return 2

def fail (msg : String) : IO UInt32 := do
  IO.eprint s!"error: {msg}\n"
  return 1

/-- Read and parse a script: positioned trees and the syntax tree. -/
def readScript (path text : String) : Except String (Script × List PNode) := do
  let ps ← match read text with
    | .ok (ps, _) => pure ps
    | .error e =>
      let lines := lineStarts text.toUTF8
      let l := lineOf lines e.pos
      let col := e.pos - lines[l - 1]! + 1
      throw s!"{e.msg}\n     --> {path}:{l}:{col}"
  match Script.ofSExps? (ps.map PNode.erase) with
  | some s => pure (s, ps)
  | none => throw s!"failed to parse the script {path}: not a .wast directive list"

def joinPath (dir name : String) : String :=
  if dir.endsWith "/" then dir ++ name else dir ++ "/" ++ name

/-- `wasm-tools json-from-wast`. -/
def jsonFromWast (args : List String) : IO UInt32 := do
  match jsonOpts? args with
  | .help long =>
    IO.print (if long then WastHelp.jsonLong else WastHelp.jsonShort)
    return 0
  | .error e => usageError "wasm-tools json-from-wast [OPTIONS] <WAST>" e
  | .run o =>
    let text ← match ← (IO.FS.readFile o.wast).toBaseIO with
      | .ok t => pure t
      | .error e => return ← fail s!"failed to read input wast file: {repr o.wast}\n\nCaused by:\n    0: {e}"
    let (script, ps) ← match readScript o.wast text with
      | .ok r => pure r
      | .error e => return ← fail e
    let stem := match o.output with
      | some out => fileStem out
      | none => fileStem o.wast
    let c : LowerCtx := { stem, source := text.toUTF8, lines := lineStarts text.toUTF8, enc := parseEncoder }
    let (json, files) ← match scriptJson c o.wast script ps with
      | .ok r => pure r
      | .error e => return ← fail e
    for (name, bytes) in files do
      let dst := match o.wasmDir with | some d => joinPath d name | none => name
      match ← (IO.FS.writeBinFile dst bytes).toBaseIO with
      | .ok () => pure ()
      | .error e => return ← fail s!"failed to write {repr dst}\n\nCaused by:\n    0: {e}"
    let out := if o.pretty then json.prettyFast else json.compactFast
    match o.output with
    | some path =>
      match ← (IO.FS.writeFile path out).toBaseIO with
      | .ok () => pure ()
      | .error e => return ← fail s!"failed to write `{path}`\n\nCaused by:\n    0: {e}"
    | none =>
      let h ← IO.getStdout
      h.putStr out
      h.flush
    return 0

/-- The parent directory of a path (`""` for none). -/
def parentDir (path : String) : String :=
  match (path.splitOn "/").dropLast with
  | [] => ""
  | ps => "/".intercalate ps

/-- `Opts::snapshot`: compare `contents` with the snapshot file (`BLESS`: write it). -/
def snapIO (dir : Option String) (bless : Bool) : Snap IO := fun kind test contents => do
  let some d := dir
    | return .error "must pass `--snapshot <dir>` to indicate where to place snapshots"
  let path := snapshotName d kind test
  let contents := contents.replace "\r\n" "\n"
  if bless then
    match ← (do
        let p := parentDir path
        if p != "" then IO.FS.createDirAll p
        IO.FS.writeFile path contents : IO Unit).toBaseIO with
    | .ok () => return .ok ()
    | .error e => return .error s!"could not write out the snapshot to {repr path}: {e}"
  match ← (IO.FS.readBinFile path).toBaseIO with
  | .error e => return .error s!"could not read the snapshot, try `env BLESS=1`: {e}"
  | .ok bytes =>
    match String.fromUTF8? bytes with
    | none => return .error "can't decode snapshot as utf-8"
    | some snap =>
      if snap.replace "\r\n" "\n" == contents then return .ok ()
      else
        let a := snap.splitOn "\n"
        let b := contents.splitOn "\n"
        let i := ((List.range (min a.length b.length)).find? fun i => a[i]! != b[i]!).getD
          (min a.length b.length)
        return .error s!"snapshot does not match the expected result, try `env BLESS=1`\nfirst difference at line {i + 1}:\n- {a.getD i ""}\n+ {b.getD i ""}"

/-- `test_json_from_wast`: the `--pretty` JSON of the script, compared with its `json`
snapshot (the auxiliary files are not written). -/
def jsonSnapshot (snap : Snap IO) (path text : String) : IO (Except String Unit) := do
  match readScript path text with
  | .error e => return .error s!"failed to run `json-from-wast`: {e}"
  | .ok (script, ps) =>
    let c : LowerCtx := { stem := fileStem path, source := text.toUTF8,
                          lines := lineStarts text.toUTF8, enc := parseEncoder }
    match scriptJson c path script ps with
    | .error e => return .error s!"failed to run `json-from-wast`: {e}"
    | .ok (json, _) =>
      match ← snap "json" (path.replace "\\" "/") json.prettyFast with
      | .ok () => return .ok ()
      | .error e => return .error s!"failed to validate the `json-from-wast` snapshot\n{e}"

/-- `wasm-tools wast`. -/
def wast (args : List String) : IO UInt32 := do
  match wastOpts? args with
  | .help long =>
    IO.print (if long then WastHelp.wastLong else WastHelp.wastShort)
    return 0
  | .error e => usageError "wasm-tools wast [OPTIONS] [INPUT]" e
  | .run o =>
    let (path, text) ← match o.input with
      | some p =>
        if p == "-" then pure ("<stdin>", ← (← IO.getStdin).readToEnd)
        else match ← (IO.FS.readFile p).toBaseIO with
          | .ok t => pure (p, t)
          | .error e => return ← fail s!"failed to read {repr p}\n\nCaused by:\n    0: {e}"
      | none => pure ("<stdin>", ← (← IO.getStdin).readToEnd)
    let (script, ps) ← match readScript path text with
      | .ok r => pure r
      | .error e => return ← fail e
    let opts : CheckOpts :=
      { ignoreErrorMessages := o.ignoreErrorMessages,
        asserts := o.asserts.filterMap Assert.ofString? }
    let bless := (← IO.getEnv "BLESS").isSome
    let snap := snapIO o.snapshot bless
    if let some p := o.input then
      if p != "-" && opts.on .snapshotJson then
        match ← jsonSnapshot snap p text with
        | .ok () => pure ()
        | .error e =>
          return ← fail (renderChain "failed to run `json-from-wast` cli subcommand" [e])
    let lines := lineStarts text.toUTF8
    let backend := fullBackend o.featureSet
    match ← checkScript backend opts snap path text.toUTF8 script ps with
    | [] => return 0
    | errs =>
      let mut s := s!"{errs.length} test failures in {path}:"
      for (pos, e) in errs do
        let l := lineOf lines pos
        let col := pos - lines[l - 1]! + 1
        s := s ++ "\n\n--------------------------------\n\n" ++
          renderChain s!"failed directive on {path}:{l}:{col}" e
      fail s

/-- The subcommands of this module, for the `wasm-tools` dispatcher. -/
def subcommands : List (String × (List String → IO UInt32)) :=
  [("json-from-wast", jsonFromWast), ("wast", wast)]

/-- The group table of the main dispatch (`WasmTools.lean`). -/
def table : List Subcommand :=
  subcommands.map fun (name, run) => { name, run }

end WasmTools.Wast
