import Silmaril.Wasm.Tools.Component.Text.Defs
import Silmaril.Wasm.Tools.Component.Cmd.Defs
import WasmTools.Component.Opts

/-!
# The IO layer of the `component` subcommands

Thin, reviewed wrappers: take the record of the arguments the specification read
(`WasmTools.Component.Opts`: `NewArgs.ofMatches`, …), read the inputs as upstream does, call one pure core
(`Silmaril.Wasm.Tools.Component.Cmd`, `.Unbundle`), write the result. Conventions of upstream
1.262.0 (`src/lib.rs`):

* help and clap's usage errors are the specification's (`WasmTools.specMain`);
* a usage error found by a body (a value the specification leaves to it) prints clap's message
  on stderr, exit 2;
* any other failure prints `error: MESSAGE` on stderr, exit 1;
* an absent input or `-` reads stdin; Wasm inputs may be binary or text (`wat::parse_bytes`);
* binary output goes to `-o PATH`, else to stdout unless stdout is a terminal; `-t` prints text.
-/

namespace WasmTools.Component

open Silmaril.Wasm.Tools.Component

/-- A failure: a usage error (exit 2, message printed as is) or an error (exit 1). -/
inductive Fail where
  | usage (msg : String)
  | error (msg : String)

abbrev M := ExceptT Fail IO

def liftE {α : Type} : Except String α → M α
  | .ok a => pure a
  | .error e => throw (.error e)

def fail {α : Type} (msg : String) : M α := throw (.error msg)

/-- Run a subcommand body: a body's usage error exit 2, other errors `error: …` exit 1. -/
def runM (body : M Unit) : IO UInt32 := do
  match ← body.run with
  | .ok () => return 0
  | .error (.usage m) => (← IO.getStderr).putStr m; return 2
  | .error (.error m) => (← IO.getStderr).putStr s!"error: {m}\n"; return 1

def osCause : IO.Error → String
  | .noFileOrDirectory .. => "No such file or directory (os error 2)"
  | .permissionDenied .. => "Permission denied (os error 13)"
  | .alreadyExists .. => "File exists (os error 17)"
  | e => toString e

/-- The raw bytes of the input (stdin when absent or `-`). -/
def readRaw (input : Option String) : M ByteArray := do
  match input with
  | none | some "-" => (← IO.getStdin).readBinToEnd
  | some path =>
    match ← (IO.FS.readBinFile path).toBaseIO with
    | .ok b => pure b
    | .error e => fail s!"failed to read from `{path}`\n\nCaused by:\n    0: {osCause e}"

/-- `InputArg::get_binary_wasm`: the input as a binary (text inputs assembled). DWARF options
only matter for text inputs; there they are refused. -/
def readWasm (io : IoArgs) : M ByteArray := do
  let raw ← readRaw io.input
  if !Text.hasMagic raw && io.dwarf then
    fail "option `--generate-dwarf`/`-g` on a text input is not implemented by this wasm-tools"
  liftE (Text.toBinary raw)

/-- `OutputArg::output_wasm`: `-t` prints the text; else the bytes to `-o`, else stdout (refused
on a terminal). -/
def writeWasm (output : Option String) (b : ByteArray) (wat : Bool) : M Unit := do
  if wat then
    let t ← liftE (Text.printWat b)
    match output with
    | some path =>
      match ← (IO.FS.writeFile path t).toBaseIO with
      | .ok () => pure ()
      | .error _ => fail s!"failed to write `{path}`"
    | none => let out ← IO.getStdout; out.putStr t; out.flush
  else
    match output with
    | some path =>
      match ← (IO.FS.writeBinFile path b).toBaseIO with
      | .ok () => pure ()
      | .error _ => fail s!"failed to write `{path}`"
    | none =>
      let out ← IO.getStdout
      if ← out.isTty then
        fail "cannot print binary wasm output to a terminal, pass the `-t` flag to print the text format"
      out.write b; out.flush

/-- Text output: to `-o`, else stdout. -/
def writeText (output : Option String) (t : String) : M Unit := do
  match output with
  | some path =>
    match ← (IO.FS.writeFile path t).toBaseIO with
    | .ok () => pure ()
    | .error _ => fail s!"failed to write `{path}`"
  | none => let out ← IO.getStdout; out.putStr t; out.flush

/-- The `.wit` files of a directory (not subdirectories), sorted, with their text. -/
def witTexts (dir : System.FilePath) : IO (List (String × String)) := do
  let es ← dir.readDir
  let fs ← es.filterM fun e => do pure (e.fileName.endsWith ".wit" && !(← e.path.isDir))
  let fs := (fs.map fun (e : IO.FS.DirEntry) => e.path.toString).qsort (fun a b => a < b)
  fs.toList.mapM fun f => do pure (f.toString, ← IO.FS.readFile f)

/-- `Resolve::push_path`: a directory (its `.wit` files, `deps/` one package per `.wit` file and
per subdirectory), a WIT binary, or one `.wit` file. -/
def readWitSrc (path : String) : M Cmd.WitSrc := do
  let p := System.FilePath.mk path
  if ← p.isDir then
    let main ← witTexts p
    let depDir := p / "deps"
    let deps ← if ← depDir.isDir then do
        let files ← witTexts depDir
        let es ← depDir.readDir
        let subs ← es.filterM fun e => e.path.isDir
        let subs := (subs.map (·.path)).qsort (·.toString < ·.toString)
        let mut ds := files.map ([·])
        for d in subs do ds := ds ++ [← witTexts d]
        pure ds
      else pure []
    pure (.dir main deps)
  else
    match ← (IO.FS.readBinFile path).toBaseIO with
    | .error e => fail s!"failed to read path for WIT [{path}]: {osCause e}"
    | .ok b =>
      if Text.hasMagic b then pure (.binary b)
      else match String.fromUTF8? b with
        | some t =>
          -- a WIT package in the WebAssembly text format (`wat::Detect`)
          let t0 := t.trimAsciiStart.toString
          if t0.startsWith "(" || t0.startsWith ";;" then pure (.binary (← liftE (Text.toBinary b)))
          else pure (.file path t)
        | none => fail s!"input file `{path}` was not valid utf-8"

/-- Refuse an option this implementation does not have (rather than ignore it): the options by
name, whether each was given. -/
def refuse (asked : List (String × Bool)) : M Unit := do
  for (k, b) in asked do
    if b then
      fail s!"option `--{k}` is not implemented by this wasm-tools (see docs/projects/wasm-components.md)"

end WasmTools.Component
