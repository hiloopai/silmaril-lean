import WasmTools.Args
import Silmaril.Wasm.Tools.Cli.Defs

/-!
# Input and output conventions shared by the subcommands

Upstream's `InputArg`/`OutputArg` (`src/lib.rs` of wasm-tools 1.262.0): an absent input or
`-` reads stdin; `-o PATH` writes `PATH` (also when `PATH` is `-`); binary output to a
terminal is refused. Errors are printed as `error: MESSAGE` with exit status 1.
-/

namespace WasmTools.Io

/-- Read the input named by the first positional (stdin when absent or `-`). -/
def readInput (p : Args.Parsed) : ExceptT String IO ByteArray := do
  let b ← readRaw
  -- `wat::parse_bytes` of a text with no module fields (an empty input, for one)
  let magic := b.size ≥ 4 && b.extract 0 4 == ByteArray.mk #[0, 0x61, 0x73, 0x6d]
  if !magic && (String.fromUTF8? b).any (·.trimAscii.isEmpty) then
    throw "expected at least one module field"
  pure b
where
  readRaw : ExceptT String IO ByteArray := do
    match p.positionals.head? with
    | none | some "-" => (← IO.getStdin).readBinToEnd
    | some path =>
      match ← (IO.FS.readBinFile path).toBaseIO with
      | .ok b => pure b
      | .error e =>
        let cause := match e with
          | .noFileOrDirectory .. => "No such file or directory (os error 2)"
          | .permissionDenied .. => "Permission denied (os error 13)"
          | e => toString e
        throw s!"failed to read from `{path}`\n\nCaused by:\n    0: {cause}"

/-- Write binary output: to `-o PATH`, else stdout unless it is a terminal. -/
def writeBinary (p : Args.Parsed) (b : ByteArray) : ExceptT String IO Unit := do
  match p.value? "output" with
  | some path =>
    match ← (IO.FS.writeBinFile path b).toBaseIO with
    | .ok () => pure ()
    | .error _ => throw s!"failed to write `{path}`"
  | none =>
    let out ← IO.getStdout
    if ← out.isTty then
      throw "cannot print binary wasm output to a terminal, pass the `-t` flag to print the text format"
    out.write b; out.flush

/-- Write text output: to `-o PATH`, else stdout. -/
def writeText (p : Args.Parsed) (s : String) : ExceptT String IO Unit := do
  match p.value? "output" with
  | some path =>
    match ← (IO.FS.writeFile path s).toBaseIO with
    | .ok () => pure ()
    | .error _ => throw s!"failed to write `{path}`"
  | none => let out ← IO.getStdout; out.putStr s; out.flush

/-- A body error starting with `usageMark` is a usage error found while validating an option
value (clap's value parsers): its text is printed verbatim and the status is 2. -/
def usageMark : String := "\x00usage\x00"

/-- Run a subcommand body against its grammar: help and usage errors as clap does, other
errors as `error: …` with status 1. -/
def runSpec (spec : Args.CmdSpec) (body : Args.Parsed → ExceptT String IO Unit)
    (args : List String) : IO UInt32 := do
  match Args.parseArgs spec args with
  | .help t => (← IO.getStdout).putStr t; return 0
  | .usageError t => (← IO.getStderr).putStr t; return 2
  | .ok p =>
    match ← (body p).run with
    | .ok () => return 0
    | .error e =>
      match e.dropPrefix? usageMark with
      | some t => (← IO.getStderr).putStr t.toString; return 2
      | none => (← IO.getStderr).putStr s!"error: {e}\n"; return 1

/-- The parsed items of the specified grammar (`Silmaril.Wasm.Tools.Cli`) in the shape the
bodies read (`Args.Parsed`: occurrences newest first, positionals in order). -/
def ofItems (is : List Silmaril.Wasm.Tools.Cli.Item) : Args.Parsed where
  occ := (is.filterMap fun
    | .opt k v => some (k, v.getD "")
    | .pos .. => none).reverse
  positionals := is.filterMap fun
    | .pos _ v => some v
    | .opt .. => none

/-- Run a subcommand body against a grammar of `Silmaril.Wasm.Tools.Cli` (specified by
`Silmaril.Wasm.Tools.Cli.Thms`): help texts, clap's usage errors (status 2), other errors as
`error: …` with status 1. -/
def runCli (spec : Silmaril.Wasm.Tools.Cli.Spec) (shortHelp longHelp : String)
    (body : Args.Parsed → ExceptT String IO Unit) (args : List String) : IO UInt32 := do
  match Silmaril.Wasm.Tools.Cli.parse spec args with
  | .help long => (← IO.getStdout).putStr (if long then longHelp else shortHelp); return 0
  | .err e => (← IO.getStderr).putStr (e.render spec); return 2
  | .ok is =>
    match ← (body (ofItems is)).run with
    | .ok () => return 0
    | .error e =>
      match e.dropPrefix? usageMark with
      | some t => (← IO.getStderr).putStr t.toString; return 2
      | none => (← IO.getStderr).putStr s!"error: {e}\n"; return 1

end WasmTools.Io
