import Silmaril.Wasm.Tools.Gen.Cmd.Args.Defs
import WasmTools.SpecArgs
import Silmaril.Wasm.Tools.Gen.Cmd.Print.Defs
import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# Shared IO of the gentool subcommands (`smith`, `mutate`, `shrink`)

The thin layer between the process and the pure cores: the arguments the specification read
(`ofMatches`; help and clap's usage errors are the specification's, `WasmTools.specMain`), reading `[INPUT]` (a path, or stdin for none or `-`), writing `-o` or
stdout, and `error: …` failures (status 1) in upstream's wording (`anyhow`'s
`Caused by:` chain).
-/

namespace WasmTools.GenCommon

open Silmaril.Wasm.Tools.Gen.Cmd

/-- A failure: the message after `error: `, exit status 1. -/
def fail (msg : String) : IO UInt32 := do
  (← IO.getStderr).putStr s!"error: {msg}\n"
  return 1

/-- The OS error of an IO error, as Rust prints it. -/
def osCause : IO.Error → String
  | .noFileOrDirectory .. => "No such file or directory (os error 2)"
  | .permissionDenied .. => "Permission denied (os error 13)"
  | .alreadyExists .. => "File exists (os error 17)"
  | .otherError 21 _ => "Is a directory (os error 21)"
  | .inappropriateType _ 21 _ => "Is a directory (os error 21)"
  | .inappropriateType .. => "Is a directory (os error 21)"
  | e => toString e

/-- `anyhow`'s one-cause chain. -/
def caused (head cause : String) : String := s!"{head}\n\nCaused by:\n    0: {cause}"

/-- Read a path or stdin (`none` or `-`). `quote` renders the path in the head message. -/
def readInput (path : Option String) (head : String → String) :
    IO (Except String ByteArray) := do
  match path with
  | none | some "-" => return .ok (← (← IO.getStdin).readBinToEnd)
  | some p =>
    match ← (IO.FS.readBinFile p).toBaseIO with
    | .ok b => return .ok b
    | .error e => return .error (caused (head p) (osCause e))

/-- Write bytes to `-o PATH`, or stdout (refused when it is a terminal). -/
def writeBytes (out : Option String) (b : ByteArray) : IO (Except String Unit) := do
  match out with
  | some p =>
    match ← (IO.FS.writeBinFile p b).toBaseIO with
    | .ok () => return .ok ()
    | .error e => return .error (caused s!"failed to write `{p}`" (osCause e))
  | none =>
    let o ← IO.getStdout
    if ← o.isTty then
      return .error
        "cannot print binary wasm output to a terminal, pass the `-t` flag to print the text format"
    o.write b; o.flush
    return .ok ()

/-- Write text to `-o PATH`, or stdout. -/
def writeText (out : Option String) (s : String) : IO (Except String Unit) :=
  writeBytes' out s.toUTF8
where
  writeBytes' (out : Option String) (b : ByteArray) : IO (Except String Unit) := do
    match out with
    | some p =>
      match ← (IO.FS.writeBinFile p b).toBaseIO with
      | .ok () => return .ok ()
      | .error e => return .error (caused s!"failed to write `{p}`" (osCause e))
    | none => let o ← IO.getStdout; o.write b; o.flush; return .ok ()

/-- **The parsed arguments of a gen subcommand**, from the specification's matches: its options
by kind (`Args.Parsed.ofOccs` over `SpecArgs.occs`) and its positionals. -/
def ofMatches (sp : Args.Spec) (m : Silmaril.Cli.Matches) : Except String Args.Parsed :=
  Args.Parsed.ofOccs sp (WasmTools.SpecArgs.occs m) (WasmTools.SpecArgs.positionals m)

/-- Run a body on the specification's matches (a value `ofMatches` refuses, which the
specification has checked already, is clap's message, status 2). -/
def runMatches (sp : Args.Spec) (body : Args.Parsed → IO UInt32) (m : Silmaril.Cli.Matches) :
    IO UInt32 := do
  match ofMatches sp m with
  | .ok p => body p
  | .error e => (← IO.getStderr).putStr e; return 2

/-- Does the input start with the binary magic? -/
def isBinary (b : ByteArray) : Bool :=
  b.size ≥ 4 && b[0]! == 0 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6D

/-- Encode a module, following the input's data-count section (`encodeModule`). -/
def encode (hint : ByteArray) (m : Silmaril.Wasm.Module) : Except String ByteArray :=
  Silmaril.Wasm.Binaryen.Exe.encodeModule hint m

/-- The text of a module, or why not. -/
def printText (m : Silmaril.Wasm.Module) : Except String String :=
  match Print.printModule? m with
  | some s => .ok s
  | none => .error ("the text form of this module is outside the printer of this wasm-tools " ++
      "(see docs/projects/wasm-components.md, Known limitations)")

end WasmTools.GenCommon
