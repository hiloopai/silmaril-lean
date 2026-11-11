import Silmaril.Wasm.Tools.OptGrammar.Defs
import Silmaril.Wasm.Tools.Text.Defs

/-!
# Shared IO of the validate track's subcommands

The thin IO wrapper around the pure cores: reading `[INPUT]` (a path, or stdin for none or `-`,
as `wasm_tools::InputArg`), writing `-o`, `--output` (as `wasm_tools::OutputArg`), printing errors
as `main.rs`'s `print_error` (`error: …` on stderr, exit status 1) and command-line errors as
clap (exit status 2), and `-h`/`--help`.
-/

namespace WasmTools.VCommon

open Silmaril.Wasm.Tools.OptGrammar

/-- A failed run: the message for `error: …`, exit status 1. -/
def fail (msg : String) : IO UInt32 := do
  IO.eprintln s!"error: {msg}"
  return 1

/-- A command-line error: clap's message and usage, exit status 2. -/
def usageError (usage line : String) : IO UInt32 := do
  IO.eprintln line
  IO.eprintln ""
  IO.eprintln s!"Usage: {usage}"
  IO.eprintln ""
  IO.eprintln "For more information, try '--help'."
  return 2

/-- Parse the arguments; on `-h`/`--help` print the help and stop (status 0); on an error print
it (status 2). Also checks `--color`. -/
def parseOrExit (specs : List Spec) (maxPos : Nat) (usage shortHelp longHelp : String)
    (args : List String) : IO (Except UInt32 Parsed) := do
  match parse specs maxPos args with
  | .error e => return .error (← usageError usage e.render)
  | .ok p =>
    if let some long := p.help then
      IO.print (if long then longHelp else shortHelp)
      return .error 0
    if let some c := p.value? "color" then
      unless colorChoices.contains c do
        IO.eprintln s!"error: invalid value '{c}' for '--color <COLOR>': unrecognized color \
          choice '{c}': valid choices are: always, always-ansi, never, auto"
        IO.eprintln ""
        IO.eprintln "For more information, try '--help'."
        return .error 2
    return .ok p

/-- The `\0asm` magic number. -/
def isBinary (b : ByteArray) : Bool :=
  b.size ≥ 4 && b[0]! == 0 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6D

/-- The binary of the bytes of an input: a binary as it is; a text (non-binary) input is
assembled by the cli track's WAT parser (`Silmaril.Wasm.Tools.Text.textToBinary`, core modules in
silmaril's certified text fragment), as upstream's `InputArg::parse_wasm` does with `wat`. -/
def toBinary (b : ByteArray) : Except String ByteArray :=
  if isBinary b then .ok b
  else
    match String.fromUTF8? b with
    | none => .error "input bytes aren't valid utf-8"
    | some s =>
      -- `wat::parse_bytes` of an empty text: no module fields
      if s.trimAscii.isEmpty then .error "expected at least one module field" else
      match Silmaril.Wasm.Tools.Text.textToBinary s with
      | .ok bin => .ok bin
      | .error e => .error s!"failed to parse the text format: {e}"

/-- Read `[INPUT]`: the file, or all of stdin for none or `-`, then `toBinary`. -/
def readInput (input : Option String) : IO (Except String ByteArray) := do
  let bytes ← match input with
    | some path =>
      if path != "-" then
        match (← (IO.FS.readBinFile path).toBaseIO) with
        | .ok b => pure (.ok b)
        | .error _ => pure (.error s!"failed to read from `{path}`")
      else readStdin
    | none => readStdin
  return bytes >>= toBinary
where
  readStdin : IO (Except String ByteArray) := do
    let stdin ← IO.getStdin
    let mut acc := ByteArray.empty
    repeat
      let chunk ← stdin.read (1024 * 1024)
      if chunk.isEmpty then break
      acc := acc ++ chunk
    return .ok acc

/-- Write binary output: to `-o PATH`, or to stdout unless it is a terminal. -/
def writeBinary (output : Option String) (bytes : ByteArray) : IO (Except String Unit) := do
  match output with
  | some path =>
    match (← (IO.FS.writeBinFile path bytes).toBaseIO) with
    | .ok () => return .ok ()
    | .error _ => return .error s!"failed to write `{path}`"
  | none =>
    let out ← IO.getStdout
    if ← out.isTty then
      return .error "cannot print binary wasm output to a terminal, pass the `-t` flag to print \
        the text format"
    out.write bytes
    out.flush
    return .ok ()

/-- Write text output: to `-o PATH` or stdout. -/
def writeText (output : Option String) (text : String) : IO (Except String Unit) := do
  match output with
  | some path =>
    match (← (IO.FS.writeFile path text).toBaseIO) with
    | .ok () => return .ok ()
    | .error _ => return .error s!"failed to write `{path}`"
  | none =>
    let out ← IO.getStdout
    out.putStr text
    out.flush
    return .ok ()

end WasmTools.VCommon
