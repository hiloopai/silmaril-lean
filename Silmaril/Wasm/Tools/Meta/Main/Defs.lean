module

public import Silmaril.Wasm.Tools.Meta.Demangle.Defs
public import Silmaril.Wasm.Tools.Meta.Cli.Defs
public import Silmaril.Wasm.Tools.Meta.Help.Defs
public import Silmaril.Wasm.Tools.Meta.Metadata.Defs
public import Silmaril.Wasm.Tools.Meta.FastCmd.Defs
public import Silmaril.Wasm.Tools.Meta.Addr2line.Defs

/-!
# `wasm-tools demangle`, `metadata show`, `metadata add`: the command-line layer

This file only reads arguments and files, calls the pure cores and writes their results:

| subcommand | arguments | core |
|---|---|---|
| `demangle` | `Cli.demangleCmd` | `Silmaril.Wasm.Tools.Meta.Demangle.demangle` |
| `metadata show` | `Cli.showCmd` | `Metadata.payloadOf`, `showJson`, `showText` |
| `metadata add` | `Cli.addCmd` | `Metadata.addMetadata` |

Input handling follows `wasm_tools::InputArg::get_binary_wasm`: the file (or stdin for none or
`-`), used as is when it starts with the Wasm magic number and otherwise parsed as WAT. The WAT
parser and the printer for `-t` are not part of this track: they come in through `Hooks`
(supplied by the `wasm-tools` main dispatch); without them, text input and `-t` fail with an
explicit error.

Exit status as upstream: 0 on success, 1 on an error (printed as `error: …` with the
`Caused by:` chain), 2 on a usage error, 0 for `-h`/`--help`.
-/

public section

namespace WasmTools.Meta

open Silmaril.Wasm.Tools.Meta
open Silmaril.Wasm.Tools.Meta.Cli

/-- What the rest of `wasm-tools` provides: the WAT parser (`wat::Parser`) and the printer
(`wasmprinter`, for `-t`). -/
structure Hooks where
  parseText : Option (ByteArray → Except String ByteArray) := none
  printWat : Option (ByteArray → Except String String) := none

/-- An error: its message and the chain of causes (anyhow's `Caused by:`). -/
structure Err where
  msg : String
  causes : List String := []

/-- `print_error` of `src/bin/wasm-tools/main.rs` (colours off). -/
def Err.render (e : Err) : String :=
  let head := "error: " ++ e.msg ++ "\n"
  if e.causes.isEmpty then head else
  head ++ "\nCaused by:\n" ++ String.join (e.causes.zipIdx.map fun (c, i) =>
    let n := toString i
    "".pushn ' ' (5 - n.length) ++ n ++ ": " ++ c.replace "\n" "\n       " ++ "\n")

abbrev M := ExceptT Err IO

/-- The message of an I/O error as Rust's `std::io::Error` prints it, for the common cases. -/
def ioMsg (e : IO.Error) : String :=
  match e with
  | .noFileOrDirectory .. => "No such file or directory (os error 2)"
  | .permissionDenied .. => "Permission denied (os error 13)"
  | .otherError 21 _ => "Is a directory (os error 21)"
  | .inappropriateType _ 21 _ => "Is a directory (os error 21)"
  | e => toString e

/-- The bytes of the input (the file, or stdin for none or `-`) and its name. -/
def readRaw (input : Option String) : M (ByteArray × String) :=
  match input with
    | some p =>
      if p == "-" then do pure (← (IO.getStdin >>= (·.readBinToEnd) : IO ByteArray), "<stdin>") else do
      match ← (IO.FS.readBinFile p).toBaseIO with
      | .ok b => pure (b, p)
      | .error e => throw { msg := "failed to read from `" ++ p ++ "`", causes := [ioMsg e] }
    | none => do pure (← (IO.getStdin >>= (·.readBinToEnd) : IO ByteArray), "<stdin>")

/-- `InputArg::get_binary_wasm` on input bytes read by `readRaw`. -/
def toBinary (h : Hooks) (bytes : ByteArray) (nm : String) : M ByteArray := do
  if bytes.size ≥ 4 && bytes.extract 0 4 == ByteArray.mk #[0, 0x61, 0x73, 0x6d] then pure bytes
  -- `wat::parse_bytes` of a text with no module fields (an empty input, for one)
  else if (String.fromUTF8? bytes).any (·.trimAscii.isEmpty) then
    throw { msg := "expected at least one module field" }
  else match h.parseText with
    | some f => match f bytes with
      | .ok b => pure b
      | .error e => throw { msg := e }
    | none => throw { msg := "input " ++ nm ++
        " is not a binary (no Wasm magic number): WebAssembly text input needs the WAT parser, which this build does not include" }

/-- `InputArg::get_binary_wasm`. -/
def readInput (h : Hooks) (input : Option String) : M ByteArray := do
  let (bytes, nm) ← readRaw input
  toBinary h bytes nm

/-- `OutputArg::output` of a binary (or its text with `-t`). -/
def writeWasm (h : Hooks) (output : Option String) (wat : Bool) (b : ByteArray) : M Unit := do
  if wat then
    match h.printWat with
    | some f => match f b with
      | .ok s => writeStr output s
      | .error e => throw { msg := e }
    | none => throw { msg := "`-t` needs the WebAssembly printer, which this build does not include" }
  else match output with
    | some p =>
      match ← (IO.FS.writeBinFile p b).toBaseIO with
      | .ok () => pure ()
      | .error e => throw { msg := "failed to write `" ++ p ++ "`", causes := [ioMsg e] }
    | none =>
      let out ← IO.getStdout
      if ← out.isTty then
        throw { msg := "cannot print binary wasm output to a terminal, pass the `-t` flag to print the text format" }
      out.write b
      out.flush
where
  writeStr (output : Option String) (s : String) : M Unit := do
    match output with
    | some p =>
      match ← (IO.FS.writeFile p s).toBaseIO with
      | .ok () => pure ()
      | .error e => throw { msg := "failed to write `" ++ p ++ "`", causes := [ioMsg e] }
    | none => let out ← IO.getStdout; out.putStr s; out.flush

/-- Run a subcommand body, printing errors as upstream; the exit status. -/
def runM (act : M Unit) : IO UInt32 := do
  match ← act.run with
  | .ok () => pure 0
  | .error e => (← IO.getStderr).putStr e.render; pure 1

/-- Parse arguments; print help or a usage error. -/
def withArgs (c : Cmd) (helpShort helpLong : String) (args : List String)
    (k : List (String × Option String) → Option String → IO UInt32) : IO UInt32 := do
  match parseArgs c args with
  | .error e => (← IO.getStderr).putStr e; pure 2
  | .ok (.usage long) => (← IO.getStdout).putStr (if long then helpLong else helpShort); pure 0
  | .ok (.ok seen input) => k seen input

open Silmaril.Wasm.Tools.Meta.Help
open Silmaril.Wasm.Tools.Meta (Producers)

/-! ## The records of the command lines

One record per subcommand: what its body reads. `…Args.ofSeen` reads it from the occurrences of
this module's reader (`Cli.parseArgs`, the core build); the full build reads it from the
matches of the CLI specification (`WasmTools.SpecCore`). The bodies are functions of the
record (`demangleWith`, `showWith`, `addWith`, `addr2lineWith`). -/

/-- The number of occurrences of a flag. -/
def Parsed.count (seen : List (String × Option String)) (k : String) : Nat :=
  (seen.filter (·.1 == k)).length

/-- `wasm-tools demangle`. -/
structure DemangleArgs where
  /-- `[INPUT]` (none or `-`: stdin) -/
  input : Option String
  /-- `-o, --output <OUTPUT>` -/
  output : Option String
  /-- `-t, --wat` -/
  wat : Bool
  verbose : Nat
  /-- `--color <COLOR>` (default `auto`) -/
  color : String
  deriving Repr, DecidableEq

def DemangleArgs.ofSeen (seen : List (String × Option String)) (input : Option String) :
    DemangleArgs where
  input := input
  output := Parsed.get? seen "output"
  wat := Parsed.has seen "wat"
  verbose := Parsed.count seen "verbose"
  color := (Parsed.get? seen "color").getD "auto"

/-- `wasm-tools metadata show`. -/
structure ShowArgs where
  input : Option String
  output : Option String
  /-- `--json` -/
  json : Bool
  verbose : Nat
  color : String
  deriving Repr, DecidableEq

def ShowArgs.ofSeen (seen : List (String × Option String)) (input : Option String) :
    ShowArgs where
  input := input
  output := Parsed.get? seen "output"
  json := Parsed.has seen "json"
  verbose := Parsed.count seen "verbose"
  color := (Parsed.get? seen "color").getD "auto"

/-- The body of `wasm-tools demangle` on its record. -/
def demangleWith (h : Hooks) (a : DemangleArgs) : IO UInt32 := runM do
    let b ← readInput h a.input
    match Demangle.demangleB b with
    | .ok out => writeWasm h a.output a.wat out
    | .error e => throw { msg := e }

/-- The body of `wasm-tools demangle` on the occurrences of `Cli.parseArgs` (`demangleMain`). -/
def demangleBody (h : Hooks) (seen : List (String × Option String)) (input : Option String) :
    IO UInt32 := demangleWith h (DemangleArgs.ofSeen seen input)

/-- `wasm-tools demangle`. -/
def demangleMain (h : Hooks) (args : List String) : IO UInt32 :=
  withArgs demangleCmd helpDemangleH helpDemangleHelp args (demangleBody h)

/-- Write text to `-o` or stdout. -/
def writeText (output : Option String) (s : String) : M Unit :=
  writeWasm.writeStr output s

/-- The body of `wasm-tools metadata show` on its record. -/
def showWith (h : Hooks) (a : ShowArgs) : IO UInt32 := runM do
    let b ← readInput h a.input
    match Metadata.payloadOfB b with
    | .error e => throw { msg := e }
    | .ok p =>
      writeText a.output (if a.json then Metadata.showJson p else Metadata.showText p)

/-- The body of `wasm-tools metadata show` on the occurrences of `Cli.parseArgs` (`showMain`). -/
def showBody (h : Hooks) (seen : List (String × Option String)) (input : Option String) :
    IO UInt32 := showWith h (ShowArgs.ofSeen seen input)

/-- `wasm-tools metadata show`. -/
def showMain (h : Hooks) (args : List String) : IO UInt32 :=
  withArgs showCmd helpMetadataShowH helpMetadataShowHelp args (showBody h)

/-- A `--x`/`--clear-x` pair as an `AddMetadataField`. -/
def fieldOf (seen : List (String × Option String)) (x : String) : Metadata.Field :=
  match Parsed.get? seen x with
  | some v => .set v
  | none => if Parsed.has seen ("clear-" ++ x) then .clear else .keep

/-- `NAME=VERSION` split at the first `=`. -/
def kv (s : String) : String × String :=
  match s.splitOn "=" with
  | k :: rest => (k, "=".intercalate rest)
  | [] => (s, "")

/-- `AddMetadataOpts` into `AddMetadata`. -/
def addOf (seen : List (String × Option String)) : Metadata.Add :=
  { name := fieldOf seen "name",
    language := (Parsed.getAll seen "language").map kv,
    processedBy := (Parsed.getAll seen "processed-by").map kv,
    sdk := (Parsed.getAll seen "sdk").map kv,
    authors := fieldOf seen "authors", description := fieldOf seen "description",
    licenses := fieldOf seen "licenses", source := fieldOf seen "source",
    homepage := fieldOf seen "homepage", revision := fieldOf seen "revision",
    version := fieldOf seen "version" }

/-- The value checks clap runs on `--licenses`, `--source`, `--homepage`. -/
def licenseCheck (v : String) : Option String := (Spdx.checkLicense v).map (v ++ "\n" ++ ·)

/-- The `metadata add` command with its value parsers. -/
def addCmdFull : Cmd :=
  let c := addCmd licenseCheck
  let urlCheck (v : String) : Option String := match Url.normalizeUrl v with
    | .ok _ => none
    | .error e => some e
  { c with opts := c.opts.map fun o =>
      if o.long == "source" || o.long == "homepage" then { o with check := urlCheck } else o }

/-- `wasm-tools metadata add`. -/
structure AddArgs where
  input : Option String
  output : Option String
  wat : Bool
  /-- `--generate-dwarf` or `-g` given (no effect: the input is read as is) -/
  dwarf : Bool
  /-- the fields to set, clear or keep, and the producers to add -/
  add : Metadata.Add
  verbose : Nat
  color : String
  deriving Repr, DecidableEq

def AddArgs.ofSeen (seen : List (String × Option String)) (input : Option String) : AddArgs where
  input := input
  output := Parsed.get? seen "output"
  wat := Parsed.has seen "wat"
  dwarf := Parsed.has seen "generate-dwarf" || Parsed.has seen "-g"
  add := addOf seen
  verbose := Parsed.count seen "verbose"
  color := (Parsed.get? seen "color").getD "auto"

/-- The body of `wasm-tools metadata add` on its record. -/
def addWith (h : Hooks) (a : AddArgs) : IO UInt32 := runM do
    let b ← readInput h a.input
    match Metadata.addMetadataB a.add b with
    | .error e => throw { msg := e }
    | .ok out => writeWasm h a.output a.wat out

/-- The body of `wasm-tools metadata add` on the occurrences of `Cli.parseArgs` (`addMain`). -/
def addBody (h : Hooks) (seen : List (String × Option String)) (input : Option String) :
    IO UInt32 := addWith h (AddArgs.ofSeen seen input)

/-- `wasm-tools metadata add`. -/
def addMain (h : Hooks) (args : List String) : IO UInt32 :=
  withArgs addCmdFull helpMetadataAddH helpMetadataAddHelp args (addBody h)

/-- `wasm-tools metadata`: `show`, `add`, `help`. -/
def metadataMain (h : Hooks) (args : List String) : IO UInt32 := do
  match args with
  | "show" :: rest => showMain h rest
  | "add" :: rest => addMain h rest
  | "help" :: rest =>
    match rest with
    | [] => (← IO.getStdout).putStr helpMetadataH; pure 0
    | ["show"] => (← IO.getStdout).putStr helpMetadataShowHelp; pure 0
    | ["add"] => (← IO.getStdout).putStr helpMetadataAddHelp; pure 0
    | ["help"] => (← IO.getStdout).putStr helpMetadataHelpHelp; pure 0
    -- clap: a further name after a leaf subcommand is an unknown subcommand of that leaf
    | "show" :: a :: _ =>
      (← IO.getStderr).putStr (clapError ("unrecognized subcommand '" ++ a ++ "'")
        (some "wasm-tools metadata show [OPTIONS] [INPUT]")); pure 2
    | "add" :: a :: _ =>
      (← IO.getStderr).putStr (clapError ("unrecognized subcommand '" ++ a ++ "'")
        (some "wasm-tools metadata add [OPTIONS] [INPUT]")); pure 2
    | "help" :: a :: _ =>
      (← IO.getStderr).putStr ("error: unrecognized subcommand '" ++ a ++
        "'\n\nUsage: wasm-tools metadata help [COMMAND]...\n"); pure 2
    | a :: _ =>
      (← IO.getStderr).putStr (clapError ("unrecognized subcommand '" ++ a ++ "'")
        (some "wasm-tools metadata <COMMAND>")); pure 2
  | a :: _ =>
    if a == "-h" || a == "--help" then (← IO.getStdout).putStr helpMetadataH; pure 0
    else if flagLike a then
      -- no positional argument, so no `-- ARG` tip; a long flag may be close to `--help`
      let n := if a.startsWith "--" then ((a.splitOn "=").headD a) else
        "-" ++ ((dropS a 1).toList.headD ' ').toString
      let sugg := if a.startsWith "--" then Silmaril.Wasm.Tools.Suggest.didYouMean (dropS n 2) ["help"]
        else none
      match sugg with
      | some l =>
        (← IO.getStderr).putStr (clapError ("unexpected argument '" ++ n ++
          "' found\n\n  tip: a similar argument exists: '--" ++ l ++ "'")
          (some "wasm-tools metadata --help <COMMAND>")); pure 2
      | none =>
        (← IO.getStderr).putStr (clapError ("unexpected argument '" ++ n ++ "' found")
          (some "wasm-tools metadata <COMMAND>")); pure 2
    else
      let tip := match Silmaril.Wasm.Tools.Suggest.didYouMean a ["show", "add", "help"] with
        | some s => "\n\n  tip: a similar subcommand exists: '" ++ s ++ "'"
        | none => ""
      (← IO.getStderr).putStr (clapError ("unrecognized subcommand '" ++ a ++ "'" ++ tip)
        (some "wasm-tools metadata <COMMAND>")); pure 2
  | [] => (← IO.getStderr).putStr helpMetadataH; pure 2

/-- `wasm-tools addr2line`. -/
structure Addr2lineArgs where
  input : Option String
  /-- `[ADDRESSES]...`, in order -/
  addresses : List String
  output : Option String
  /-- `--generate-dwarf` or `-g` given -/
  dwarf : Bool
  codeSectionRelative : Bool
  verbose : Nat
  color : String
  deriving Repr, DecidableEq

def Addr2lineArgs.ofSeen (seen : List (String × Option String)) (input : Option String) :
    Addr2lineArgs where
  input := input
  addresses := Parsed.getAll seen "ADDRESSES"
  output := Parsed.get? seen "output"
  dwarf := Parsed.has seen "generate-dwarf" || Parsed.has seen "-g"
  codeSectionRelative := Parsed.has seen "code-section-relative"
  verbose := Parsed.count seen "verbose"
  color := (Parsed.get? seen "color").getD "auto"

/-- The body of `wasm-tools addr2line` on its record. -/
def addr2lineWith (h : Hooks) (r : Addr2lineArgs) : IO UInt32 := runM do
    let dwarf := r.dwarf
    -- read once: stdin cannot be read a second time
    let (raw, nm) ← readRaw r.input
    let isBin := raw.size ≥ 4 && raw.extract 0 4 == ByteArray.mk #[0, 0x61, 0x73, 0x6d]
    if dwarf && !isBin then
      throw { msg := "`--generate-dwarf` needs DWARF generation by the WAT parser, which this build does not include" }
    let ba ← toBinary h raw nm
    let mods ← match Addr2line.modulesOf ba with
      | .ok m => pure m
      | .error (m, c) => throw { msg := m, causes := [c] }
    let csr := r.codeSectionRelative
    let mut out := ""
    let mut ctxs : Array (Option Silmaril.Wasm.Tools.Dwarf.Context) := Array.replicate mods.size none
    let mut caches : Array Silmaril.Wasm.Tools.Dwarf.Cache := Array.replicate mods.size {}
    let output := r.output
    let fail (out : String) (a : String) (causes : List String) : M Unit := do
      writeText output out
      throw { msg := "failed to find frames for `" ++ a ++ "`", causes }
    for a in r.addresses do
      let n ← match Addr2line.parseAddr a with
        | .ok n => pure n
        | .error e => fail out a [e]; pure 0
      let picked ← match Addr2line.pick mods n csr with
        | .ok p => pure p
        | .error e => fail out a [e]; pure none
      let some (i, rel) := picked | fail out a ["no module found which contains this address"]
      let c ← match ctxs[i]! with
        | some c => pure c
        | none =>
          match Silmaril.Wasm.Tools.Dwarf.Context.parse (mods[i]!.secs ba) with
          | .ok c => ctxs := ctxs.set! i (some c); pure c
          | .error e =>
            fail out a ["failed to create addr2line dwarf mapping context", e]
            pure default
      let (r, k) := c.findFramesC caches[i]! rel
      caches := caches.set! i k
      match r with
      | .ok fs => out := out ++ Addr2line.render a fs
      | .error e => fail out a [e]
    writeText output out

/-- The body of `wasm-tools addr2line` on the occurrences of `Cli.parseArgs` (`addr2lineMain`). -/
def addr2lineBody (h : Hooks) (seen : List (String × Option String)) (input : Option String) :
    IO UInt32 := addr2lineWith h (Addr2lineArgs.ofSeen seen input)

/-- `wasm-tools addr2line`. -/
def addr2lineMain (h : Hooks) (args : List String) : IO UInt32 :=
  withArgs addr2lineCmd helpAddr2lineH helpAddr2lineHelp args (addr2lineBody h)

/-- The subcommands of this track: name and entry point (arguments after the name). -/
def subcommands (h : Hooks) : List (String × (List String → IO UInt32)) :=
  [("demangle", demangleMain h), ("metadata", metadataMain h), ("addr2line", addr2lineMain h)]

end WasmTools.Meta

end
