import WasmTools.Types
import WasmTools.Args
import WasmTools.Io
import WasmTools.Help
import WasmTools.Completion
import WasmTools.CompHook
import Silmaril.Wasm.Tools.Text.Defs
import Silmaril.Wasm.Tools.Print.Defs
import Silmaril.Wasm.Tools.PrintCheck.Defs

/-!
# `wasm-tools parse` and `wasm-tools print` (cli track)

Grammars (`parseSpec`, `printSpec`) as data, and thin bodies: read the input, call one pure
core function of `Silmaril.Wasm.Tools.Text` (theorems in `Silmaril.Wasm.Tools.Text.Thms`), write
the output. Options accepted for compatibility but without effect yet are listed in
`tools/wasm-tools/README.md` (Known limitations); the ones that would change the output
(`-g`, `--generate-dwarf`, and `print`'s formatting options) are refused with an error rather
than ignored.
-/

namespace WasmTools.Core

open Args
open Silmaril.Wasm.Tools

open Silmaril.Wasm.Tools.Cli in
/-- Options shared by `parse` and `print` (upstream's `GenerateDwarfArg`, `InputOutput`,
`GeneralOpts`). -/
def ioOpts : List Opt :=
  [ { key := "generate-dwarf", long := some "generate-dwarf", takes := .value "lines|full" ["lines", "full"] },
    { key := "g", short := some 'g' },
    { key := "output", long := some "output", short := some 'o', takes := .value "OUTPUT" [] },
    { key := "verbose", long := some "verbose", short := some 'v', takes := .count },
    { key := "color", long := some "color", takes := .value "COLOR" ["always", "always-ansi", "never", "auto"] } ]

open Silmaril.Wasm.Tools.Cli in
def parseSpec : Spec where
  usage := "wasm-tools parse [OPTIONS] [INPUT]"
  opts := ioOpts ++ [{ key := "wat", long := some "wat", short := some 't' }]
  pos := [{ key := "INPUT", name := "INPUT" }]

open Silmaril.Wasm.Tools.Cli in
def printSpec : Spec where
  usage := "wasm-tools print [OPTIONS] [INPUT]"
  opts := ioOpts ++
    [ { key := "print-offsets", long := some "print-offsets", short := some 'p' },
      { key := "skeleton", long := some "skeleton" },
      { key := "name-unnamed", long := some "name-unnamed" },
      { key := "fold-instructions", long := some "fold-instructions", short := some 'f' },
      { key := "print-operand-stack", long := some "print-operand-stack" },
      { key := "indent-text", long := some "indent-text", takes := .value "INDENT_TEXT" [] },
      { key := "indent", long := some "indent", takes := .value "INDENT" [] } ]
  pos := [{ key := "INPUT", name := "INPUT" }]

/-! ## The records of the command lines

What the bodies of `parse` and `print` read. `…ofParsed` reads a record from the occurrences of
the core build's reader (`Silmaril.Wasm.Tools.Cli`, through `Io.runCli`); the full build reads it
from the matches of the CLI specification (`WasmTools.SpecCore`). -/

/-- What `parse` and `print` share (upstream's `InputOutput`, `GeneralOpts`,
`GenerateDwarfArg`). -/
structure IoArgs where
  /-- `[INPUT]` (none or `-`: stdin) -/
  input : Option String
  /-- `-o, --output <OUTPUT>` -/
  output : Option String
  /-- `--generate-dwarf <lines|full>` -/
  generateDwarf : Option String
  /-- `-g` -/
  g : Bool
  verbose : Nat
  /-- `--color <COLOR>` (default `auto`) -/
  color : String
  deriving Repr, DecidableEq

def IoArgs.ofParsed (p : Parsed) : IoArgs where
  input := p.positionals.head?
  output := p.value? "output"
  generateDwarf := (p.values "generate-dwarf").getLast?
  g := p.flag "g"
  verbose := p.count "verbose"
  color := ((p.values "color").getLast?).getD "auto"

/-- `wasm-tools parse`. -/
structure ParseArgs where
  io : IoArgs
  /-- `-t, --wat` -/
  wat : Bool
  deriving Repr, DecidableEq

def ParseArgs.ofParsed (p : Parsed) : ParseArgs where
  io := IoArgs.ofParsed p
  wat := p.flag "wat"

/-- `wasm-tools print`. -/
structure PrintArgs where
  io : IoArgs
  printOffsets : Bool
  skeleton : Bool
  nameUnnamed : Bool
  foldInstructions : Bool
  printOperandStack : Bool
  /-- `--indent-text <INDENT_TEXT>` -/
  indentText : Option String
  /-- `--indent <INDENT>` (the word given; the body reads the number) -/
  indent : Option String
  deriving Repr, DecidableEq

def PrintArgs.ofParsed (p : Parsed) : PrintArgs where
  io := IoArgs.ofParsed p
  printOffsets := p.flag "print-offsets"
  skeleton := p.flag "skeleton"
  nameUnnamed := p.flag "name-unnamed"
  foldInstructions := p.flag "fold-instructions"
  printOperandStack := p.flag "print-operand-stack"
  indentText := (p.values "indent-text").getLast?
  indent := (p.values "indent").getLast?

def liftE {α} : Except String α → ExceptT String IO α
  | .ok a => pure a
  | .error e => throw e

/-- Options that would change the output and are not implemented: the options by name, whether
each was given. -/
def refuse (asked : List (String × Bool)) : ExceptT String IO Unit := do
  for (k, b) in asked do
    if b then throw s!"option `{k}` is not implemented by this wasm-tools (see tools/wasm-tools/README.md)"

/-- The chunk size of the parallel field passes (`PrintCheck.parMapM`): `WASM_TOOLS_LEAN_CHUNK`, or
`PrintCheck.defaultChunk`. Every value gives the same output (`PrintCheck.Thms`). -/
def chunk : IO Nat := do
  pure (((← IO.getEnv "WASM_TOOLS_LEAN_CHUNK").bind String.toNat?).filter (· > 0) |>.getD
    PrintCheck.defaultChunk)

/-- Whether text output is coloured (`OutputArg::output_writer` and termcolor 1.4.1's
`ColorChoice`): to a file only with `--color always-ansi`; to stdout with `always` or
`always-ansi`, and with `auto` (the default) when stdout is a terminal, `TERM` is set and not
`dumb`, and `NO_COLOR` is unset. -/
def useColor (io : IoArgs) : IO Bool := do
  let c := io.color
  match io.output with
  | some _ => pure (c == "always-ansi")
  | none =>
    if c == "always" || c == "always-ansi" then return true
    if c == "never" then return false
    if !(← (← IO.getStdout).isTty) then return false
    match ← IO.getEnv "TERM" with
    | none => pure false
    | some t => if t == "dumb" then pure false else pure (← IO.getEnv "NO_COLOR").isNone

/-- The certified text `plain` of `bin`, coloured when `useColor` (`PrintCheck.colorText`:
kept only when its escapes removed give `plain`). -/
def colored (io : IoArgs) (cfg : Silmaril.Wasm.Tools.Print.Config) (bin : ByteArray) (plain : String) :
    IO String := do
  if ← useColor io then pure (PrintCheck.colorText cfg bin plain) else pure plain

/-- In the full build (`WasmTools.CompHook.hooks` set), a component input
(`CompVal.isComponentInput`: a component binary, or text starting with `(component`) goes to the
compval track's path, which writes exactly what `wasm-tools-cv` writes; the options it does not
read (`-g`, `--color`, `print`'s formatting options) do not change its output. Every other
input, and every input of the core build, stays on the core path. -/
def component (input : ByteArray)
    (run : CompHook.Hooks → ByteArray → IO (Except String Unit)) : ExceptT String IO Bool := do
  let some h ← (monadLift (CompHook.hooks.get : IO _) : ExceptT String IO _) | return false
  if h.isComponent input then
    let r ← (monadLift (run h input : IO (Except String Unit)) : ExceptT String IO _)
    liftE r
    return true
  return false

/-- The body of `parse` on its record. -/
def parseWith (a : ParseArgs) : ExceptT String IO Unit := do
  let input ← Io.readInput a.io.input
  if ← component input (fun h => h.parseOn a.wat a.io.output) then return
  refuse [("generate-dwarf", a.io.generateDwarf.isSome), ("g", a.io.g)]
  -- the fast paths are equal to `Text.watToWat` / `Text.watToBinary` (`PrintCheck.Thms`)
  let k ← chunk
  let bin ← liftE (PrintCheck.watToBinaryFast k input)
  if a.wat then
    -- `watToWatFast` (= `Text.watToWat`), with colours when asked
    let plain ← liftE (PrintCheck.binaryToWatWithFast k {} bin)
    Io.writeText a.io.output (← colored a.io {} bin plain)
  else Io.writeBinary a.io.output bin

/-- The body of `parse` on the occurrences of the core build's reader. -/
def parseBody (p : Parsed) : ExceptT String IO Unit := parseWith (ParseArgs.ofParsed p)

/-- The body of `print` on its record. -/
def printWith (a : PrintArgs) : ExceptT String IO Unit := do
  -- `--indent-text` wins over `--indent N` (N spaces)
  let indent ← match a.indent with
    | none => pure none
    | some v => match v.toNat? with
      | some n => pure (some (String.ofList (List.replicate n ' ')))
      | none => throw (Io.usageMark ++
          s!"error: invalid value '{v}' for '--indent <INDENT>': invalid digit found in string\n\nFor more information, try '--help'.\n")
  let indentText := (a.indentText <|> indent).getD "  "
  let input ← Io.readInput a.io.input
  if ← component input (fun h => h.printOn a.io.output) then return
  refuse [("generate-dwarf", a.io.generateDwarf.isSome), ("g", a.io.g),
    ("print-operand-stack", a.printOperandStack)]
  let k ← chunk
  let bin ← liftE (PrintCheck.watToBinaryFast k input)
  let cfg : Silmaril.Wasm.Tools.Print.Config :=
    { skeleton := a.skeleton, nameUnnamed := a.nameUnnamed, indentText,
      printOffsets := a.printOffsets, fold := a.foldInstructions }
  if (← IO.getEnv "WASM_TOOLS_LEAN_PRINT_CHECK").isSome then
    match PrintCheck.printModuleFast k cfg bin with
    | .ok r =>
      IO.eprintln s!"print-check: {if r.certified then "certified" else "uncertified"}"
    | .error _ => pure ()
  let wsIndent := indentText.all (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
  if cfg.skeleton || !wsIndent then
    -- `--skeleton` elides bodies, and an indentation that is not whitespace is not WAT, so
    -- these texts are not module texts and are not checked (tools/wasm-tools/README.md).
    match PrintCheck.printModuleFast k { cfg with color := ← useColor a.io } bin with
    | .ok r => Io.writeText a.io.output r.text
    | .error e => throw e.message
  else
    let plain ← liftE (PrintCheck.binaryToWatWithFast k cfg bin)
    Io.writeText a.io.output (← colored a.io cfg bin plain)

/-- The body of `print` on the occurrences of the core build's reader. -/
def printBody (p : Parsed) : ExceptT String IO Unit := printWith (PrintArgs.ofParsed p)

def table : List Subcommand :=
  [ ⟨"parse", Io.runCli parseSpec Help.parse_short Help.parse_long parseBody⟩,
    ⟨"print", Io.runCli printSpec Help.print_short Help.print_long printBody⟩ ] ++
    Completion.table

end WasmTools.Core
