import WasmTools.SpecArgs
import WasmTools.SpecMain
import WasmTools.Core
import WasmTools.Validate
import WasmTools.ValidateComp
import WasmTools.Meta
import WasmTools.Wast
import Silmaril.Wasm.Tools.Wast.Spec.Defs

/-!
# The core subcommands on the specification's matches (the full build)

The bodies of the core groups (`parse`, `print`, `completion`, `validate`, `strip`, `objdump`,
`dump`, `demangle`, `metadata show`, `metadata add`, `addr2line`, `json-from-wast`, `wast`) are
functions of one typed record each (`Core.ParseArgs`, `Core.PrintArgs`,
`CompVal.ValidateArgs`, `Strip.StripOpts`, `VCommon.InOut`, `Meta.DemangleArgs`,
`Meta.ShowArgs`, `Meta.AddArgs`, `Meta.Addr2lineArgs`, `Wast.Cli.JsonOpts`, `Wast.Cli.WastOpts`),
read here from what the specification `Silmaril.Cli.Spec.WasmTools.tool` read, through one
`…ofMatches` each.

The core build (`wasm-tools-core`, the first release's binary) builds the same records from its
own readers (`…ofParsed`/`…ofSeen` over `Silmaril.Wasm.Tools.Cli`, `Silmaril.Wasm.Tools.OptGrammar`,
`Silmaril.Wasm.Tools.Meta.Cli`; `Silmaril.Wasm.Tools.Wast.Cli`'s records; `WasmTools.Args` for
`completion`): those readers are the variants of the first release. On a command line both
accept they give the bodies the same record: stated as `WasmTools.SpecThms.Task.*_agree`
(frozen: the readers are `partial def`s), checked on the derived corpus, the texts vectors and
the golden suites by `wasm-tools-agree` (`tools/wasm-tools/tests/args-agree.sh`), which compares
the records themselves.
-/

namespace WasmTools.SpecCore

open Silmaril.Cli

/-! ## `parse`, `print` (`Core.ParseArgs`, `Core.PrintArgs`) and `completion` -/

def _root_.WasmTools.Core.IoArgs.ofMatches (m : Matches) : Core.IoArgs where
  input := m.str? "input"
  output := m.str? "output"
  generateDwarf := m.str? "generate-dwarf"
  g := m.flag "-g"
  verbose := m.count "verbose"
  color := (m.str? "color").getD "auto"

def _root_.WasmTools.Core.ParseArgs.ofMatches (m : Matches) : Core.ParseArgs where
  io := Core.IoArgs.ofMatches m
  wat := m.flag "wat"

def _root_.WasmTools.Core.PrintArgs.ofMatches (m : Matches) : Core.PrintArgs where
  io := Core.IoArgs.ofMatches m
  printOffsets := m.flag "print-offsets"
  skeleton := m.flag "skeleton"
  nameUnnamed := m.flag "name-unnamed"
  foldInstructions := m.flag "fold-instructions"
  printOperandStack := m.flag "print-operand-stack"
  indentText := m.str? "indent-text"
  indent := m.str? "indent"

/-- Run a body of `parse` or `print`: a body's usage error (`Io.usageMark`) exit 2, other
errors `error: …` exit 1. -/
def runBody (body : ExceptT String IO Unit) : IO UInt32 := do
  match ← body.run with
  | .ok () => return 0
  | .error e =>
    match e.dropPrefix? Io.usageMark with
    | some t => (← IO.getStderr).putStr t.toString; return 2
    | none => (← IO.getStderr).putStr s!"error: {e}\n"; return 1

/-- `completion SHELL`: the script of the shell (the specification has checked the name). -/
def completion (m : Matches) : IO UInt32 := do
  match (m.str? "shell").bind (Completion.shells.lookup ·) with
  | some script =>
    let out ← IO.getStdout
    out.putStr script; out.flush
    return 0
  | none => (← IO.getStderr).putStr Completion.missing; return 2

/-! ## `strip`, `objdump`, `dump` (`VCommon.InOut`, `Strip.StripOpts`) -/

def _root_.WasmTools.VCommon.InOut.ofMatches (m : Matches) : VCommon.InOut where
  input := m.str? "input"
  output := m.str? "output"
  verbose := m.count "verbose"
  color := (m.str? "color").getD "auto"

def _root_.WasmTools.Strip.StripOpts.ofMatches (m : Matches) : Strip.StripOpts where
  io := VCommon.InOut.ofMatches m
  all := m.flag "all"
  delete := m.strs "delete"
  wat := m.flag "wat"

/-! ## `demangle`, `metadata`, `addr2line` (`Meta.DemangleArgs`, …) -/

def _root_.WasmTools.Meta.DemangleArgs.ofMatches (m : Matches) : Meta.DemangleArgs where
  input := m.str? "input"
  output := m.str? "output"
  wat := m.flag "wat"
  verbose := m.count "verbose"
  color := (m.str? "color").getD "auto"

def _root_.WasmTools.Meta.ShowArgs.ofMatches (m : Matches) : Meta.ShowArgs where
  input := m.str? "input"
  output := m.str? "output"
  json := m.flag "json"
  verbose := m.count "verbose"
  color := (m.str? "color").getD "auto"

/-- A `--x`/`--clear-x` pair of `metadata add`. -/
def fieldOf (m : Matches) (x : String) : Silmaril.Wasm.Tools.Meta.Metadata.Field :=
  match m.str? x with
  | some v => .set v
  | none => if m.flag ("clear-" ++ x) then .clear else .keep

def _root_.WasmTools.Meta.AddArgs.ofMatches (m : Matches) : Meta.AddArgs where
  input := m.str? "input"
  output := m.str? "output"
  wat := m.flag "wat"
  dwarf := m.flag "generate-dwarf" || m.flag "-g"
  add :=
    { name := fieldOf m "name",
      language := (m.strs "language").map WasmTools.Meta.kv,
      processedBy := (m.strs "processed-by").map WasmTools.Meta.kv,
      sdk := (m.strs "sdk").map WasmTools.Meta.kv,
      authors := fieldOf m "authors", description := fieldOf m "description",
      licenses := fieldOf m "licenses", source := fieldOf m "source",
      homepage := fieldOf m "homepage", revision := fieldOf m "revision",
      version := fieldOf m "version" }
  verbose := m.count "verbose"
  color := (m.str? "color").getD "auto"

def _root_.WasmTools.Meta.Addr2lineArgs.ofMatches (m : Matches) : Meta.Addr2lineArgs where
  input := m.str? "input"
  addresses := m.strs "addresses"
  output := m.str? "output"
  dwarf := m.flag "generate-dwarf" || m.flag "-g"
  codeSectionRelative := m.flag "code-section-relative"
  verbose := m.count "verbose"
  color := (m.str? "color").getD "auto"

/-- The value checks the specification leaves to the program (`metadata add --licenses`, an SPDX
expression; `--source`, `--homepage`, URLs): clap's message for the first value refused, in the
order of the command line's options (the options given, `SpecArgs.occs`). -/
def metaRefused (c : Silmaril.Wasm.Tools.Meta.Cli.Cmd) (m : Matches) : Option String :=
  (SpecArgs.occs m).findSome? fun (k, v) => do
    let o ← c.opts.find? (·.key == k)
    let v ← v
    let msg ← o.check v
    pure (Silmaril.Wasm.Tools.Meta.Cli.errInvalid o v msg)

/-- Run a meta body after the program's value checks. -/
def metaRun (c : Silmaril.Wasm.Tools.Meta.Cli.Cmd) (body : IO UInt32) (m : Matches) :
    IO UInt32 := do
  match metaRefused c m with
  | some e => (← IO.getStderr).putStr e; return 2
  | none => body

/-! ## `json-from-wast`, `wast` (`Wast.Cli`'s records) -/

/-- The records of `json-from-wast` and `wast` (`Silmaril.Wasm.Tools.Wast.Spec`). -/
abbrev jsonOfMatches := Silmaril.Wasm.Tools.Wast.Spec.jsonOfMatches
abbrev wastOfMatches := Silmaril.Wasm.Tools.Wast.Spec.wastOfMatches

/-! ## The dispatch -/

open Silmaril.Wasm.Tools.Meta.Cli in
/-- The core subcommands, by their path in the specification, on its matches (`none`: another
group's): each body on its record. -/
def byPath (m : Matches) : Option (IO UInt32) :=
  let h := WasmTools.Meta.mainHooks
  match m.path with
  | ["parse"] => some (runBody (Core.parseWith (Core.ParseArgs.ofMatches m)))
  | ["print"] => some (runBody (Core.printWith (Core.PrintArgs.ofMatches m)))
  | ["completion"] => some (completion m)
  | ["validate"] => some (ValidateComp.run (CompVal.ValidateArgs.ofMatches m))
  | ["strip"] => some (WasmTools.Strip.body (Strip.StripOpts.ofMatches m))
  | ["objdump"] => some (WasmTools.Objdump.body (VCommon.InOut.ofMatches m))
  | ["dump"] => some (WasmTools.Dump.body (VCommon.InOut.ofMatches m))
  | ["demangle"] =>
    some (metaRun demangleCmd (WasmTools.Meta.demangleWith h (Meta.DemangleArgs.ofMatches m)) m)
  | ["metadata", "show"] =>
    some (metaRun showCmd (WasmTools.Meta.showWith h (Meta.ShowArgs.ofMatches m)) m)
  | ["metadata", "add"] =>
    some (metaRun WasmTools.Meta.addCmdFull (WasmTools.Meta.addWith h (Meta.AddArgs.ofMatches m)) m)
  | ["addr2line"] =>
    some (metaRun addr2lineCmd (WasmTools.Meta.addr2lineWith h (Meta.Addr2lineArgs.ofMatches m)) m)
  | ["json-from-wast"] => some (WasmTools.Wast.jsonBody (jsonOfMatches m))
  | ["wast"] => some (WasmTools.Wast.wastBody (wastOfMatches m))
  | _ => none

end WasmTools.SpecCore
