import WasmTools.Top
import Silmaril.Cli.Spec.WasmTools.Defs
import Silmaril.Cli.Clap.Main.Defs

/-!
# `wasm-tools` behind its CLI specification: the program entry

The `main` of the full build (`WasmTools.lean`) and of the wave-2 test drivers
(`wasm-tools-gen`, `wasm-tools-cv`): **`(WasmTools.toolAt w).main run`** (`Clap.Tool.main`).
The specification of upstream's command line, `Silmaril.Cli.Spec.WasmTools.tool`, reads every
command line (the clap pre-pass, the args parser proved sound and complete, the value checks,
the `requires`/`conflicts_with` rules); help, version, a missing subcommand and every usage
error are its texts (clap's exact texts, `Silmaril.Cli.Clap.Exact`, at clap's width
`w = Help.widthOf COLUMNS`), with their exit codes; a command line that runs hands its
`Matches` to `run`, which dispatches on `m.path` to the subcommand's body. Each subcommand reads
what it needs from the matches in one place, its `ofMatches` (`WasmTools.SpecArgs`), and no
other grammar reads the command line.

The tool differs from the specification's only in its presentation of the root's `--version`
(this build's `WasmTools.versionLine`); `toolAt_grammar` states that its grammar is the
specification's and `WasmTools.SpecThms.toolAt_read` that it reads every command line as
the specification does, so `Clap.Tool.main_refines` and `Clap.Tool.spec_usageError`
apply as they are.

Hidden options of upstream (not shown in help, so not in the specification:
`component new --skip-validation`) are taken off the command line before the reading and handed
to `run` (`Hidden`).
-/

namespace WasmTools

open Silmaril.Cli

/-- The specification without presentation (`Silmaril.Cli.Spec.WasmTools.toolBase`). -/
abbrev specBase : Clap.Tool := Silmaril.Cli.Spec.WasmTools.toolBase

/-- Whether `argv` asks for the root's version (`-V`, `--version` before any subcommand). -/
def rootVersion (argv : List String) : Bool :=
  Clap.wordsPath specBase.grammar [specBase.grammar.name] argv == [specBase.grammar.name]

/-- **`wasm-tools` at clap width `w`**: the specification's grammar and texts (clap's exact
texts at `w` columns), the root's version line this build's (`versionLine`). -/
def toolAt (w : Nat) : Clap.Tool :=
  { specBase with present := some fun argv o =>
      match o with
      | .version =>
        if rootVersion argv then Clap.chomp versionLine
        else specBase.exact Silmaril.Cli.Spec.WasmTools.reason w argv o
      | _ => specBase.exact Silmaril.Cli.Spec.WasmTools.reason w argv o }

/-- **`wasm-tools`** at clap's default width (a pipe without `COLUMNS`). -/
def tool : Clap.Tool := toolAt Clap.Help.width

/-- The tool reads with the specification's grammar. -/
theorem toolAt_grammar (w : Nat) : (toolAt w).grammar = Silmaril.Cli.Spec.WasmTools.tool.grammar :=
  rfl

/-- Hidden options of upstream 1.262.0 (not shown in help, so not in the specification): the
command path and the option. -/
def hidden : List (List String × String) :=
  [(["component", "new"], "--skip-validation")]

/-- The hidden options a command line gives: the line without them, and the options given. -/
def Hidden.split (argv : List String) : List String × List String :=
  match hidden.find? fun (p, o) => argv.take p.length == p && (argv.drop p.length).contains o with
  | some (p, o) => (p ++ (argv.drop p.length).filter (· != o), [o])
  | none => (argv, [])

/-- A subcommand of upstream that this build does not implement: `error: …`, exit 1. -/
def notImplemented (path : List String) (note : String := "") : IO UInt32 := do
  (← IO.getStderr).putStr
    s!"error: wasm-tools {" ".intercalate path}: not implemented in this build{note}\n"
  return 1

/-- **The program**: `(toolAt w).main` at clap's width from `COLUMNS`, the matches to
`run hidden argv` (the hidden options given and the command line read). -/
def specMain (run : List String → List String → Matches → IO UInt32) (args : List String) :
    IO UInt32 := do
  let w := Clap.Help.widthOf (← IO.getEnv "COLUMNS")
  let (argv, hid) := Hidden.split args
  (toolAt w).main (run hid argv) argv

end WasmTools
