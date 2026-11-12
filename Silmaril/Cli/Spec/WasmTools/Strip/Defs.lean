module

public import Silmaril.Cli.Spec.WasmTools.Defs
public import Silmaril.Cli.Clap.Main.Defs
public import Silmaril.Cli.Files.Defs

/-!
# Adopting the CLI spec in `wasm-tools`: `strip`, a worked example

The guide of docs/projects/wasm-binaryen-tooling.md ("apply", an earlier step) for the wasm-tools-core workflow
(`tools/wasm-tools`, branches `wtc-*`), worked out on one subcommand, `wasm-tools strip`
(upstream 1.262.0: `strip [OPTIONS] [INPUT]` with `-o, --output`, `-a, --all`,
`-d, --delete REGEX` (repeatable), `-t, --wat`, `-v`, `--color`):

1. **The command line is `Silmaril.Cli.Spec.WasmTools.tool`.** `wasm-tools`'s `main` becomes
   `WasmTools.tool.main run` (`Clap.Tool.main`): help, version, `help NAME…`, usage errors and
   their exit codes are derived; `run` receives the typed `Matches` and dispatches on
   `m.path`.
2. **A subcommand reads its matches into a record** (`StripArgs.ofMatches`), the only place
   that knows option ids; its body is a function of the record.
3. **Its behaviour is a spec on the record.** `strip` is a file transformer: the input file
   (or stdin), the output file (or stdout), a function on bytes (`Spec.transform`,
   `Silmaril.Cli.Files`). The function is a parameter here (`f`), since the stripping itself
   (`Silmaril.Wasm.Tools.Strip.strip` on `wtc-*`) lives in region `Wasm`, which `Cli` does not
   import; on the tool's side `f a` is `Strip.strip` (then the printer for `-t`), with
   upstream's error text.
4. **The whole tool's spec** is `WasmTools.tool.spec` with `strip`'s spec at `["strip"]` and
   anything elsewhere (`spec`); `Silmaril.Cli.Spec.WasmTools.Strip.Thms.main_refines` reduces the
   proof that the tool refines it to the one subcommand.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Spec.WasmTools.Strip

open Silmaril.Cli

/-- What `wasm-tools strip` needs from its command line. -/
structure StripArgs where
  /-- `[INPUT]` (none or `-`: stdin) -/
  input : Option String
  /-- `-o, --output <OUTPUT>` (none: stdout) -/
  output : Option String
  /-- `-a, --all` -/
  all : Bool
  /-- `-d, --delete <REGEX>`, in order -/
  delete : List String
  /-- `-t, --wat` -/
  wat : Bool
  deriving DecidableEq, Repr

/-- **The record of a run**, from the matches of `WasmTools.tool` at `["strip"]` (keys: the
option ids of the grammar). -/
def StripArgs.ofMatches (m : Matches) : StripArgs where
  input := m.str? "input"
  output := m.str? "output"
  all := m.flag "all"
  delete := m.strs "delete"
  wat := m.flag "wat"

/-- Where `strip` reads: the input file, or stdin when there is none or it is `-`. -/
def StripArgs.source (a : StripArgs) (i : Input) : Option Source :=
  match a.input with
  | none | some "-" => some .stdin
  | some s => (i.resolve s).map .file

/-- Where `strip` writes: the `-o` file, or stdout. -/
def StripArgs.sink (a : StripArgs) (i : Input) : Option Sink :=
  match a.output with
  | none => some .stdout
  | some s => (i.resolve s).map .file

/-- **The behaviour of `strip`**, for a byte function `f` (the stripping, then the printer
under `-t`; an error is the message on stderr, exit 1): read the source, write `f a` of it to
the sink. -/
def stripSpec (f : StripArgs → Bytes → Except Bytes Bytes) (m : Matches) : Spec :=
  let a := StripArgs.ofMatches m
  Spec.transform a.source a.sink fun _ => f a

/-- The subcommands this example specifies, by path. -/
def cmds (f : StripArgs → Bytes → Except Bytes Bytes) : List (List String × (Matches → Spec)) :=
  [(["strip"], stripSpec f)]

/-- The spec of a command's matches: the listed one at its path, else anything. -/
def bodySpec (cs : List (List String × (Matches → Spec))) (m : Matches) : Spec :=
  match cs.lookup m.path with
  | some S => S m
  | none => ⊤

/-- **`wasm-tools` with `strip` specified**: the derived front end of 1.262.0, `strip`'s
behaviour on `["strip"]`, the other subcommands left open. -/
def spec (f : StripArgs → Bytes → Except Bytes Bytes) : Spec :=
  WasmTools.tool.spec (bodySpec (cmds f))

end Silmaril.Cli.Spec.WasmTools.Strip
