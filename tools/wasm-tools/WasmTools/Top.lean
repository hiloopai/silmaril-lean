import WasmTools.Types
import Silmaril.Wasm.Tools.Suggest.Defs

/-!
# The top level of `wasm-tools`, shared by its builds

The help, version, alias and unknown-subcommand behaviour of upstream's clap front end
(wasm-tools 1.262.0), and `run`, which dispatches to the first subcommand of a list of
tables. `WasmTools.lean` (every table) and `WasmToolsCore.lean` (the core tables: no
`component`, `compose` or generators) are the two builds; a subcommand of upstream that the
build's tables lack reports `not implemented in this build` (exit 1).

Top-level behaviour (as clap does for upstream):

* no arguments: the help on stderr, exit 2;
* `-h`, `--help`, `help`: the help on stdout, exit 0;
* `-V`, `--version`: the version line on stdout, exit 0;
* an unknown subcommand: an `error:` message on stderr, with clap's tip naming the similar
  subcommands (`similarTip`), exit 2;
* a subcommand of upstream that no table implements: an `error:` message on stderr, exit 1.
-/

namespace WasmTools

/-- Upstream's top-level help (`wasm-tools --help`, 1.262.0), verbatim. -/
def topHelp : String := "Usage: wasm-tools <COMMAND>\n\nCommands:\n  parse           Parse the WebAssembly text format\n  validate        Validate a WebAssembly binary\n  print           Print the textual form of a WebAssembly binary\n  smith           A WebAssembly test case generator\n  shrink          Shrink a Wasm file while maintaining a property of interest (such as triggering a\n                  compiler bug)\n  mutate          A WebAssembly test case mutator\n  dump            Debugging utility to dump information about a wasm binary\n  objdump         Dumps information about sections in a WebAssembly file\n  strip           Removes custom sections from an input WebAssembly file\n  compose         WebAssembly component composer\n  demangle        Demangle Rust and C++ symbol names in the `name` section\n  component       WebAssembly wit-based component tooling\n  metadata        Manipulate metadata (module name, producers) to a WebAssembly file\n  wit-smith       A WIT test case generator\n  wit-dylib       Generate a wasm dynamic library from the input WIT world\n  addr2line       Translate a WebAssembly address to a filename and line number using DWARF\n                  debugging information\n  completion      Generate shell completion scripts for this CLI\n  json-from-wast  Convert a `*.wast` WebAssembly spec test into a `*.json` file and `*.wasm` files\n  wast            A subcommand to test `*.wast` files short of executing WebAssembly code\n  help            Print this message or the help of the given subcommand(s)\n\nOptions:\n  -h, --help     Print help\n  -V, --version  Print version\n"

/-- The version line. Upstream prints `wasm-tools 1.262.0 (e22db44da 2026-10-13)`; this
binary names itself instead of upstream's commit. -/
def versionLine : String := "wasm-tools 1.262.0 (lean)\n"

/-- The subcommands of upstream 1.262.0, in the order of its help. -/
def upstreamCommands : List String :=
  ["parse", "validate", "print", "smith", "shrink", "mutate", "dump", "objdump", "strip",
   "compose", "demangle", "component", "metadata", "wit-smith", "wit-dylib", "addr2line",
   "completion", "json-from-wast", "wast", "help"]

/-- clap's subcommand aliases of upstream (`#[command(alias = …)]` in `main.rs`). -/
def aliases : List (String × String) :=
  [("wat2wasm", "parse"), ("wasm2wat", "print"), ("wast2json", "json-from-wast")]

/-- `all_subcommand_names`: each subcommand followed by its aliases, `help` last. -/
def subcommandNames : List String :=
  upstreamCommands.flatMap fun c => c :: (aliases.filter (·.2 == c)).map (·.1)

/-- The implemented subcommands that have subcommands of their own (`metadata show`, …). -/
def nestedCommands : List String := ["metadata"]

/-- The subcommand an alias stands for. -/
def resolveAlias (a : String) : String := ((aliases.find? (·.1 == a)).map (·.2)).getD a

/-- clap's tip for an unknown subcommand: every subcommand of upstream (`help` last) above
the similarity threshold, most similar last (`Suggest.didYouMeanAll`). -/
def similarTip (s : String) : String :=
  match Silmaril.Wasm.Tools.Suggest.didYouMeanAll s subcommandNames with
  | [] => ""
  | [c] => s!"  tip: a similar subcommand exists: '{c}'\n\n"
  | cs => "  tip: some similar subcommands exist: " ++
      ", ".intercalate (cs.map fun c => s!"'{c}'") ++ "\n\n"

/-- The usage error clap prints for an unknown subcommand; `tip` adds the similar-subcommand
tip (clap gives none for `help NAME`). -/
def unknownSubcommand (s : String) (tip : Bool := true) : String :=
  s!"error: unrecognized subcommand '{s}'\n\n" ++ (if tip then similarTip s else "") ++
    "Usage: wasm-tools <COMMAND>\n\nFor more information, try '--help'.\n"

/-- The `main` of a build whose subcommands are `commands` (the tables in dispatch order). -/
def run (commands : List Subcommand) (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match args with
  | [] => err.putStr topHelp; return 2
  | a :: rest =>
    if a == "-h" || a == "--help" || (a == "help" && rest.isEmpty) then
      out.putStr topHelp; return 0
    if a == "-V" || a == "--version" then
      out.putStr versionLine; return 0
    -- `help CMD` is `CMD --help`
    let viaHelp := a == "help"
    -- `help CMD SUB…` of a command with subcommands is `CMD help SUB…` (clap)
    let (a, rest) := if viaHelp then
        match rest with
        | c :: sub@(_ :: _) => if nestedCommands.contains (resolveAlias c) then (c, "help" :: sub)
            else (c, ["--help"])
        | _ => (rest.headD "", ["--help"])
      else (a, rest)
    let a := resolveAlias a
    match commands.find? (·.name == a) with
    | some c => c.run rest
    | none =>
      if upstreamCommands.contains a then
        err.putStr s!"error: wasm-tools {a}: not implemented in this build\n"
        return 1
      err.putStr (unknownSubcommand a (tip := !viaHelp)); return 2

end WasmTools
