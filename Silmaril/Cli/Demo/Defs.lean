module

public import Silmaril.Cli.Args.Defs

@[expose] public section

/-!
# A demo grammar: `demo`, shaped like `wasm-asyncify`

It uses every convention of the dialect: subcommands with an alias, a counted flag (`-vvv`),
a global flag accepted after the subcommand (`-q`), an option with an optional value
(`--color[=WHEN]`), a negatable flag (`--[no-]selective`), short clusters and attached values
(`-qo out.wasm`, `-oout.wasm`), an exact multi-letter token (`-O2`), typed values, a default, an
environment variable, and positionals of several arities.
-/

namespace Silmaril.Cli.Demo

open Silmaril.Cli

/-- The demo command line. -/
def demo : Command :=
  Command.withHelp <| Command.withVersion (v := "0.1.0")
  { name := "demo"
    about := "Instrument and run Wasm modules"
    exits := [(0, "success"), (1, "the tool failed"), (2, "usage error")]
    opts := [flag "verbose" ["v"] "Print more (repeat for more)" |>.counted,
             flag "quiet" ["q"] "Print less" |>.inherited,
             opt "color" (.enum ["auto", "always", "never"]) (help := "Colour output")
               (metavar := "WHEN") |>.optVal]
    subs := [
      { name := "asyncify"
        about := "Run the verified pass"
        opts := [opt "output" .path ["o"] "Output file" |>.req,
                 opt "pages" .nat (help := "Memory pages") |>.withDefault "1",
                 flag "selective" (help := "Instrument only suspending calls") |>.withNo,
                 { id := "O2", long := [], short := ["O2"], help := "Optimise first" }]
        pos := [arg "input" .path (help := "Input module")] },
      { name := "run"
        aliases := ["r"]
        about := "Run an export"
        opts := [opt "fuel" .nat (help := "Fuel") |>.withDefault "1000000" |>.withEnv "DEMO_FUEL",
                 opt "side" (.enum ["src", "tgt"]) (help := "Model") |>.withDefault "src"]
        pos := [arg "input" .path, arg "export", arg "args" .nat .many] }] }

/-! ## Fragments of real command lines -/

/-- A fragment of Binaryen's `wasm-opt`: exact multi-letter tokens (`-O2`, `-Oz`, `-all`), a
one-letter output option and a flag that cluster (`-go out.wasm`), repeatable stages. -/
def wasmOpt : Command :=
  Command.withHelp
  { name := "wasm-opt"
    opts := [opt "output" .path ["o"] "Output file",
             flag "debuginfo" ["g"] "Keep names",
             { id := "all-features", short := ["all"], help := "Enable all features" },
             { id := "O2", long := [], short := ["O2"], help := "Optimise", repeated := true },
             { id := "Oz", long := [], short := ["Oz"], help := "Optimise for size",
               repeated := true },
             opt "passes" (help := "Run these passes") |>.many,
             flag "vacuum" (help := "Remove obviously unneeded code") |>.many]
    pos := [arg "input" .path (help := "Input module, - for stdin")] }

/-- A fragment of `wasm-tools`: per-subcommand counted `-v`, a clustered flag and output
(`-to out.wat`), an optional value (`--merge-imports-based-on-semver[=true|false]`). -/
def wasmTools : Command :=
  Command.withHelp <| Command.withVersion (v := "1.262.0")
  { name := "wasm-tools"
    subs := [
      { name := "parse"
        opts := [flag "verbose" ["v"] "More output" |>.counted,
                 opt "output" .path ["o"] "Where to place output",
                 flag "wat" ["t"] "Output the text format"]
        pos := [arg "input" .path .optional] },
      { name := "component"
        subs := [
          { name := "new"
            opts := [opt "output" .path ["o"],
                     opt "merge-imports-based-on-semver" (.enum ["true", "false"])
                       (metavar := "MERGE") |>.optVal]
            pos := [arg "input" .path .optional] }] }] }

end Silmaril.Cli.Demo
