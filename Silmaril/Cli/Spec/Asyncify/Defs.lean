module

public import Silmaril.Cli.Clap.Main.Defs

/-!
# The command line of `wasm-asyncify`

The command line of `wasm-asyncify` (`tools/wasm-asyncify/WasmAsyncify.lean`, front end of
`Silmaril.Wasm.FX.Asyncify.Tool`; docs/projects/wasm-binaryen-tooling.md). The
tool reads its arguments with this grammar: its `main` is `tool.main` (`Silmaril.Cli.Clap.Main`)
on a dispatch over the matches, so its help, usage errors and exit codes are the derived ones
and it refines `tool.spec` (`Clap.Tool.main_refines`); the differential
tests and `cli-harness front` check the binary against it (docs/projects/wasm-binaryen-tooling.md).
An earlier version parsed by hand (laxer: extra arguments ignored, `-o` found anywhere,
a non-numeric `--pages` replaced by the default; no `-h`; usage errors exit 1).
-/

@[expose] public section

namespace Silmaril.Cli.Spec.Asyncify

open Silmaril.Cli

/-- `-o OUT.wasm`, required. -/
def outOpt : Opt :=
  { id := "-o", long := [], short := ["o"], arg := some .path, metavar := "OUT.wasm",
    required := true, help := "the output" }

/-- `--fuel N`. -/
def fuelOpt : Opt :=
  { id := "fuel", arg := some .nat, metavar := "N", default := some "1000000",
    help := "the step budget of the run" }

/-- The arguments of `run-src` and `run-tgt`. -/
def runPos : List Pos :=
  [{ id := "in", type := .path, metavar := "IN.wasm", help := "a Core module" },
   { id := "export", help := "the export to call" },
   { id := "args", help := "comma-separated unsigned 32-bit numbers (possibly empty: \"\")" }]

/-- The exit codes. -/
def exits : List (Nat × String) :=
  [(0, "success"), (1, "the command failed"), (2, "a usage error")]

/-- `wasm-asyncify`. -/
def extraAsyncify : Command where
  name := "wasm-asyncify"
  about := "The verified asyncify pass and its source and target models"
  exits := exits
  subs := [
    { name := "asyncify", about := "the verified pass on a binary",
      pos := [{ id := "in", type := .path, metavar := "IN.wasm", help := "a Core module" }],
      opts := [outOpt,
        { id := "pages", arg := some .nat, metavar := "N", default := some "1",
          help := "pages of the asyncify data region" },
        { id := "no-elide", help := "the guarded pass, statement form only" },
        { id := "selective", help := "instrument only calls that may suspend" }] },
    { name := "run-src", about := "run the source model on the test host", pos := runPos,
      opts := [fuelOpt] },
    { name := "run-tgt", about := "run the target model on the test host", pos := runPos,
      opts := [fuelOpt] },
    { name := "example", about := "write a built-in example module",
      pos := [{ id := "name" }], opts := [outOpt] },
    { name := "examples", about := "list the examples" }]

/-- `wasm-asyncify` in the clap dialect: `-h` on every command, no `help` subcommand. -/
def tool : Clap.Tool where
  grammar := extraAsyncify.helpEverywhere
  helpSub := false

/-- The clap view (help, corpus, the reference reading). -/
def surface : Surface.Command := tool.surface.root

end Silmaril.Cli.Spec.Asyncify
