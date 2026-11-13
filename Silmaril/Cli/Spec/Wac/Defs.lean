module

public import Silmaril.Cli.Clap.Main.Defs

/-!
# The command line of `wasm-wac`

The command line of `wasm-wac` (`tools/wasm-wac/WasmWac.lean`, the front end of
`Silmaril.Wasm.Wac.Tool`; docs/projects/wasm-components.md), as an args grammar in the clap dialect, written from its
usage text and its `main` (2026-11-10):

```
wasm-wac (json|print|pretty) IN.wac [-o OUT]
wasm-wac check IN.wac
wasm-wac targets COMP.wasm --wit WIT.wasm [--world W]
wasm-wac compose IN.wac [--deps DIR] [--dep PKG=PATH]... [-o OUT.wat]
wasm-wac compose IN.wac [--deps DIR] [--dep PKG=PATH]... --wasm [--import-dependencies] -o OUT.wasm
wasm-wac plug SOCKET.wasm --plug P.wasm... [--import-dependencies] [--wac] -o OUT
wasm-wac encode-wit (DIR|FILE.wit) -o OUT.wasm
wasm-wac parse-wat IN.wat -o OUT.wasm
wasm-wac shapes OUT.wasm [--core-dir DIR]
```

`compose` also takes wac's spellings `--deps-dir`, `-d`, `-i` and `--output` (long-name
aliases and single-dash names of the grammar). Rules: `compose --wasm` needs `-o`; `--dep` is
`PKG=PATH` (a value check). Not expressible as a rule yet: `plug` needs `-o` unless `--wac`
(a `required_unless`), so `-o` is optional here and the program refuses `plug` without
`-o` or `--wac` itself (exit 2). The tool reads its arguments
with this grammar (`tool.main`, `Silmaril.Cli.Clap.Main`; `-h` on every command), so it refines
`tool.spec` (`Clap.Tool.main_refines`); `tools/cli-spec/tests/pinned-tools.sh` and
`cli-harness front` check the binary. Before, it parsed by hand (fixed positions, no `-h`,
no `--`).
-/

@[expose] public section

namespace Silmaril.Cli.Spec.Wac

open Silmaril.Cli

/-- `-o OUT`. -/
def outOpt (mv : String := "OUT") (required : Bool := false) : Opt :=
  { id := "-o", long := [], short := ["o"], arg := some .path, metavar := mv, required,
    help := "the output (default: stdout)" }

/-- A text command on a WAC document. -/
def textCmd (name about : String) (out : Bool := true) : Command :=
  { name, about, pos := [{ id := "in", type := .path, metavar := "IN.wac" }],
    opts := if out then [outOpt] else [] }

/-- The exit codes. -/
def exits : List (Nat × String) :=
  [(0, "success (check: every round trip holds)"), (1, "the command failed"),
   (2, "a usage error")]

/-- `wasm-wac`. -/
def extraWac : Command where
  name := "wasm-wac"
  about := "Verified WAC tooling (parse, print, compose, plug)"
  exits := exits
  subs := [
    textCmd "json" "the JSON of `wac parse`, without spans",
    textCmd "print" "the document, one space between tokens",
    textCmd "pretty" "the document, with line breaks",
    textCmd "check" "well-formedness and the print/parse round trip" (out := false),
    { name := "targets", about := "does the component fit the world (by projection)",
      pos := [{ id := "comp", type := .path, metavar := "COMP.wasm" }],
      opts := [{ id := "wit", arg := some .path, metavar := "WIT.wasm", required := true,
                 help := "a WIT package in binary form" },
               { id := "world", arg := some .str, metavar := "W", help := "the world" }] },
    { name := "compose", about := "elaborate, validate and encode the composition",
      pos := [{ id := "in", type := .path, metavar := "IN.wac" }],
      opts := [{ id := "deps", long := ["deps", "deps-dir"], arg := some .path, metavar := "DIR",
                 default := some "deps", help := "the package directory" },
               { id := "dep", short := ["d"], arg := some .str, metavar := "PKG=PATH",
                 repeated := true, help := "a package override" },
               { id := "wasm", help := "a component binary instead of WAT" },
               { id := "import-dependencies", short := ["i"],
                 help := "import the packages instead of embedding them" },
               { outOpt with long := ["output"] }] },
    { name := "plug", about := "plug the plugs' exports into the socket's imports",
      pos := [{ id := "socket", type := .path, metavar := "SOCKET.wasm" }],
      opts := [{ id := "plug", arg := some .path, metavar := "P.wasm", repeated := true,
                 required := true, help := "a plug" },
               { id := "import-dependencies", help := "import the components" },
               { id := "wac", help := "print the WAC document" },
               outOpt] },
    { name := "encode-wit", about := "a WIT package of one or more files",
      pos := [{ id := "src", type := .path, metavar := "DIR|FILE.wit" }],
      opts := [outOpt "OUT.wasm" true] },
    { name := "parse-wat", about := "component WAT with abbreviations to a binary",
      pos := [{ id := "in", type := .path, metavar := "IN.wat" }],
      opts := [outOpt "OUT.wasm" true] },
    { name := "shapes", about := "the packages embedded in a composed binary",
      pos := [{ id := "bin", type := .path, metavar := "OUT.wasm" }],
      opts := [{ id := "core-dir", arg := some .path, metavar := "DIR",
                 help := "write the main core module of each stream package" }] }]

/-- `wasm-wac` in the clap dialect. -/
def tool : Clap.Tool where
  helpSub := false
  grammar := (extraWac.helpEverywhere.withChecks [("dep", .keyValue)]).withRules
    [(["compose"], .requires "wasm" "-o")]

/-- The clap view (help, corpus, the reference reading). -/
def surface : Surface.Command := tool.surface.root

end Silmaril.Cli.Spec.Wac
