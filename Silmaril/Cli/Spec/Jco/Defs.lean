module

public import Silmaril.Cli.Clap.Main.Defs

/-!
# The command line of `wasm-jco`

The command line of `wasm-jco` (`tools/wasm-jco/WasmJco.lean`, the jco/`wasm-tools
component` style front end of `Silmaril.Wasm.JcoTool`; docs/projects/wasm-components.md), as an args
grammar in the clap dialect, written from its usage text and its `main` (2026-11-10):

```
wasm-jco new CORE.wasm [--wit SRC --world W] [--adaptor [--alloc NAME]] [--lime] -o OUT.wasm
wasm-jco new CORE.wasm --adapt NAME=ADAPTER.wasm [--adapt …] [--wit SRC --world W] -o OUT.wasm
wasm-jco new CORE.wasm --ref [--wit SRC --world W] -o OUT.wasm
wasm-jco component wit COMP.wasm [-o OUT.wit]
wasm-jco [component] embed WIT CORE.wasm [--world W] [--encoding utf8|utf16|compact-utf16] -o OUT.wasm
wasm-jco component new …   (= new)
wasm-jco print COMP.wasm
wasm-jco validate COMP.wasm
wasm-jco kcore NAME KERNEL N [--baseline] [--canonical | --printer | -o OUT.wasm]
```

The alternatives of the usage text are `rules`: `--wit` and `--world` go together, `--alloc`
needs `--adaptor`, `--ref` excludes `--adaptor`, `--lime` and `--adapt`, `--adapt` excludes
`--adaptor` and `--lime`, and the three outputs of `kcore` exclude each other. The kernel and
`N` of `kcore` are checked by the program (an unknown kernel or a bad `N` is a failure, exit 1),
so they are strings here. The tool reads its arguments with
this grammar (`tool.main`, `Silmaril.Cli.Clap.Main`; `-h` on every command), so it refines
`tool.spec` (`Clap.Tool.main_refines`); `tools/cli-spec/tests/pinned-tools.sh` and
`cli-harness front` check the binary. Before, it parsed by hand (the input right after the
subcommand, unknown options ignored, no `-h`, no `--`).
-/

@[expose] public section

namespace Silmaril.Cli.Spec.Jco

open Silmaril.Cli

/-- `-o OUT`, required. -/
def outReq (mv : String := "OUT.wasm") : Opt :=
  { id := "-o", long := [], short := ["o"], arg := some .path, metavar := mv, required := true,
    help := "the output" }

/-- The options of `new`. -/
def newOpts : List Opt :=
  [{ id := "wit", arg := some .path, metavar := "SRC",
     help := "a WIT file, or a directory with one .wit file (and deps/)" },
   { id := "world", arg := some .str, metavar := "W", help := "the world of --wit" },
   { id := "adaptor", help := "the adaptor layout" },
   { id := "alloc", arg := some .str, metavar := "NAME", default := some "alloc",
     help := "the allocator export of --adaptor" },
   { id := "lime", help := "the lime layout" },
   { id := "adapt", arg := some .str, metavar := "NAME=ADAPTER.wasm", repeated := true,
     help := "an adapter module (the name defaults to the file name's stem)" },
   { id := "ref", help := "the reference layouts" },
   { id := "realloc-via-memory-grow", help := "with --adapt: realloc by memory.grow" },
   outReq]

/-- `new` (and `component new`). -/
def newCmd : Command where
  name := "new"
  about := "a component from a core module"
  pos := [{ id := "core", type := .path, metavar := "CORE.wasm" }]
  opts := newOpts

/-- `embed` (and `component embed`). -/
def embedCmd : Command where
  name := "embed"
  about := "embed a WIT world in a core module"
  pos := [{ id := "wit", type := .path, metavar := "WIT" },
          { id := "core", type := .path, metavar := "CORE.wasm" }]
  opts := [{ id := "world", arg := some .str, metavar := "W", help := "the world (default: the only one)" },
           { id := "encoding", arg := some (.enum ["utf8", "utf16", "compact-utf16"]),
             metavar := "E", default := some "utf8", help := "the string encoding" },
           outReq]

/-- The exit codes. -/
def exits : List (Nat × String) :=
  [(0, "success"), (1, "the command failed"), (2, "a usage error")]

/-- `wasm-jco`. -/
def extraJco : Command where
  name := "wasm-jco"
  about := "Verified component tooling in the style of jco and wasm-tools component"
  exits := exits
  subs := [
    newCmd,
    { name := "component", about := "the wasm-tools component spellings",
      subs := [newCmd,
        { name := "wit", about := "the WIT of a component",
          pos := [{ id := "comp", type := .path, metavar := "COMP.wasm" }],
          opts := [{ outReq "OUT.wit" with required := false }] },
        embedCmd] },
    embedCmd,
    { name := "print", about := "component WAT (verified grammar only)",
      pos := [{ id := "comp", type := .path, metavar := "COMP.wasm" }] },
    { name := "validate", about := "the verified parser, the IR reader and the reference validator",
      pos := [{ id := "comp", type := .path, metavar := "COMP.wasm" }] },
    { name := "kcore", about := "the core module generated from a byte kernel",
      pos := [{ id := "name" }, { id := "kernel" }, { id := "n", metavar := "N" }],
      opts := [{ id := "baseline", help := "round 1's generator" },
               { id := "canonical", help := "the WAT of the proved printer (the default)" },
               { id := "printer", help := "the text of Prog.wat, checked per output" },
               { outReq with required := false, help := "the bytes" }] }]

/-- The relations of the usage text. -/
def newRules (p : List String) : List (List String × Rule) :=
  [(p, .requires "wit" "world"), (p, .requires "world" "wit"), (p, .requires "alloc" "adaptor"),
   (p, .conflicts "ref" "adaptor"), (p, .conflicts "ref" "lime"), (p, .conflicts "ref" "adapt"),
   (p, .conflicts "adapt" "adaptor"), (p, .conflicts "adapt" "lime")]

/-- `wasm-jco` in the clap dialect. -/
def tool : Clap.Tool where
  helpSub := false
  grammar := extraJco.helpEverywhere.withRules (newRules ["new"] ++ newRules ["component", "new"] ++
    [(["kcore"], .conflicts "canonical" "printer"), (["kcore"], .conflicts "canonical" "-o"),
     (["kcore"], .conflicts "printer" "-o")])

/-- The clap view (help, corpus, the reference reading). -/
def surface : Surface.Command := tool.surface.root

end Silmaril.Cli.Spec.Jco
