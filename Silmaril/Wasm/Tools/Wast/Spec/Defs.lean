module

public import Silmaril.Wasm.Tools.Wast.Cli.Defs
public import Silmaril.Cli.Spec.WasmTools.Defs

/-!
# `json-from-wast` and `wast` on the CLI specification's matches

The records of the two subcommands (`Silmaril.Wasm.Tools.Wast.Cli.JsonOpts`, `WastOpts`) built
from the matches of `Silmaril.Cli.Spec.WasmTools.tool` at `["json-from-wast"]` and `["wast"]`: the
full build of `wasm-tools` runs the bodies on these (`tools/wasm-tools/WasmTools/SpecCore.lean`);
the core build (the first release) on `Wast.Cli.jsonOpts?`/`wastOpts?`, its own reader, kept as
that release's variant.

**Agreement, open** (`Task.jsonOpts_agree`, `Task.wastOpts_agree`): on a command line both
readers accept, both give the body the same record. Checked on the derived corpus, the texts
vectors and the golden suites by `tools/wasm-tools/tests/args-agree.sh` (0 differences); not
proved. Nothing depends on them.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast.Spec

open Silmaril.Cli Silmaril.Wasm.Tools.Wast.Cli

/-- **The record of a `json-from-wast` run**, from the specification's matches. -/
def jsonOfMatches (m : Matches) : JsonOpts where
  wast := (m.str? "wast").getD ""
  output := m.str? "output"
  wasmDir := m.str? "wasm-dir"
  pretty := m.flag "pretty"
  allowConfusingUnicode := (m.str? "allow-confusing-unicode").map (· == "true")

/-- **The record of a `wast` run**, from the specification's matches (`--assert` is a
comma-separated list). -/
def wastOfMatches (m : Matches) : WastOpts where
  input := m.str? "input"
  ignoreErrorMessages := m.flag "ignore-error-messages"
  features := m.strs "features"
  allowConfusingUnicode := m.flag "allow-confusing-unicode"
  asserts := (m.strs "assert").flatMap (·.splitOn ",")
  snapshot := m.str? "snapshot"

/-- Open: where the first release's reader and the specification both accept a
`json-from-wast` command line, they give the body the same record. -/
def Task.jsonOpts_agree : Prop :=
  ∀ (args : List String) (o : JsonOpts) (fs : Invocation) (m : Matches),
    jsonOpts? args = .run o →
    Silmaril.Cli.Spec.WasmTools.tool.read (fun _ => none) ("json-from-wast" :: args) = .run fs m →
    jsonOfMatches m = o

/-- Open: the same for `wast`. -/
def Task.wastOpts_agree : Prop :=
  ∀ (args : List String) (o : WastOpts) (fs : Invocation) (m : Matches),
    wastOpts? args = .run o →
    Silmaril.Cli.Spec.WasmTools.tool.read (fun _ => none) ("wast" :: args) = .run fs m →
    wastOfMatches m = o

end Silmaril.Wasm.Tools.Wast.Spec
