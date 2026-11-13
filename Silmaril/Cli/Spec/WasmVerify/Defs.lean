module

public import Silmaril.Cli.Clap.Defs

/-!
# The command line of `wasm-verify`

The command line of `wasm-verify` (`tools/wasm-verify/WasmVerify.lean`;
docs/projects/wasm-components.md), the checker of the Binaryen toolkit:

```
wasm-verify FILE.wasm (never-call|assert-never-false) IMPORT
wasm-verify FILE.wasm never-call-from IMPORT EXPORT
wasm-verify FILE.wasm (imports|exports)
```

The command word comes after the file, so it is a positional with choices; how many
arguments follow depends on it (1, 2 or 0), which the grammar records only as two optional
positionals. The camelCase spellings (`neverCall`, `assertNeverFalse`, `neverCallFrom`) are
accepted too.
-/

@[expose] public section

namespace Silmaril.Cli.Spec.WasmVerify

open Silmaril.Cli

/-- The command words. -/
def commands : List String :=
  ["never-call", "assert-never-false", "never-call-from", "imports", "exports",
   "neverCall", "assertNeverFalse", "neverCallFrom"]

/-- The exit codes. -/
def exits : List (Nat × String) :=
  [(0, "a report was printed (whatever the verdict)"), (2, "a usage, input or decoding error")]

/-- `wasm-verify`. -/
def extraWasmVerify : Command where
  name := "wasm-verify"
  about := "Run the verified checker on a Core module and print its JSON report"
  exits := exits
  pos := [
    { id := "file", type := .path, metavar := "FILE.wasm", help := "a Core 3.0 binary module" },
    { id := "command", type := .enum commands },
    { id := "import", arity := .optional, help := "an import index or module.name" },
    { id := "export", arity := .optional,
      help := "an index into the function exports, or an export name" }]

/-- `wasm-verify` in the clap dialect. -/
def tool : Clap.Tool := { grammar := extraWasmVerify }

/-- The clap view (help, corpus, the reference reading). -/
def surface : Surface.Command := tool.surface.root

end Silmaril.Cli.Spec.WasmVerify
