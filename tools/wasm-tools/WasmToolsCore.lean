-- First import: the release manifest's checker follows `Silmaril.*` imports of the entry
-- point to its runtime root (`Wasm.Tools.Validate.Defs`).
import Silmaril.Wasm.Tools.Validate.Defs
import WasmTools.Top
import WasmTools.Core
import WasmTools.Validate
import WasmTools.Meta
import WasmTools.Wast

/-!
# `wasm-tools-core`: the core build of `wasm-tools`

The same top level as `wasm-tools` (`WasmTools.run`) over the core tables only: `parse`,
`print`, `validate`, `strip`, `objdump`, `dump`, `metadata`, `demangle`, `addr2line`,
`completion`, `json-from-wast` and `wast`. `component`, `compose` and the generators report
`not implemented in this build` (exit 1), as every other subcommand of upstream that no
table implements. `validate`, `print` and `parse` have no component path here
(`WasmTools.CompHook`): component binaries are validated by `Silmaril.Wasm.Tools.CompValidate`,
and component text is not read. This is the first open-source release's `wasm-tools`.
-/

namespace WasmTools

/-- The core tables, in the dispatch order of the full build. -/
def coreCommands : List Subcommand :=
  Core.table ++ Validate.table ++ Meta.table ++ Wast.table

end WasmTools

def main (args : List String) : IO UInt32 :=
  WasmTools.run WasmTools.coreCommands args
