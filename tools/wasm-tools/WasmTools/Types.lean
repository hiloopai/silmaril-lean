/-!
# The subcommand table type of `wasm-tools`

Each group of subcommands (`WasmTools.Core`, `WasmTools.Component`, `WasmTools.Gen`, …)
exports a `List Subcommand`. The main entry (`WasmTools.lean`) dispatches on the first
argument: the first table entry whose `name` equals it runs with the remaining arguments.
`run` returns the process exit status; upstream's conventions are 0 for success, 1 for a
failure of the command and 2 for a usage error (see `tools/wasm-tools/README.md`).
-/

namespace WasmTools

/-- One top-level subcommand: its name (as typed on the command line, e.g. `parse` or
`component`) and its action on the arguments that follow the name. -/
structure Subcommand where
  name : String
  run : List String → IO UInt32

end WasmTools
