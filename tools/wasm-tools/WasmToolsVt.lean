import WasmTools.Validate
import WasmTools.CompRoute

/-!
# `wasm-tools-vt`: the validate track's subcommands as a standalone binary

`wasm-tools-vt <SUBCOMMAND> ARGS…` runs the subcommand of `WasmTools.Validate.table` exactly as
`wasm-tools <SUBCOMMAND> ARGS…` does once the table is in the main dispatch
(`tools/wasm-tools/WasmTools.lean`); the tests in `tools/wasm-tools/tests` run it (or the binary
named by `WASM_TOOLS_OURS`).
-/

def main (args : List String) : IO UInt32 := do
  WasmTools.CompRoute.install
  match args with
  | cmd :: rest =>
    match WasmTools.Validate.table.find? (·.name == cmd) with
    | some c => c.run rest
    | none =>
      IO.eprintln s!"error: unrecognized subcommand '{cmd}'"
      return 2
  | [] =>
    IO.eprintln "usage: wasm-tools-vt <validate|strip|objdump> [ARGS]..."
    return 2
