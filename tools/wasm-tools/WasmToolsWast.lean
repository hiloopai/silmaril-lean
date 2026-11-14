import WasmTools.Wast

/-!
# `wasm-tools-wast`: the `json-from-wast` and `wast` subcommands alone

A stand-in executable for testing the wast track before the main `wasm-tools` dispatcher
(`WasmTools.lean`, owned by the CLI track) imports `WasmTools.Wast.subcommands`:
`wasm-tools-wast json-from-wast …` behaves as `wasm-tools json-from-wast …`.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | cmd :: rest =>
    match WasmTools.Wast.subcommands.find? (·.1 == cmd) with
    | some (_, run) => run rest
    | none =>
      IO.eprintln s!"error: unrecognized subcommand '{cmd}'"
      return 2
  | [] =>
    IO.eprintln "usage: wasm-tools-wast <json-from-wast|wast> ..."
    return 2
