import Silmaril.Wasm.Tools.Meta.Main.Defs

/-!
# `wasm-tools-meta`: the meta track's subcommands on their own

A test driver for the subcommands of `WasmTools.Meta` (`demangle`, `metadata`, `addr2line`)
before they are dispatched from the `wasm-tools` main entry: `wasm-tools-meta SUBCOMMAND ARGS…`
behaves as `wasm-tools SUBCOMMAND ARGS…`. Also `wasm-tools-meta x-demangle-symbols` reads
symbols, one per line, from stdin and prints `demangleName` of each (for the demangler corpus
tests).
-/

open WasmTools.Meta

def main (args : List String) : IO UInt32 := do
  match args with
  | "x-demangle-symbols" :: _ =>
    let stdin ← IO.getStdin
    let out ← IO.getStdout
    let mut line ← stdin.getLine
    while !line.isEmpty do
      let sym := String.ofList (line.toList.filter (· != '\n'))
      let r := Silmaril.Wasm.Tools.Meta.Demangle.demangleName sym.toUTF8.toList
      out.putStrLn (String.fromUTF8! (ByteArray.mk r.toArray))
      line ← stdin.getLine
    pure 0
  | cmd :: rest =>
    match (subcommands {}).lookup cmd with
    | some f => f rest
    | none => (← IO.getStderr).putStrLn s!"wasm-tools-meta: unknown subcommand {cmd}"; pure 2
  | [] => (← IO.getStderr).putStrLn "usage: wasm-tools-meta SUBCOMMAND ARGS..."; pure 2
