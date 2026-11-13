import Silmaril.Wasm.Tools.Dump.Defs
import WasmTools.VCommon
import WasmTools.HelpV

/-!
# `wasm-tools dump`

The CLI wrapper of `Silmaril.Wasm.Tools.Dump.dump` (the walker; its operators come from
`DumpOps.dExpr`, the certified decoder with a log: `DumpOps.Thms.dExpr_erase`). Options as
upstream: `-o`, `--output`, `-v`, `--color`, `[INPUT]`. Colours as `wasm_tools::OutputArg`:
on stdout for `--color always`/`always-ansi`, and for `auto` on a terminal; in a `-o` file only
for `always-ansi`. What was printed before an error is written, then `error: …` (status 1).
The text is `Dump.dump`'s, written line by line (the same characters; less memory).
-/

namespace WasmTools.Dump

open Silmaril.Wasm.Tools.OptGrammar WasmTools.VCommon

def specs : List Spec := outputSpecs ++ generalSpecs

def usage : String := "wasm-tools dump [OPTIONS] [INPUT]"

/-- The body of `dump` on its record (`run`; the full build: from the specification's
matches, `WasmTools.SpecCore`). -/
def body (a : InOut) : IO UInt32 := do
  let input ← match ← readInput a.input with
    | .error e => return ← fail e
    | .ok b => pure b
  let colorArg := a.color
  let out := a.output
  let color ← match out with
    | some _ => pure (colorArg == "always-ansi")
    | none =>
      if colorArg == "auto" then (← IO.getStdout).isTty
      else pure (colorArg == "always" || colorArg == "always-ansi")
  let (ls, err) := Silmaril.Wasm.Tools.Dump.dumpLines input
  let w := Silmaril.Wasm.Tools.Dump.width input
  -- the text of `Dump.dump input color`, written in chunks rather than built whole
  let emit (h : IO.FS.Stream) : IO Unit := do
    let mut buf := ""
    for l in ls do
      buf := buf ++ Silmaril.Wasm.Tools.Dump.renderLine input w color l
      if buf.utf8ByteSize > 65536 then
        h.putStr buf; buf := ""
    h.putStr buf
    h.flush
  let wrote ← match out with
    | some path =>
      match ← (IO.FS.Handle.mk path .write).toBaseIO with
      | .ok h => do emit (IO.FS.Stream.ofHandle h); pure true
      | .error _ => pure false
    | none => do emit (← IO.getStdout); pure true
  unless wrote do return ← fail s!"failed to create `{out.getD ""}`"
  match err with
  | some e => fail e
  | none => return 0

/-- Run `dump` on its arguments. -/
def run (args : List String) : IO UInt32 := do
  let p ← match ← parseOrExit specs 1 usage HelpV.dump_short HelpV.dump_long args with
    | .error code => return code
    | .ok p => pure p
  body (InOut.ofParsed p)

end WasmTools.Dump
