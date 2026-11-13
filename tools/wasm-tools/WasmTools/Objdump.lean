import Silmaril.Wasm.Tools.Objdump.Defs
import Silmaril.Wasm.Tools.FastPaths.Defs
import WasmTools.VCommon
import WasmTools.HelpV

/-!
# `wasm-tools objdump`

The CLI wrapper of `Silmaril.Wasm.Tools.Objdump.objdump` (`Thms`: `offsets_spec`). Options as
upstream: `-o`, `--output`, `-v`, `--color`, `[INPUT]`.
-/

namespace WasmTools.Objdump

open Silmaril.Wasm.Tools.OptGrammar WasmTools.VCommon

/-- The options of `objdump`. -/
def specs : List Spec := outputSpecs ++ generalSpecs

def usage : String := "wasm-tools objdump [OPTIONS] [INPUT]"

/-- The body of `objdump` on its record (`run`; the full build: from the specification's
matches, `WasmTools.SpecCore`). -/
def body (a : InOut) : IO UInt32 := do
  let input ← match ← readInput a.input with
    | .error e => return ← fail e
    | .ok b => pure b
  -- `objdumpFast` = `Objdump.objdump` on the bytes (`FastPaths.objdumpFast_eq`)
  match Silmaril.Wasm.Tools.FastPaths.objdumpFast input with
  | .error e => fail e
  | .ok ls =>
    match ← writeText a.output (String.join (ls.map (· ++ "\n"))) with
    | .ok () => return 0
    | .error e => fail e

/-- Run `objdump` on its arguments. -/
def run (args : List String) : IO UInt32 := do
  let p ← match ← parseOrExit specs 1 usage HelpV.objdump_short HelpV.objdump_long args with
    | .error code => return code
    | .ok p => pure p
  body (InOut.ofParsed p)

end WasmTools.Objdump
