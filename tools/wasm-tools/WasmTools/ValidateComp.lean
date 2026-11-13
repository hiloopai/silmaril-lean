import Silmaril.Wasm.Tools.Validate.Defs
import Silmaril.Wasm.Tools.CompValidate.Defs
import Silmaril.Wasm.Tools.FastPaths.Defs
import WasmTools.VCommon
import WasmTools.CompVal

/-!
# `wasm-tools validate` with the component path (the full build)

The CLI wrapper of `Silmaril.Wasm.Tools.Validate.check` (correctness: `check_ok_iff`,
`check_sound`, `check_complete`) for core modules, and of the compval track's
`WasmTools.CompVal.validateOn` for components. Options as upstream (read by the specification, `CompVal.ValidateArgs.ofMatches`):
`--generate-dwarf <lines|full>`, `-g`, `-f`, `--features` (repeatable;
`Silmaril.Wasm.Tools.Features.parseFeatures`, `applyActions` for core modules), `-v`, `--verbose`,
`--color`, `--validate-custom`, `[INPUT]`. `WasmTools.CompRoute.install` makes it the
`validate` of the full build (`WasmTools.ValidateCmd.run`).
-/

namespace WasmTools.ValidateComp

open Silmaril.Wasm.Tools.Features WasmTools.VCommon

/-- Run `validate` on its record (`CompVal.ValidateArgs.ofMatches`: help, usage errors and the
`--features` values are the specification's); the input is read once. A component (`CompVal.isComponentInput`: a component
binary, or text starting with `(component`) goes to the component validator
(`CompVal.validateOn`); every other input to the core path below. -/
def run (a : CompVal.ValidateArgs) : IO UInt32 := do
  let cflags ← match CompVal.featuresOf a.features with
    | .error m => return ← CompVal.fail m 2
    | .ok f => pure f
  match ← CompVal.readInput a.input with
  | .error e => CompVal.fail s!"error: {e}\n"
  | .ok raw =>
    if CompVal.isComponentInput raw then return ← CompVal.validateOn cflags raw
    -- the core feature set (every value parsed by `CompVal.validateArgs` already)
    let mut acts : List Action := []
    for v in a.features do
      match parseFeatures v with
      | .ok a => acts := acts ++ a
      | .error e =>
        IO.eprintln s!"error: invalid value '{v}' for '--features <FEATURES>': {e}"
        IO.eprintln ""
        IO.eprintln "For more information, try '--help'."
        return 2
    let F := applyActions acts
    match toBinary raw with
    | .error e => fail e
    | .ok bytes =>
      if bytes.size ≥ 8 && bytes[4]! == 0x0d && bytes[6]! == 0x01 then
        return ← match Silmaril.Wasm.Tools.CompValidate.check F bytes with
          | .ok () => pure 0
          | .error e => fail e
      -- `checkFast` = `Validate.check` (`FastPaths.checkFast_eq`)
      match Silmaril.Wasm.Tools.FastPaths.checkFast F bytes with
      | .ok () => return 0
      | .error e => fail e.message

end WasmTools.ValidateComp
