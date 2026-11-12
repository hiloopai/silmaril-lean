import Silmaril.Wasm.Tools.Validate.Defs
import Silmaril.Wasm.Tools.CompValidate.Defs
import Silmaril.Wasm.Tools.FastPaths.Defs
import WasmTools.VCommon
import WasmTools.HelpV
import WasmTools.CompHook

/-!
# `wasm-tools validate`

The CLI wrapper of `Silmaril.Wasm.Tools.Validate.check` (correctness: `check_ok_iff`,
`check_sound`, `check_complete`). Options as upstream: `--generate-dwarf <lines|full>`, `-g`,
`-f`, `--features` (repeatable; `Silmaril.Wasm.Tools.Features.parseFeatures`, `applyActions`),
`-v`, `--verbose`, `--color`, `--validate-custom`, `[INPUT]`.

In the full build, `run` is the component-aware `WasmTools.ValidateComp.run`
(`WasmTools.CompHook`, set by `WasmTools.CompRoute.install`); in the core build it is
`runCore` below.
-/

namespace WasmTools.ValidateCmd

open Silmaril.Wasm.Tools.OptGrammar Silmaril.Wasm.Tools.Features WasmTools.VCommon

/-- The options of `validate`. -/
def specs : List Spec :=
  [{ long := "generate-dwarf", kind := .single, valueName := "lines|full" },
   { long := "generate-full-dwarf", short := some 'g', kind := .flag, hasLong := false },
   { long := "features", short := some 'f', kind := .multi, valueName := "FEATURES" },
   { long := "validate-custom", kind := .flag }] ++ generalSpecs

def usage : String := "wasm-tools validate [OPTIONS] [INPUT]"

/-- Run `validate` on its arguments (the core build: no component path). -/
def runCore (args : List String) : IO UInt32 := do
  let p ← match ← parseOrExit specs 1 usage HelpV.validate_short HelpV.validate_long args with
    | .error code => return code
    | .ok p => pure p
  -- `-g` conflicts with `--generate-dwarf`
  if p.flag "generate-full-dwarf" && (p.value? "generate-dwarf").isSome then
    return ← usageError "wasm-tools validate -g <INPUT>"
      "error: the argument '-g' cannot be used with '--generate-dwarf <lines|full>'"
  if let some g := p.value? "generate-dwarf" then
    unless g == "lines" || g == "full" do
      IO.eprintln s!"error: invalid value '{g}' for '--generate-dwarf <lines|full>': unknown \
        `--generate-dwarf` setting: {g}"
      IO.eprintln ""
      IO.eprintln "For more information, try '--help'."
      return 2
  -- every `--features` argument is parsed (clap's value parser) before running
  let mut acts : List Action := []
  for v in p.values "features" do
    match parseFeatures v with
    | .ok a => acts := acts ++ a
    | .error e =>
      IO.eprintln s!"error: invalid value '{v}' for '--features <FEATURES>': {e}"
      IO.eprintln ""
      IO.eprintln "For more information, try '--help'."
      return 2
  let F := applyActions acts
  match ← readInput p.pos.head? with
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

/-- Run `validate` on its arguments: the build's component path if it has one
(`WasmTools.CompHook.hooks`), else `runCore`. -/
def run (args : List String) : IO UInt32 := do
  match ← CompHook.hooks.get with
  | some h => h.validate args
  | none => runCore args

end WasmTools.ValidateCmd
