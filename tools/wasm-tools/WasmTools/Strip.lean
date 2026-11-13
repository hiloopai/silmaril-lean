import Silmaril.Wasm.Tools.Strip.Defs
import Silmaril.Wasm.Tools.FastPaths.Defs
import Silmaril.Wasm.Tools.Regex.Defs
import Silmaril.Wasm.Tools.Text.Defs
import WasmTools.VCommon
import WasmTools.HelpV

/-!
# `wasm-tools strip`

The CLI wrapper of `Silmaril.Wasm.Tools.Strip.strip` (`Thms`: `strip_module`,
`strip_module_frames`, `strip_module_idem`). Options as upstream: `-o`, `--output`, `-v`,
`--color`, `-a`, `--all`, `-d`, `--delete REGEX` (repeatable; `Silmaril.Wasm.Tools.Regex`),
`-t`, `--wat`, `[INPUT]`.
-/

namespace WasmTools.Strip

open Silmaril.Wasm.Tools.OptGrammar WasmTools.VCommon

/-- The options of `strip`. -/
def specs : List Spec :=
  outputSpecs ++ generalSpecs ++
  [{ long := "all", short := some 'a', kind := .flag },
   { long := "delete", short := some 'd', kind := .multi, valueName := "REGEX" },
   { long := "wat", short := some 't', kind := .flag }]

def usage : String := "wasm-tools strip [OPTIONS] [INPUT]"

/-- What `strip` reads from its command line (the fields of
`Silmaril.Cli.Spec.WasmTools.Strip.StripArgs`, the worked example of the CLI spec, and the general
options). -/
structure StripOpts where
  io : InOut
  /-- `-a, --all` -/
  all : Bool
  /-- `-d, --delete <REGEX>`, in order -/
  delete : List String
  /-- `-t, --wat` -/
  wat : Bool
  deriving Repr, DecidableEq

def StripOpts.ofParsed (p : Parsed) : StripOpts where
  io := InOut.ofParsed p
  all := p.flag "all"
  delete := p.values "delete"
  wat := p.flag "wat"

/-- The body of `strip` on its record (`run`; the full build: from the specification's
matches, `WasmTools.SpecCore`). -/
def body (a : StripOpts) : IO UInt32 := do
  let input ← match ← readInput a.io.input with
    | .error e => return ← fail e
    | .ok b => pure b
  -- `RegexSet::new` rejects a bad pattern after the input is read
  let patterns := a.delete
  for pat in patterns do
    if let .error e := Silmaril.Wasm.Tools.Regex.parse pat then
      return ← fail s!"regex parse error: {pat}: {e} (outside the supported subset)"
  let mode := Silmaril.Wasm.Tools.Strip.Mode.ofArgs a.all patterns
  let rm := mode.removes Silmaril.Wasm.Tools.Regex.isMatch
  -- `stripFast` = `Strip.strip` on the bytes (`FastPaths.stripFast_eq`)
  match Silmaril.Wasm.Tools.FastPaths.stripFast rm input with
  | .error e => fail e
  | .ok out =>
    if a.wat then
      -- `-t`: the stripped module printed by the wasmprinter-format printer
      -- (`Silmaril.Wasm.Tools.Text.binaryToWat_sound`)
      match Silmaril.Wasm.Tools.Text.binaryToWat out with
      | .error e => return ← fail e
      | .ok t =>
        match ← writeText a.io.output t with
        | .ok () => return 0
        | .error e => return ← fail e
    match ← writeBinary a.io.output out with
    | .ok () => return 0
    | .error e => fail e

/-- Run `strip` on its arguments. -/
def run (args : List String) : IO UInt32 := do
  let p ← match ← parseOrExit specs 1 usage HelpV.strip_short HelpV.strip_long args with
    | .error code => return code
    | .ok p => pure p
  body (StripOpts.ofParsed p)

end WasmTools.Strip
