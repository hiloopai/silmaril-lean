import WasmTools.GenCommon
import Silmaril.Wasm.Tools.Gen.Cmd.WitSmith.Defs
import Silmaril.Wasm.Tools.Component.WitPkg.Defs
import Silmaril.Wasm.Tools.Component.Wat.Defs

/-!
# `wasm-tools wit-smith` (gentool track)

Grammar `spec` (upstream 1.262.0's options, `wit_smith::Config` flattened), and a thin body:
read the seed, run the pure generator `Silmaril.Wasm.Tools.Gen.Cmd.WitSmith.witSmith` (the
document is valid in wasm-wit's sense and printable: `WitSmith.Thms.witSmith_valid`; its text
reads back as it: `witSmith_print`), print it as WIT (`Silmaril.Wasm.Wit.Text.print`) and encode
it as a WIT package component with the `component wit --wasm` core of the compcmd track
(`Silmaril.Wasm.Tools.Component.Cmd.witWasmOfSrc`: wasm-wit's resolver and encoder); write the
binary, or (`-t`) its text with compval's component printer (`Component.Wat.printBytes`).
When the encoder refuses the document, the fallback document is written instead (counted by
`tools/wasm-tools/tests/gen/wit-smith.sh`).

Options: the limits and the type flags are honoured; `--arbitrary-config` draws the
configuration from the seed first; `--world-include` adds `include`s of earlier worlds;
`--implements` only permits a kind of item, which this generator does not produce (accepted);
`--canonical-names` changes the encoding (`wit_component::encode`'s flag), which the wasm-wit
encoder does not have: refused with an error (status 1).
-/

namespace WasmTools.GenWitSmith

open Silmaril.Wasm.Tools.Gen.Cmd

def spec : Args.Spec where
  path := "wasm-tools wit-smith"
  positionals := [("[INPUT]", false)]
  usage := "wasm-tools wit-smith [OPTIONS] [INPUT]"
  opts := [
    Args.outputOpt, Args.watOpt,
    { long := "max-packages", kind := .u64, valName := "MAX_PACKAGES" },
    { long := "max-type-size", kind := .u64, valName := "MAX_TYPE_SIZE" },
    { long := "max-interface-items", kind := .u64, valName := "MAX_INTERFACE_ITEMS" },
    { long := "max-world-items", kind := .u64, valName := "MAX_WORLD_ITEMS" },
    { long := "max-pkg-items", kind := .u64, valName := "MAX_PKG_ITEMS" },
    { long := "max-type-parts", kind := .u64, valName := "MAX_TYPE_PARTS" },
    { long := "max-files-per-package", kind := .u64, valName := "MAX_FILES_PER_PACKAGE" },
    { long := "max-resource-items", kind := .u64, valName := "MAX_RESOURCE_ITEMS" },
    { long := "async" }, { long := "futures" }, { long := "streams" },
    { long := "error-context" }, { long := "fixed-length-lists" }, { long := "world-include" },
    { long := "implements" }, { long := "canonical-names" }, { long := "arbitrary-config" },
    Args.verboseOpt, Args.colorOpt]

/-- The configuration of the options. -/
def config (p : Args.Parsed) : WitSmith.Config :=
  let n (k : String) (d : Nat) : Nat := (p.num? k).getD d
  { maxPackages := n "max-packages" 10, maxTypeSize := n "max-type-size" 100,
    maxInterfaceItems := n "max-interface-items" 10, maxWorldItems := n "max-world-items" 10,
    maxPkgItems := n "max-pkg-items" 10, maxTypeParts := n "max-type-parts" 10,
    maxFilesPerPackage := n "max-files-per-package" 10,
    maxResourceItems := n "max-resource-items" 10,
    async := p.flag "async", futures := p.flag "futures", streams := p.flag "streams",
    errorContext := p.flag "error-context", fixedLengthLists := p.flag "fixed-length-lists",
    worldInclude := p.flag "world-include" }

/-- The package component of a document (`component wit --wasm` of its text). -/
def encodeDoc (d : Silmaril.Wasm.Wit.Document) : Except String ByteArray :=
  Silmaril.Wasm.Tools.Component.Cmd.witWasmOfSrc (.file "wit-smith.wit" (Silmaril.Wasm.Wit.Text.print d))

/-- The bytes for a seed, and whether the fallback was used. -/
def bytesOf (cfg : WitSmith.Config) (arb : Bool) (seed : ByteArray) :
    Except String (ByteArray × Bool) :=
  match encodeDoc (WitSmith.witSmith cfg arb seed) with
  | .ok b => .ok (b, false)
  | .error e =>
    match encodeDoc WitSmith.fallback with
    | .ok b => .ok (b, true)
    | .error _ => .error s!"failed to encode the generated WIT package: {e}"

/-- What `wit-smith` reads from its command line. -/
structure WitSmithArgs where
  /-- `[INPUT]`: the seed (none or `-`: stdin) -/
  input : Option String
  /-- `-o, --output <OUTPUT>` -/
  output : Option String
  /-- `-t, --wat` -/
  wat : Bool
  /-- the generator's limits and switches (`--max-…`, `--async`, …) -/
  config : WitSmith.Config
  arbitraryConfig : Bool
  canonicalNames : Bool
  verbose : Nat

/-- The record of the typed values the specification's matches give (`GenCommon.ofMatches`). -/
def WitSmithArgs.ofParsed (p : Args.Parsed) : WitSmithArgs where
  input := p.pos.head?
  output := p.str? "output"
  wat := p.flag "wat"
  config := GenWitSmith.config p
  arbitraryConfig := p.flag "arbitrary-config"
  canonicalNames := p.flag "canonical-names"
  verbose := p.count "verbose"

/-- The body on its arguments (`run`: from the specification's matches). -/
def body (a : WitSmithArgs) : IO UInt32 := do
  if a.canonicalNames then
    return ← GenCommon.fail ("option `--canonical-names` is not supported by this " ++
      "wasm-tools wit-smith (see docs/projects/wasm-components.md)")
  match ← GenCommon.readInput a.input (fun path => s!"failed to read '{path}'") with
  | .error e => GenCommon.fail e
  | .ok seed =>
    match bytesOf a.config a.arbitraryConfig seed with
    | .error e => GenCommon.fail e
    | .ok (b, fb) =>
      if a.verbose > 0 then
        let raw := WitSmith.rawDoc a.config a.arbitraryConfig seed
        if !WitSmith.accepts a.config a.arbitraryConfig raw then
          (← IO.getStderr).putStrLn "wit-smith: the raw document failed wasm-wit's check; wrote the fallback"
        else if fb then
          (← IO.getStderr).putStrLn "wit-smith: the generated package did not encode; wrote the fallback"
      if a.wat then
        match Silmaril.Wasm.Tools.Component.Wat.printBytes b with
        | .error e => GenCommon.fail e
        | .ok s =>
          match ← GenCommon.writeText a.output s with
          | .error e => GenCommon.fail e
          | .ok () => return 0
      else
        match ← GenCommon.writeBytes a.output b with
        | .error e => GenCommon.fail e
        | .ok () => return 0

/-- Run on the specification's matches (`GenCommon.runMatches`). -/
def run (m : Silmaril.Cli.Matches) : IO UInt32 :=
  GenCommon.runMatches spec (fun p => body (WitSmithArgs.ofParsed p)) m

end WasmTools.GenWitSmith
