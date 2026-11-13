import WasmTools.SpecArgs

/-!
# The arguments of `component new/wit/embed/targets/unbundle/semver-check` and `compose`

One record per subcommand, read from the matches of the specification
`Silmaril.Cli.Spec.WasmTools.tool` in one place (`…Args.ofMatches`, keys: the option ids of the
grammar); the bodies (`WasmTools.Component.Cmds`, `.ComposeCmd`) are functions of the record and
know no option ids. Values the specification supplies as defaults (`--color auto`,
`unbundle --threshold 10240`) are in the record as if given; values the specification leaves to
the program (`--threshold` digits, `--import-name OLD=NEW`, `--encoding`) are kept as the words
given, and the body refuses them with clap's message.

Optional booleans (`--validate[=<true|false>]`): `none` when absent, a bare occurrence is
`true` (the grammar's `missing` value).
-/

namespace WasmTools.Component

open Silmaril.Cli

/-- An optional boolean's value (`--x[=<true|false>]`): `none` when absent. -/
def boolOf (m : Matches) (id : String) : Option Bool := (m.str? id).map (· == "true")

/-- What the subcommands that read a Wasm input and write a Wasm or text output share
(upstream's `InputArg`, `OutputArg`, `GeneralOpts`, `GenerateDwarfArg`). -/
structure IoArgs where
  /-- `[INPUT]` (none or `-`: stdin) -/
  input : Option String := none
  /-- `-o, --output <OUTPUT>` (none: stdout) -/
  output : Option String := none
  /-- `--generate-dwarf <lines|full>` or `-g` given (refused on text inputs) -/
  dwarf : Bool := false
  /-- `-v`, repeated -/
  verbose : Nat := 0
  /-- `--color <COLOR>` (default `auto`) -/
  color : String := "auto"
  deriving Repr, BEq, Inhabited

def IoArgs.ofMatches (m : Matches) : IoArgs where
  input := m.str? "input"
  output := m.str? "output"
  dwarf := m.flag "generate-dwarf" || m.flag "-g"
  verbose := m.count "verbose"
  color := (m.str? "color").getD "auto"

/-- `--features F,…` (each occurrence split at spaces and commas) and `--all-features`. -/
structure FeatureArgs where
  features : List String := []
  allFeatures : Bool := false
  deriving Repr, BEq, Inhabited

def FeatureArgs.ofMatches (m : Matches) : FeatureArgs where
  features := (m.strs "features").flatMap fun f =>
    (f.splitOn " ").flatMap fun f => (f.splitOn ",").filter (· ≠ "")
  allFeatures := m.flag "all-features"

/-- `component new`. -/
structure NewArgs where
  io : IoArgs
  /-- `--import-name <OLD=NEW>`, in order (the words given) -/
  importName : List String
  /-- `--adapt <[NAME=]MODULE>`, in order -/
  adapt : List String
  validate : Option Bool
  reallocViaMemoryGrow : Bool
  mergeImportsBasedOnSemver : Option Bool
  emitCanonicalNames : Bool
  rejectLegacyNames : Bool
  debugNames : Option Bool
  returnCallRef : Option Bool
  /-- `-t, --wat` -/
  wat : Bool
  deriving Repr, BEq

def NewArgs.ofMatches (m : Matches) : NewArgs where
  io := IoArgs.ofMatches m
  importName := m.strs "import-name"
  adapt := m.strs "adapt"
  validate := boolOf m "validate"
  reallocViaMemoryGrow := m.flag "realloc-via-memory-grow"
  mergeImportsBasedOnSemver := boolOf m "merge-imports-based-on-semver"
  emitCanonicalNames := m.flag "emit-canonical-names"
  rejectLegacyNames := m.flag "reject-legacy-names"
  debugNames := boolOf m "debug-names"
  returnCallRef := boolOf m "return-call-ref"
  wat := m.flag "wat"

/-- `component embed`. -/
structure EmbedArgs where
  io : IoArgs
  /-- `<WIT>` -/
  wit : String
  feats : FeatureArgs
  /-- `--encoding <ENCODING>` (the word given; checked by the body) -/
  encoding : Option String
  /-- `-w, --world <WORLD>` -/
  world : Option String
  emitCanonicalNames : Bool
  dummy : Bool
  dummyNames : Option String
  asyncCallback : Bool
  asyncStackful : Bool
  wat : Bool
  onlyCustom : Bool
  deriving Repr, BEq

def EmbedArgs.ofMatches (m : Matches) : EmbedArgs where
  io := IoArgs.ofMatches m
  wit := (m.str? "wit").getD ""
  feats := FeatureArgs.ofMatches m
  encoding := m.str? "encoding"
  world := m.str? "world"
  emitCanonicalNames := m.flag "emit-canonical-names"
  dummy := m.flag "dummy"
  dummyNames := m.str? "dummy-names"
  asyncCallback := m.flag "async-callback"
  asyncStackful := m.flag "async-stackful"
  wat := m.flag "wat"
  onlyCustom := m.flag "only-custom"

/-- `component wit`. -/
structure WitArgs where
  io : IoArgs
  wasm : Bool
  wat : Bool
  noDocs : Bool
  outDir : Option String
  skipValidation : Bool
  json : Bool
  importize : Bool
  importizeOutWorldName : Option String
  importizeWorld : Option String
  exportize : Bool
  exportizeOutWorldName : Option String
  exportizeImport : List String
  exportizeWorld : Option String
  mergeWorldImportsBasedOnSemver : Option String
  generateNominalTypeIds : Option String
  feats : FeatureArgs
  emitCanonicalNames : Bool
  deriving Repr, BEq

def WitArgs.ofMatches (m : Matches) : WitArgs where
  io := IoArgs.ofMatches m
  wasm := m.flag "wasm"
  wat := m.flag "wat"
  noDocs := m.flag "no-docs"
  outDir := m.str? "out-dir"
  skipValidation := m.flag "skip-validation"
  json := m.flag "json"
  importize := m.flag "importize"
  importizeOutWorldName := m.str? "importize-out-world-name"
  importizeWorld := m.str? "importize-world"
  exportize := m.flag "exportize"
  exportizeOutWorldName := m.str? "exportize-out-world-name"
  exportizeImport := m.strs "exportize-import"
  exportizeWorld := m.str? "exportize-world"
  mergeWorldImportsBasedOnSemver := m.str? "merge-world-imports-based-on-semver"
  generateNominalTypeIds := m.str? "generate-nominal-type-ids"
  feats := FeatureArgs.ofMatches m
  emitCanonicalNames := m.flag "emit-canonical-names"

/-- `component targets`. -/
structure TargetsArgs where
  io : IoArgs
  wit : String
  feats : FeatureArgs
  world : Option String
  semverCompatible : Bool
  deriving Repr, BEq

def TargetsArgs.ofMatches (m : Matches) : TargetsArgs where
  io := IoArgs.ofMatches m
  wit := (m.str? "wit").getD ""
  feats := FeatureArgs.ofMatches m
  world := m.str? "world"
  semverCompatible := m.flag "semver-compatible"

/-- `component semver-check`. -/
structure SemverArgs where
  wit : String
  feats : FeatureArgs
  prev : String
  new : String
  verbose : Nat
  color : String
  deriving Repr, BEq

def SemverArgs.ofMatches (m : Matches) : SemverArgs where
  wit := (m.str? "wit").getD ""
  feats := FeatureArgs.ofMatches m
  prev := (m.str? "prev").getD ""
  new := (m.str? "new").getD ""
  verbose := m.count "verbose"
  color := (m.str? "color").getD "auto"

/-- `component unbundle`. -/
structure UnbundleArgs where
  io : IoArgs
  /-- `--module-dir <PATH>` (required) -/
  moduleDir : String
  /-- `--threshold <SIZE>` (the word; default `10240`) -/
  threshold : String
  wat : Bool
  deriving Repr, BEq

def UnbundleArgs.ofMatches (m : Matches) : UnbundleArgs where
  io := IoArgs.ofMatches m
  moduleDir := (m.str? "module-dir").getD "."
  threshold := (m.str? "threshold").getD "10240"
  wat := m.flag "wat"

/-- `compose` (deprecated upstream). -/
structure ComposeArgs where
  /-- `<COMPONENT>` -/
  component : String
  output : Option String
  config : Option String
  definitions : List String
  searchPath : List String
  skipValidation : Bool
  noImports : Bool
  wat : Bool
  quiet : Bool
  verbose : Nat
  color : String
  deriving Repr, BEq

def ComposeArgs.ofMatches (m : Matches) : ComposeArgs where
  component := (m.str? "component").getD ""
  output := m.str? "output"
  config := m.str? "config"
  definitions := m.strs "definitions"
  searchPath := m.strs "search-path"
  skipValidation := m.flag "skip-validation"
  noImports := m.flag "no-imports"
  wat := m.flag "wat"
  quiet := m.flag "quiet"
  verbose := m.count "verbose"
  color := (m.str? "color").getD "auto"

end WasmTools.Component
