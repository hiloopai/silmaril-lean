import WasmTools.GenCommon
import Silmaril.Wasm.Tools.Gen.Cmd.Smith.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.Model.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.Input.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.SmithConfig.Defs

/-!
# `wasm-tools smith` (gentool track)

Grammar `spec` (every option of upstream 1.262.0, in its order), the model of the feature flags
(`Silmaril.Wasm.Tools.Gen.Cmd.Model.model`), the limits of the `--max-*`/`--min-*` options
(`config`), and a thin body: read the seed, run the pure generator
`Silmaril.Wasm.Tools.Gen.Cmd.Smith.smith` (valid in the model: `Smith.Thms.smith_validInW`,
bytes: `smithBytes_spec`, `smithBytesC_spec`), write the binary or (`-t`) its text.

Honoured: the feature flags (the model), the limits, `--ensure-termination`,
`--disallow-traps`, `--allowed-instructions` (wasm-smith's kinds; an unknown kind is clap's
usage error, status 2), `--generate-custom-sections` (`Smith.smithBytesC`) and
`--available-imports` (function and global imports drawn from the given module's). Options that
would change what upstream generates in a way this generator cannot honour are refused with an
error (status 1) rather than ignored: `--memory-offset-choices`, `--canonicalize-nans true`.
`--exports FILE` makes the output export exactly the exports of FILE (names and types, each
a new entity of that type); `--module-shape FILE` also gives it exactly FILE's imports. `--config FILE` fills the options the
command line does not give from a JSON file (`SmithConfig`), as upstream does.
`--min-uleb-size` is accepted and has no effect, as in wasm-smith 0.263 (which declares the
option and never reads it). The others hold of every output (no threads are generated).
-/

namespace WasmTools.GenSmith

open Silmaril.Wasm.Tools.Gen.Cmd

def spec : Args.Spec where
  path := "wasm-tools smith"
  positionals := [("[INPUT]", false)]
  usage := "wasm-tools smith [OPTIONS] [INPUT]"
  opts := [
    { long := "output", short := some 'o', kind := .str, valName := "OUTPUT" },
    { long := "wat", short := some 't' },
    { long := "ensure-termination" },
    { long := "fuel", short := some 'f', kind := .ranged 4294967295, valName := "FUEL" },
    { long := "config", short := some 'c', kind := .str, valName := "CONFIG" },
    { long := "available-imports", kind := .str, valName := "AVAILABLE_IMPORTS" },
    { long := "exports", kind := .str, valName := "EXPORTS" },
    { long := "module-shape", kind := .str, valName := "MODULE_SHAPE" },
    { long := "allow-start-export", kind := .bool, valName := "ALLOW_START_EXPORT" },
    { long := "allowed-instructions", kind := .str, valName := "ALLOWED_INSTRUCTIONS" },
    { long := "allow-floats", kind := .bool, valName := "ALLOW_FLOATS" },
    { long := "bulk-memory-enabled", kind := .bool, valName := "BULK_MEMORY_ENABLED" },
    { long := "canonicalize-nans", kind := .bool, valName := "CANONICALIZE_NANS" },
    { long := "disallow-traps", kind := .bool, valName := "DISALLOW_TRAPS" },
    { long := "exceptions-enabled", kind := .bool, valName := "EXCEPTIONS_ENABLED" },
    { long := "export-everything", kind := .bool, valName := "EXPORT_EVERYTHING" },
    { long := "gc-enabled", kind := .bool, valName := "GC_ENABLED" },
    { long := "compact-imports-enabled", kind := .bool, valName := "COMPACT_IMPORTS_ENABLED" },
    { long := "custom-descriptors-enabled", kind := .bool, valName := "CUSTOM_DESCRIPTORS_ENABLED" },
    { long := "custom-page-sizes-enabled", kind := .bool, valName := "CUSTOM_PAGE_SIZES_ENABLED" },
    { long := "generate-custom-sections", kind := .bool, valName := "GENERATE_CUSTOM_SECTIONS" },
    { long := "max-aliases", kind := .u64, valName := "MAX_ALIASES" },
    { long := "max-components", kind := .u64, valName := "MAX_COMPONENTS" },
    { long := "max-data-segments", kind := .u64, valName := "MAX_DATA_SEGMENTS" },
    { long := "max-element-segments", kind := .u64, valName := "MAX_ELEMENT_SEGMENTS" },
    { long := "max-elements", kind := .u64, valName := "MAX_ELEMENTS" },
    { long := "max-exports", kind := .u64, valName := "MAX_EXPORTS" },
    { long := "max-funcs", kind := .u64, valName := "MAX_FUNCS" },
    { long := "max-globals", kind := .u64, valName := "MAX_GLOBALS" },
    { long := "max-imports", kind := .u64, valName := "MAX_IMPORTS" },
    { long := "max-instances", kind := .u64, valName := "MAX_INSTANCES" },
    { long := "max-instructions", kind := .u64, valName := "MAX_INSTRUCTIONS" },
    { long := "max-memories", kind := .u64, valName := "MAX_MEMORIES" },
    { long := "max-memory32-bytes", kind := .u64, valName := "MAX_MEMORY32_BYTES" },
    { long := "max-memory64-bytes", kind := .u64, valName := "MAX_MEMORY64_BYTES" },
    { long := "max-modules", kind := .u64, valName := "MAX_MODULES" },
    { long := "max-nesting-depth", kind := .u64, valName := "MAX_NESTING_DEPTH" },
    { long := "max-table-elements", kind := .u64, valName := "MAX_TABLE_ELEMENTS" },
    { long := "max-tables", kind := .u64, valName := "MAX_TABLES" },
    { long := "max-tags", kind := .u64, valName := "MAX_TAGS" },
    { long := "max-type-size", kind := .ranged 4294967295, valName := "MAX_TYPE_SIZE" },
    { long := "max-types", kind := .u64, valName := "MAX_TYPES" },
    { long := "max-values", kind := .u64, valName := "MAX_VALUES" },
    { long := "memory64-enabled", kind := .bool, valName := "MEMORY64_ENABLED" },
    { long := "memory-max-size-required", kind := .bool, valName := "MEMORY_MAX_SIZE_REQUIRED" },
    { long := "memory-offset-choices", kind := .str, valName := "MEMORY_OFFSET_CHOICES" },
    { long := "min-data-segments", kind := .u64, valName := "MIN_DATA_SEGMENTS" },
    { long := "min-element-segments", kind := .u64, valName := "MIN_ELEMENT_SEGMENTS" },
    { long := "min-elements", kind := .u64, valName := "MIN_ELEMENTS" },
    { long := "min-exports", kind := .u64, valName := "MIN_EXPORTS" },
    { long := "min-funcs", kind := .u64, valName := "MIN_FUNCS" },
    { long := "min-globals", kind := .u64, valName := "MIN_GLOBALS" },
    { long := "min-imports", kind := .u64, valName := "MIN_IMPORTS" },
    { long := "min-memories", kind := .u64, valName := "MIN_MEMORIES" },
    { long := "min-tables", kind := .u64, valName := "MIN_TABLES" },
    { long := "min-tags", kind := .u64, valName := "MIN_TAGS" },
    { long := "min-types", kind := .u64, valName := "MIN_TYPES" },
    { long := "min-uleb-size", kind := .ranged 255, valName := "MIN_ULEB_SIZE" },
    { long := "multi-value-enabled", kind := .bool, valName := "MULTI_VALUE_ENABLED" },
    { long := "reference-types-enabled", kind := .bool, valName := "REFERENCE_TYPES_ENABLED" },
    { long := "relaxed-simd-enabled", kind := .bool, valName := "RELAXED_SIMD_ENABLED" },
    { long := "saturating-float-to-int-enabled", kind := .bool, valName := "SATURATING_FLOAT_TO_INT_ENABLED" },
    { long := "sign-extension-ops-enabled", kind := .bool, valName := "SIGN_EXTENSION_OPS_ENABLED" },
    { long := "shared-everything-threads-enabled", kind := .bool, valName := "SHARED_EVERYTHING_THREADS_ENABLED" },
    { long := "simd-enabled", kind := .bool, valName := "SIMD_ENABLED" },
    { long := "tail-call-enabled", kind := .bool, valName := "TAIL_CALL_ENABLED" },
    { long := "table-max-size-required", kind := .bool, valName := "TABLE_MAX_SIZE_REQUIRED" },
    { long := "threads-enabled", kind := .bool, valName := "THREADS_ENABLED" },
    { long := "allow-invalid-funcs", kind := .bool, valName := "ALLOW_INVALID_FUNCS" },
    { long := "wide-arithmetic-enabled", kind := .bool, valName := "WIDE_ARITHMETIC_ENABLED" },
    { long := "extended-const-enabled", kind := .bool, valName := "EXTENDED_CONST_ENABLED" },
    { long := "const-expr-fuel", kind := .ranged 4294967295, valName := "CONST_EXPR_FUEL" },
    { long := "limit-arrays-in-const-exprs", kind := .bool, valName := "LIMIT_ARRAYS_IN_CONST_EXPRS" },
    { long := "verbose", short := some 'v', kind := .count },
    { long := "color", kind := .color, valName := "COLOR" }
  ]

/-- The limits of the options. -/
def config (p : Args.Parsed) : Smith.Config :=
  let n (k : String) (d : Nat) : Nat := (p.num? k).getD d
  let b (k : String) (d : Bool) : Bool := (p.bool? k).getD d
  { maxTypes := n "max-types" 100, maxImports := n "max-imports" 100,
    maxFuncs := n "max-funcs" 100, maxGlobals := n "max-globals" 100,
    maxExports := n "max-exports" 100, maxMemories := n "max-memories" 1,
    maxTables := n "max-tables" 1, maxDataSegments := n "max-data-segments" 100,
    maxElementSegments := n "max-element-segments" 100, maxElements := n "max-elements" 100,
    maxInstructions := n "max-instructions" 100, maxNestingDepth := n "max-nesting-depth" 10,
    maxTableElements := n "max-table-elements" 1000000,
    maxMemoryPages := n "max-memory32-bytes" (2 ^ 32) / 65536,
    minFuncs := n "min-funcs" 0, minGlobals := n "min-globals" 0,
    minImports := n "min-imports" 0, minExports := n "min-exports" 0,
    minTypes := n "min-types" 0, minMemories := n "min-memories" 0,
    minTables := n "min-tables" 0, minDataSegments := n "min-data-segments" 0,
    minElementSegments := n "min-element-segments" 0,
    allowStartExport := b "allow-start-export" true,
    exportEverything := b "export-everything" false,
    memoryMaxSizeRequired := b "memory-max-size-required" false,
    tableMaxSizeRequired := b "table-max-size-required" false,
    ensureTermination := p.flag "ensure-termination",
    disallowTraps := b "disallow-traps" false,
    allowed := match p.str? "allowed-instructions" with
      | some v => (Smith.parseKinds v).toOption.getD Smith.allKinds
      | none => Smith.allKinds,
    customSections := b "generate-custom-sections" false }

/-- The model of the flags. -/
def model (p : Args.Parsed) : Silmaril.Wasm.Models.FeatureSet :=
  Model.model (p.bool? ·) ((p.num? "max-memories").getD 1)

/-- Options refused (see the module doc), with the reason. -/
def refused (p : Args.Parsed) : Option String :=
  let strs := ["memory-offset-choices"]
  match strs.find? (p.flag ·) with
  | some k => some s!"--{k}"
  | none =>
    if p.bool? "canonicalize-nans" == some true then some "--canonicalize-nans true" else none

/-- `--config FILE`: the options the command line does not give, from the JSON file
(`SmithConfig.parse`; upstream's messages, serde's cause without its position). -/
def withConfig (p : Args.Parsed) : IO (Except String Args.Parsed) := do
  match p.str? "config" with
  | none => return .ok p
  | some path =>
    match ← (IO.FS.readFile path).toBaseIO with
    | .error e => return .error (GenCommon.caused s!"failed to read json config: {path}"
        (GenCommon.osCause e))
    | .ok text =>
      match SmithConfig.parse (SmithConfig.fieldsOf spec) text with
      | .error e => return .error (GenCommon.caused s!"failed to decode json config: {path}" e)
      | .ok vals => return .ok { p with vals := p.vals ++ vals }

/-- The function and global imports of a module (`--available-imports`); imports of other
kinds are not used by this generator. -/
def importsOf (m : Silmaril.Wasm.Module) :
    List (String × String × Silmaril.Wasm.FuncType) × List (String × String × Silmaril.Wasm.GlobalType) :=
  let tys := m.types.map fun r => match r.types with
    | [⟨true, [], .func f⟩] => some f
    | _ => none
  (m.imports.filterMap fun i => match i.type with
    | .func x => (tys.getD x.toNat none).map fun f => (i.moduleName, i.name, f)
    | _ => none,
   m.imports.filterMap fun i => match i.type with
    | .global g => some (i.moduleName, i.name, g)
    | _ => none)

/-- Read the module of `--exports` or `--module-shape` (binary or text, as `wat::parse_file`). -/
def readShape (path : String) : IO (Except String Silmaril.Wasm.Module) := do
  match ← (IO.FS.readBinFile path).toBaseIO with
  | .error e => return .error (GenCommon.caused s!"failed to read from `{path}`" (GenCommon.osCause e))
  | .ok b => return Input.readModule b

/-- clap's error for a value `--allowed-instructions` does not parse (wasm-smith's
`InstructionKinds::from_str`). -/
def kindsError (p : Args.Parsed) : Option String :=
  match p.str? "allowed-instructions" with
  | some v =>
    match Smith.parseKinds v with
    | .error part => some (s!"error: invalid value '{v}' for '--allowed-instructions " ++
        s!"<ALLOWED_INSTRUCTIONS>': unknown instruction kind: {part}\n\n" ++
        "For more information, try '--help'.\n")
    | .ok _ => none
  | none => none

/-- What `smith` reads from its command line. The generator settings stay the typed table of
option values (`settings`, `Args.Parsed`): `--config FILE` supplies the settings the command
line does not give, under the same keys and kinds (`withConfig`), so the configuration
(`config`, `model`, `refused`) is computed from the merged table at run time. -/
structure SmithArgs where
  /-- `[INPUT]`: the seed (none or `-`: stdin) -/
  input : Option String
  /-- `-o, --output <OUTPUT>` -/
  output : Option String
  /-- `-t, --wat` -/
  wat : Bool
  /-- every other option, typed (`-c, --config` included) -/
  settings : Args.Parsed

/-- The record of the typed values the specification's matches give (`GenCommon.ofMatches`). -/
def SmithArgs.ofParsed (p : Args.Parsed) : SmithArgs where
  input := p.pos.head?
  output := p.str? "output"
  wat := p.flag "wat"
  settings := p

/-- The body on its arguments (`run`: from the specification's matches). -/
def body (a : SmithArgs) : IO UInt32 := do
  let p ← match ← withConfig a.settings with
    | .ok p => pure p
    | .error e => return ← GenCommon.fail e
  if let some e := kindsError p then
    (← IO.getStderr).putStr e
    return 2
  if let some o := refused p then
    return ← GenCommon.fail s!"option `{o}` is not supported by this wasm-tools smith (see docs/projects/wasm-components.md)"
  match ← GenCommon.readInput a.input (fun path => s!"failed to read '{path}'") with
  | .error e => GenCommon.fail e
  | .ok seed =>
    let S := model p
    let cfg ← match p.str? "available-imports" with
      | none => pure (config p)
      | some path =>
        match ← (IO.FS.readBinFile path).toBaseIO with
        | .error e => return ← GenCommon.fail (GenCommon.caused s!"failed to read from `{path}`"
            (GenCommon.osCause e))
        | .ok b =>
          match Input.readModule b with
          | .error e => return ← GenCommon.fail e
          | .ok m =>
            let (fs, gs) := importsOf m
            pure { config p with availFuncs := some fs, availGlobals := gs }
    -- `--exports` / `--module-shape` (the shape's exports win, as in wasm-smith)
    let cfg : Smith.Config ← match p.str? "module-shape", p.str? "exports" with
      | some path, _ =>
        match ← readShape path with
        | .error e => return ← GenCommon.fail e
        | .ok m =>
          match Smith.importsOf m, Smith.exportsOf m with
          | some is, some es =>
            pure { cfg with shapeImports := some is, reqExports := some es, availFuncs := none,
                            availGlobals := [] }
          | _, _ => return ← GenCommon.fail (s!"the module shape `{path}` has types outside " ++
              "this wasm-tools smith (see docs/projects/wasm-components.md)")
      | none, some path =>
        match ← readShape path with
        | .error e => return ← GenCommon.fail e
        | .ok m =>
          match Smith.exportsOf m with
          | some es => pure { cfg with reqExports := some es }
          | none => return ← GenCommon.fail (s!"the exports of `{path}` have types outside " ++
              "this wasm-tools smith (see docs/projects/wasm-components.md)")
      | none, none => pure cfg
    let bytes := Smith.smithBytesC S cfg seed
    if a.wat then
      let m := Smith.smith S cfg seed
      let text := if cfg.customSections then
          match Print.printModuleC? m
              (Sections.printAnchors ⟨bytes.toArray⟩) with
          | some s => .ok s
          | none => GenCommon.printText m >>= fun _ =>
              .error "the custom sections of this module are outside the printer of this wasm-tools"
        else GenCommon.printText m
      match text with
      | .error e => GenCommon.fail e
      | .ok s =>
        match ← GenCommon.writeText a.output s with
        | .error e => GenCommon.fail e
        | .ok () => return 0
    else
      match ← GenCommon.writeBytes a.output ⟨bytes.toArray⟩ with
      | .error e => GenCommon.fail e
      | .ok () => return 0

/-- Run on the specification's matches (`GenCommon.runMatches`). -/
def run (m : Silmaril.Cli.Matches) : IO UInt32 :=
  GenCommon.runMatches spec (fun p => body (SmithArgs.ofParsed p)) m

end WasmTools.GenSmith
