module

public import Silmaril.Cli.Clap.Defs

/-!
# The command line of `wasm-opt`

The surface of `wasm-opt` (`tools/wasm-opt`, `Silmaril.Wasm.Binaryen.Driver`):
silmaril's `wasm-opt`-style command line plus the verified stages. An args grammar
(`extraWasmOpt : Silmaril.Cli.Command`) in the clap dialect (`tool : Clap.Tool`). Binaryen's
conventions are not clap's: presets are single-dash words (`-O2`, `-Os`) and `--all-features`
is also `-all`; both are single-dash names of the grammar, matched exactly before short
clusters. Value types: `--rounds` is a natural number (`ArgType.nat`), `--passes` a comma-separated list of
stage names (`Driver.parsePasses`).

The stage names are pinned here as data (as `wasm-opt --print-passes` prints them on
2026-11-10); `Silmaril.Wasm.Binaryen.DriverSpec` proves that they are exactly the driver's
selectable stages, and that the driver's reading of the verified-stages path agrees with this
surface
on the normal form (`DriverSpec.parseArgs_render`).

**One surface for two paths.** Without a verified-stage option the driver hands the whole
command line to silmaril's parser (`--mode`, the growth-policy flags and `--print-presets`
exist only there); with one, it uses its own parser, which rejects those flags. The surface
lists both groups; that they cannot be mixed is a conflicts rule, which surfaces do not
model (docs/projects/wasm-binaryen-tooling.md, "Apply").
-/

@[expose] public section

namespace Silmaril.Cli.Spec.WasmOpt

open Silmaril.Cli

/-- silmaril's named stages, selectable as `--NAME` and in `--passes`. -/
def silmarilNamed : List String :=
  ["dce", "remove-unused-names", "merge-blocks", "vacuum", "simplify-globals", "directize",
   "precompute", "code-folding", "coalesce-locals", "remove-unused-brs",
   "optimize-instructions", "simplify-locals", "remove-unused-module-elements", "inlining"]

/-- silmaril's local subrules, selectable only in `--passes`. -/
def silmarilSubrules : List String := ["const-branch", "const-select", "add-chain"]

/-- The verified stages, selectable as `--NAME` and in `--passes`. -/
def extraStages : List String := ["neutral-ops", "eqz-pair", "rse-line", "drop-get", "tee-form"]

/-- The lambda-SSA stage: opt-in, `--ssa` or `ssa` in `--passes`. -/
def ssaStage : String := "ssa"

/-- Every name `--passes` accepts, in the driver's order (`Driver.selectableStages`). -/
def passNames : List String :=
  ["dce", "remove-unused-names", "merge-blocks", "vacuum", "simplify-globals", "directize",
   "precompute", "const-branch", "const-select", "add-chain", "code-folding", "coalesce-locals",
   "remove-unused-brs", "optimize-instructions", "simplify-locals",
   "remove-unused-module-elements", "inlining"] ++ extraStages ++ [ssaStage]

/-- The presets without their dash, in the order of the usage text. -/
def presetNames : List String := ["O", "O0", "O1", "O2", "O3", "O4", "Os", "Oz"]

/-- The preset words: `-O`, `-O0`, …, `-Oz`. -/
def presetTokens : List String := presetNames.map ("-" ++ ·)

/-- A stage switch `--NAME`; stages may repeat (order and repetitions are kept). -/
def stageOpt (name : String) : Opt :=
  { id := name, repeated := true, help := "append the stage " ++ name }

/-- A preset word (`-O2`): a single-dash name, which may repeat. -/
def presetOpt (n : String) : Opt :=
  { id := "-" ++ n, long := [], short := [n], repeated := true, exact := true,
    help := "append a restricted preset" }

/-- Options that only act as the sole argument (`wasm-opt --print-passes`). -/
def infoOpts : List Opt :=
  [{ helpOpt with help := "show this help" },
   { id := "help-silmaril", help := "show the help of silmaril's wasm-opt" },
   { id := "version", help := "show the compatibility baseline" },
   { id := "print-passes", help := "list the selectable stages" },
   { id := "print-coverage", help := "print Binaryen pass coverage (silmaril / verified stages / none)" },
   { id := "print-verified-presets", help := "print the verified-stage schedules" }]

/-- Options of the verified-stages path. Switches that the driver lets repeat are `repeated`. -/
def extraOpts : List Opt :=
  [{ id := "verified-stages", repeated := true,
     help := "-O* presets use verified-stage schedules; alone, selects the -O2 one" },
   { id := "stats", repeated := true, help := "report sizes and per-stage firing counts on stderr" },
   { id := "component", repeated := true, help := "reserved for a component-model mode (exit 2)" },
   { id := "print-pipeline", repeated := true,
     help := "print the expanded stage list without file IO" }]

/-- Options of both paths. -/
def commonOpts : List Opt :=
  [{ id := "output", short := ["o"], arg := some .path, metavar := "OUT.wasm",
     help := "output binary; - for stdout; without it no binary is written" },
   { id := "rounds", arg := some .nat, metavar := "N", default := some "1", repeated := true,
     help := "repeat the selected list" },
   { id := "passes", arg := some .str, metavar := "NAME,...", repeated := true,
     help := "append an ordered list of stages" },
   { id := "all-features", short := ["all"], repeated := true,
     help := "allow all supported proposals" }] ++
  presetNames.map presetOpt

/-- Options of silmaril's path only. -/
def silmarilOpts : List Opt :=
  [{ id := "mode", arg := some (.enum ["equivalence", "refinement", "trap-insertion"]),
     metavar := "MODE", default := some "equivalence",
     help := "correctness mode (silmaril path only)" },
   { id := "select-grow-failure", help := "requires refinement or trap-insertion mode" },
   { id := "trap-grow-failure", help := "requires trap-insertion mode" },
   { id := "select-zero-grow-success", help := "requires refinement or trap-insertion mode" },
   { id := "print-presets", help := "show preset omissions and substitutions" }]

/-- The exit codes of `wasm-opt` (`Driver.runExtraOpt`, `runExtraPlan`). -/
def exits : List (Nat × String) :=
  [(0, "success; also the information options and --print-pipeline"),
   (1, "optimisation, decoding or file IO failed"),
   (2, "a usage error (verified-stages path), a missing input, or --component")]

/-- The input, `-` for stdin. -/
def inputPos : Pos :=
  { id := "input", type := .path, arity := .optional, metavar := "IN.wasm",
    help := "binary input; - for stdin" }

/-- `wasm-opt`. -/
def extraWasmOpt : Command where
  name := "wasm-opt"
  about := "silmaril's wasm-opt CLI plus verified stages. " ++
    "No passes run by default; order and repetitions are preserved."
  pos := [inputPos]
  opts := infoOpts ++ extraOpts ++ commonOpts ++
    (silmarilNamed ++ extraStages ++ [ssaStage]).map stageOpt ++ silmarilOpts
  exits := exits

/-- The options that select the verified-stages path (`Driver.usesVerifiedStages`): they
exclude silmaril's. -/
def extraOnly : List String :=
  ["verified-stages", "stats", "component", "print-pipeline"] ++ extraStages

/-- The options of silmaril's path only. -/
def silmarilOnly : List String :=
  ["mode", "select-grow-failure", "trap-grow-failure", "select-zero-grow-success",
   "print-presets"]

/-- `wasm-opt` in the clap dialect: value checks and the two paths as conflicts. -/
def tool : Clap.Tool where
  grammar := (extraWasmOpt.withChecks [("passes", .listOf ',' false (.oneOf passNames))]).withRules
    (extraOnly.flatMap fun a => silmarilOnly.map fun b => ([], .conflicts a b))

/-- The clap view (help, corpus, the reference reading). -/
def surface : Surface.Command := tool.surface.root

end Silmaril.Cli.Spec.WasmOpt
