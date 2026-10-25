module

public import Silmaril.Wasm.Binaryen.Exe.CleanupPresets
public import Silmaril.Wasm.Binaryen.Exe.CompatSelected

@[expose] public section

/-! # Explicit pass selection with a `wasm-opt`-style command line

This additive driver keeps every older cleanup parser and its defaults intact.
Only requested stages run, in command-line order, with repetitions retained.
The empty selection is the default. Each stage retains its current guard and
restricted implementation; accepting a familiar flag does not assert upstream
algorithm or optimization-level parity. No uncertified implementation registry
exists, so `--unverified` is rejected explicitly.

Pure selected optimization and its certificates live in `SelectedCleanup` and
`SelectedCleanupSound`. This module contains parsing, reporting and file IO.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Optimization

/-- These three local subrules do not name upstream Binaryen passes. They are
available explicitly through `--passes`, rather than advertised as upstream flags. -/
def FunctionStageId.hasUpstreamFlag : FunctionStageId → Bool
  | .constBranch | .constSelect | .addChain => false
  | _ => true

def optCompatStages : List CleanupStage := functionStageIds.map .function ++ [.rume, .inlining]

def optCompatNamedStages : List CleanupStage :=
  (functionStageIds.filter FunctionStageId.hasUpstreamFlag).map .function ++ [.rume, .inlining]

def optCompatPassList : String :=
  "Supported certified restricted implementations (not full upstream pass algorithms):\n" ++
  String.intercalate "\n" (optCompatNamedStages.map fun stage => "  --" ++ stage.name) ++
  "\nLocal subrules, selected with --passes NAME,...: const-branch, const-select, add-chain\n" ++
  "--inlining uses the existing guarded small/leaf-callee heuristic.\n" ++
  "All stages retain applicability checks and identity fallbacks."

def optCompatUsage : String :=
  "usage: wasm-opt [OPTIONS] IN.wasm [-o OUT.wasm]\n" ++
  "       wasm-opt --print-passes\n" ++
  "  --PASS                           append a supported named pass\n" ++
  "  --passes NAME,...                 append an ordered list of local stages\n" ++
  "  --all-features, -all              allow all supported proposals; unsupported inputs still reject\n" ++
  "  -O, -O0, -O1, -O2, -O3, -O4, -Os, -Oz  append a restricted preset\n" ++
  "  --rounds N                        repeat the selected list (default: 1)\n" ++
  "  --print-pipeline                  inspect the expanded plan without file IO\n" ++
  "  --print-presets                   show preset omissions and substitutions\n" ++
  "  -o FILE, --output FILE             output binary; input/options may be reordered\n" ++
  "  -                                binary stdin (input) or stdout (output)\n" ++
  "  --mode equivalence|refinement|trap-insertion  (default: equivalence)\n" ++
  "  --select-grow-failure              requires refinement or trap-insertion mode\n" ++
  "  --trap-grow-failure                requires trap-insertion mode\n" ++
  "  --select-zero-grow-success         requires refinement or trap-insertion mode\n" ++
  "  -h, --help                        show this help\n" ++
  "  --version                         show the compatibility baseline\n" ++
  "No passes run by default. Order and repetitions are preserved.\n" ++
  "--coalesce-locals selects only its existing adjacent-overwrite rule here;\n" ++
  "wasm-opt-modes-lean retains its older whole-pipeline flag behavior.\n" ++
  "-O is -Os. -O0 appends nothing; it does not clear earlier selections.\n" ++
  "Presets use available restricted implementations, not upstream algorithm parity.\n" ++
  "Without -o, conversion runs and no binary is written. Binary input only.\n" ++
  "No uncertified --unverified registry is implemented.\n" ++
  "Exact selected cleanup holds at every numerical profile with the closed host.\n" ++
  "Growth-policy rewrites retain their documented wrapper and mode restrictions.\n\n" ++
  optCompatPassList

/-- A fully checked command, retaining the exact requested stage sequence. -/
structure OptCompatOptions where
  input : String
  output : Option String
  stages : List CleanupStage
  policy : TrapGrowOptions
  deriving Repr

/-- Pipeline inspection is an explicit no-IO action, rather than an optimizer
option that silently suppresses a requested output. -/
inductive OptCompatCommand where
  | optimize (options : OptCompatOptions)
  | printPipeline (stages : List CleanupStage) (policy : TrapGrowOptions)
  | optimizeZeroGrow (options : OptCompatOptions)
  | printZeroGrowPipeline (stages : List CleanupStage) (policy : TrapGrowOptions)
  deriving Repr

structure OptCompatParseState where
  input : Option String := none
  output : Option String := none
  stagesRev : List CleanupStage := []
  policy : TrapGrowOptions := { base := { rounds := 1 } }
  printPipeline : Bool := false
  selectZeroGrowSuccess : Bool := false

def parseOptCompatPreset : String → Option CleanupPreset
  | "-O" | "-Os" => some .os
  | "-O0" => some .o0
  | "-O1" => some .o1
  | "-O2" => some .o2
  | "-O3" => some .o3
  | "-O4" => some .o4
  | "-Oz" => some .oz
  | _ => none

def optCompatPipeline (stages : List CleanupStage) (policy : TrapGrowOptions) : String :=
  let mode := match policy.base.mode with
    | .equivalence => "equivalence"
    | .refinement => "refinement"
    | .trapInsertion => "trap-insertion"
  "Expanded restricted pipeline; no files read or written.\n" ++
  "passes: " ++ String.intercalate "," (stages.map CleanupStage.name) ++ "\n" ++
  "rounds: " ++ toString policy.base.rounds ++ "\nmode: " ++ mode ++ "\n" ++
  "select-grow-failure: " ++ toString policy.base.selectGrowthFailure ++ "\n" ++
  "trap-grow-failure: " ++ toString policy.trapGrowthFailure

def parseOptCompatStage (name : String) : Except String CleanupStage :=
  match optCompatStages.find? (fun stage => stage.name == name) with
  | some stage => .ok stage
  | none => .error ("unsupported pass: " ++ name ++ "; use --print-passes")

def parseOptCompatPasses (names : String) : Except String (List CleanupStage) := do
  (names.splitOn ",").mapM parseOptCompatStage

def parseOptCompatMode : String → Except String Mode
  | "equivalence" => .ok .equivalence
  | "refinement" => .ok .refinement
  | "trap-insertion" => .ok .trapInsertion
  | other => .error ("unknown correctness mode: " ++ other)

def setOptCompatInput (state : OptCompatParseState) (path : String) :
    Except String OptCompatParseState :=
  if path.isEmpty then
    .error "an input path or - for stdin is required"
  else if state.input.isSome then
    .error "exactly one input file is supported"
  else
    .ok { state with input := some path }

def setOptCompatOutput (state : OptCompatParseState) (path : String) :
    Except String OptCompatParseState :=
  if path.isEmpty then
    .error "an output path or - for stdout is required"
  else if state.output.isSome then
    .error "output was specified more than once"
  else
    .ok { state with output := some path }

def finishOptCompatArgs (state : OptCompatParseState) : Except String OptCompatCommand := do
  if state.selectZeroGrowSuccess then zeroGrowOptionsCheck state.policy else state.policy.check
  if state.printPipeline then
    if state.selectZeroGrowSuccess then
      return .printZeroGrowPipeline state.stagesRev.reverse state.policy
    else
      return .printPipeline state.stagesRev.reverse state.policy
  let some input := state.input | .error ("missing input file\n" ++ optCompatUsage)
  let options := OptCompatOptions.mk input state.output state.stagesRev.reverse state.policy
  pure (if state.selectZeroGrowSuccess then .optimizeZeroGrow options else .optimize options)

def parseOptCompatFlags : List String → OptCompatParseState → Except String OptCompatCommand
  | [], state => finishOptCompatArgs state
  | "--all-features" :: rest, state
  | "-all" :: rest, state => parseOptCompatFlags rest state
  | ["--"], state => finishOptCompatArgs state
  | "--" :: input :: rest, state => do
      let state ← setOptCompatInput state input
      if rest.isEmpty then finishOptCompatArgs state
      else .error "exactly one input file is supported after --"
  | "-o" :: path :: rest, state
  | "--output" :: path :: rest, state => do
      let state ← setOptCompatOutput state path
      parseOptCompatFlags rest state
  | "--rounds" :: count :: rest, state => do
      let some rounds := count.toNat? | .error "--rounds requires a nonnegative integer"
      parseOptCompatFlags rest { state with policy.base.rounds := rounds }
  | "--mode" :: name :: rest, state => do
      let mode ← parseOptCompatMode name
      parseOptCompatFlags rest { state with policy.base.mode := mode }
  | "--passes" :: names :: rest, state => do
      let stages ← parseOptCompatPasses names
      parseOptCompatFlags rest { state with stagesRev := stages.reverse ++ state.stagesRev }
  | "--select-grow-failure" :: rest, state =>
      parseOptCompatFlags rest { state with policy.base.selectGrowthFailure := true }
  | "--trap-grow-failure" :: rest, state =>
      parseOptCompatFlags rest { state with policy.trapGrowthFailure := true }
  | "--select-zero-grow-success" :: rest, state =>
      parseOptCompatFlags rest { state with selectZeroGrowSuccess := true }
  | "--print-pipeline" :: rest, state =>
      parseOptCompatFlags rest { state with printPipeline := true }
  | "-" :: rest, state => do
      let state ← setOptCompatInput state "-"
      parseOptCompatFlags rest state
  | "--unverified" :: _, _ =>
      .error "--unverified is unavailable: no uncertified pass implementation registry exists"
  | flag :: rest, state => do
      if let some preset := parseOptCompatPreset flag then
        parseOptCompatFlags rest { state with stagesRev := preset.stages.reverse ++ state.stagesRev }
      else if let some path := flag.dropPrefix? "--output=" then
        let state ← setOptCompatOutput state path.toString
        parseOptCompatFlags rest state
      else if let some names := flag.dropPrefix? "--passes=" then
        let stages ← parseOptCompatPasses names.toString
        parseOptCompatFlags rest { state with stagesRev := stages.reverse ++ state.stagesRev }
      else if let some count := flag.dropPrefix? "--rounds=" then
        let some rounds := count.toString.toNat? | .error "--rounds requires a nonnegative integer"
        parseOptCompatFlags rest { state with policy.base.rounds := rounds }
      else if let some name := flag.dropPrefix? "--mode=" then
        let mode ← parseOptCompatMode name.toString
        parseOptCompatFlags rest { state with policy.base.mode := mode }
      else if let some stage := optCompatNamedStages.find? (fun stage => flag == "--" ++ stage.name) then
        parseOptCompatFlags rest { state with stagesRev := stage :: state.stagesRev }
      else if flag.startsWith "-O" then
        .error ("unsupported optimization level: " ++ flag ++ "; select implemented passes explicitly")
      else if flag.startsWith "-" then
        .error ("unsupported option: " ++ flag ++ "; use --help or --print-passes")
      else
        let state ← setOptCompatInput state flag
        parseOptCompatFlags rest state

/-- Input and output options may occur before, between or after pass selectors.
Every rejected command fails before any input/output file is opened. -/
def optCompatArgs (args : List String) : Except String OptCompatCommand :=
  parseOptCompatFlags args {}

/-- File IO glue for the selected certified optimizer; no output is opened
before the complete pure conversion succeeds. -/
def runOptCompat (args : List String) : IO UInt32 := do
  if args == ["--version"] then
    IO.println "Silmaril scoped Binaryen CLI compatibility (shape baseline: Binaryen version_133)"
    return 0
  if args == ["--help"] || args == ["-h"] then
    IO.println optCompatUsage
    return 0
  if args == ["--print-passes"] then
    IO.println optCompatPassList
    return 0
  if args == ["--print-presets"] then
    IO.println (String.intercalate "\n\n"
      ([.o0, .o1, .o2, .o3, .o4, .os, .oz].map CleanupPreset.report))
    return 0
  let command ← match optCompatArgs args with
    | .error error =>
      IO.eprintln error
      return 2
    | .ok command => pure command
  let (options, selectZeroGrowSuccess) ← match command with
    | .printPipeline stages policy =>
      IO.println (optCompatPipeline stages policy)
      return 0
    | .printZeroGrowPipeline stages policy =>
      IO.println (optCompatPipeline stages policy ++ "\nselect-zero-grow-success: true")
      return 0
    | .optimize options => pure (options, false)
    | .optimizeZeroGrow options => pure (options, true)
  try
    let input ← if options.input == "-" then (← IO.getStdin).readBinToEnd
      else IO.FS.readBinFile options.input
    let optimized := optimizeSelectedCompatBytes options.stages options.policy
      selectZeroGrowSuccess input
    match optimized with
    | .error error =>
      IO.eprintln error
      return 1
    | .ok artifact =>
      match options.output with
      | none => pure ()
      | some "-" => (← IO.getStdout).write artifact.bytes
      | some path => IO.FS.writeBinFile path artifact.bytes
      return 0
  catch error =>
    IO.eprintln s!"wasm-opt: {error}"
    return 1

end Silmaril.Wasm.Binaryen.Exe
