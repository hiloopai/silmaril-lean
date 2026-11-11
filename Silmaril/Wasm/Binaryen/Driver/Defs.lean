module

public import Silmaril.Wasm.Binaryen.Pipeline.Defs
public import Silmaril.Wasm.Binaryen.Exe.OptCompatMain
public import Silmaril.Wasm.Binaryen.Coverage.Defs

@[expose] public section

/-! # `wasm-opt`: command line

The `wasm-opt` executable (`tools/wasm-opt/WasmOptCompatLean.lean`) runs
`runExtraOpt`. Without any verified-stage option the whole command line is handed
to silmaril's `Exe.runOptCompat` unchanged, so the tool is a drop-in superset of
silmaril's `wasm-opt`. Verified-stage options:

* `--verified-stages`: `-O*` presets expand to verified-stage schedules (`extraSchedule`:
  silmaril's restricted schedule plus the verified stages after each `optimize-instructions` slot);
  with no other selection, `--verified-stages` alone selects the verified-stage `-O2` schedule;
* `--neutral-ops`, `--eqz-pair`, `--rse-line`, `--drop-get`, `--tee-form` (every
  `ExtraStageId` name), also inside `--passes`;
* `--stats`: report sizes, the certified profile class, and how often each stage
  changed the module (an unverified replay used for reporting only);
* `--component`: reserved for a component-model mode (see below); rejected.

On the verified-stages path every stage runs in exact-equivalence mode
(`extraSelectedCompatBytes`, certified by `extraSelectedCompatBytes_sound_exact` at
every numerical profile for every selection, `ssa` included: every verified stage is an
every-profile stage); silmaril's growth-policy flags (`--mode`,
`--*-grow-*`) are available only on the delegated path and are rejected here.

**The SSA stage (`--ssa`, `ssa` in `--passes`).** Opt-in and never part of a
preset. It runs `SsaStage.ssaRun`: the Wasm lambda-SSA optimiser of
`Silmaril.Wasm.SSA` on every function in its fragment, each replacement export-certified at run
time (`SSA.optimizeFuncExport`: `SSA.optimizeFuncLocal`, `SSA.runCert`, strict leaf source and
result). Its certificate class is `StageCert.anyProfile`: exact export equivalence at every
numerical profile under the closed host (`SsaStage.ssaRun_exportEquiv`, through the
caller-side simulation `SSA.behaviours_srel`), so `extraSelectedCompatBytes_sound(_exact,
_det)` cover selections containing it; `--ssa` alone also has `ssaOnlyCompatBytes_sound`
(export equivalence plus, per rewritten function, fragment equivalence and equal Core 3.0
behaviours of its invocations in the allocated stores). The run-time checks need a module
without imports (modules with imports are returned unchanged); only the rewritten functions
themselves must be store-free integer code. `--stats` lists per function whether it was in
the fragment, rewritten, or rewritable only without the export certificate. Follow `--ssa` with cleanup stages (e.g. `-O2`, `--tee-form`,
`--rse-line`, `--drop-get`, `--vacuum`) to remove the out-of-SSA locals and blocks;
the cleanup stages keep their own certificates.

**Extension points.** New function-level stages are registered in
`Silmaril.Wasm.Binaryen.Pipeline` (`ExtraStageId`) and become selectable here by name
automatically. A component mode is reserved as `InputKind.component`: a future
component optimiser supplies a byte endpoint and its certificate and replaces the
rejection in `runExtraPlan`.
-/

namespace Silmaril.Wasm.Binaryen.Driver

open Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.Exe Silmaril.Wasm.Binaryen.Pipeline

/-- The kind of input the optimiser runs on. Only core modules are implemented. -/
inductive InputKind where
  | core
  | component
  deriving DecidableEq, Repr

/-- A selection item; presets are expanded once `--verified-stages` is known. -/
inductive Item where
  | stage (stage : ExtraStage)
  | preset (preset : CleanupPreset)
  deriving Repr

structure Plan where
  input : Option String := none
  output : Option String := none
  itemsRev : List Item := []
  rounds : Nat := 1
  verifiedStages : Bool := false
  stats : Bool := false
  printPipeline : Bool := false
  kind : InputKind := .core

/-- Every selectable name: silmaril's named stages and local subrules, then the verified stages. -/
def selectableStages : List ExtraStage :=
  optCompatStages.map .silmaril ++ extraStageIds.map .verified ++ [.ssa]

def extraOnlyFlag (arg : String) : Bool :=
  arg == "--verified-stages" || arg == "--stats" || arg == "--component" || arg == "--ssa" ||
    (arg.splitOn ",").any (· == "ssa") ||
    ((arg.dropPrefix? "--passes=").map (·.toString)).any (fun n => (n.splitOn ",").any (· == "ssa")) ||
    extraStageIds.any (fun s => arg == "--" ++ s.name) ||
    extraStageIds.any (fun s => (arg.splitOn ",").any (· == s.name)) ||
    extraStageIds.any (fun s => ((arg.dropPrefix? "--passes=").map (·.toString)).any
      (fun names => (names.splitOn ",").any (· == s.name)))

/-- Use the verified-stage driver only when some verified-stage option is present. -/
def usesVerifiedStages (args : List String) : Bool := args.any extraOnlyFlag

def parseStage (name : String) : Except String ExtraStage :=
  match selectableStages.find? (fun stage => stage.name == name) with
  | some stage => .ok stage
  | none => .error ("unsupported pass: " ++ name ++ "; use --print-passes")

def parsePasses (names : String) : Except String (List ExtraStage) :=
  (names.splitOn ",").mapM parseStage

def setInput (plan : Plan) (path : String) : Except String Plan :=
  if path.isEmpty then .error "an input path or - for stdin is required"
  else if plan.input.isSome then .error "exactly one input file is supported"
  else .ok { plan with input := some path }

def setOutput (plan : Plan) (path : String) : Except String Plan :=
  if path.isEmpty then .error "an output path or - for stdout is required"
  else if plan.output.isSome then .error "output was specified more than once"
  else .ok { plan with output := some path }

def namedFlag? (flag : String) : Option ExtraStage :=
  (optCompatNamedStages.map ExtraStage.silmaril ++ extraStageIds.map ExtraStage.verified ++
    [ExtraStage.ssa]).find?
    fun stage => flag == "--" ++ stage.name

def parseArgs : List String → Plan → Except String Plan
  | [], plan => .ok plan
  | "--all-features" :: rest, plan | "-all" :: rest, plan => parseArgs rest plan
  | "--verified-stages" :: rest, plan => parseArgs rest { plan with verifiedStages := true }
  | "--stats" :: rest, plan => parseArgs rest { plan with stats := true }
  | "--component" :: rest, plan => parseArgs rest { plan with kind := .component }
  | "--print-pipeline" :: rest, plan => parseArgs rest { plan with printPipeline := true }
  | "-o" :: path :: rest, plan | "--output" :: path :: rest, plan => do
      parseArgs rest (← setOutput plan path)
  | "--rounds" :: count :: rest, plan => do
      let some rounds := count.toNat? | .error "--rounds requires a nonnegative integer"
      parseArgs rest { plan with rounds := rounds }
  | "--passes" :: names :: rest, plan => do
      let stages ← parsePasses names
      parseArgs rest { plan with itemsRev := (stages.map Item.stage).reverse ++ plan.itemsRev }
  | "-" :: rest, plan => do parseArgs rest (← setInput plan "-")
  | flag :: rest, plan => do
      if let some preset := parseOptCompatPreset flag then
        parseArgs rest { plan with itemsRev := .preset preset :: plan.itemsRev }
      else if let some path := flag.dropPrefix? "--output=" then
        parseArgs rest (← setOutput plan path.toString)
      else if let some names := flag.dropPrefix? "--passes=" then
        let stages ← parsePasses names.toString
        parseArgs rest { plan with itemsRev := (stages.map Item.stage).reverse ++ plan.itemsRev }
      else if let some count := flag.dropPrefix? "--rounds=" then
        let some rounds := count.toString.toNat? | .error "--rounds requires a nonnegative integer"
        parseArgs rest { plan with rounds := rounds }
      else if let some stage := namedFlag? flag then
        parseArgs rest { plan with itemsRev := .stage stage :: plan.itemsRev }
      else if flag.startsWith "-" then
        .error ("unsupported option on the verified-stages path: " ++ flag ++
          "; growth policies and modes are available without verified-stage options")
      else parseArgs rest (← setInput plan flag)

/-- Expand the selection; presets follow `--verified-stages`. -/
def Plan.stages (plan : Plan) : List ExtraStage :=
  let items := plan.itemsRev.reverse
  let items := if plan.verifiedStages && items.isEmpty then [Item.preset .o2] else items
  items.flatMap fun
    | .stage stage => [stage]
    | .preset preset =>
      if plan.verifiedStages then extraPresetStages preset else preset.stages.map .silmaril

def passList : String :=
  optCompatPassList ++ "\nVerified stages (exact equivalence at every numerical profile):\n" ++
    String.intercalate "\n" (extraStageIds.map fun s =>
      "  --" ++ s.name ++ "  (restricted " ++ s.upstream ++ " subrule)")

def usage : String :=
  "usage: wasm-opt [OPTIONS] IN.wasm [-o OUT.wasm]\n" ++
  "Without verified-stage options this is silmaril's wasm-opt; see wasm-opt --help-silmaril.\n" ++
  "Verified-stage options:\n" ++
  "  --verified-stages   -O* presets use verified-stage schedules; alone, selects the -O2 one\n" ++
  "  --neutral-ops       append the verified neutral-operand stage (also in --passes)\n" ++
  "  --eqz-pair          append the verified double-eqz stage (also in --passes)\n" ++
  "  --rse-line          append silmaril's self-store elimination, proved here (also in --passes)\n" ++
  "  --drop-get          append the verified dropped-local-read stage (also in --passes)\n" ++
  "  --tee-form          append the verified set/get-to-tee stage (also in --passes)\n" ++
  "  --ssa               append the lambda-SSA optimiser (opt-in; export-equivalence certificate,\n" ++
  "                      never in a preset; also `ssa` in --passes)\n" ++
  "  --stats             report sizes and per-stage firing counts on stderr\n" ++
  "  --component         reserved for a component-model mode (not implemented)\n" ++
  "  --print-pipeline    print the expanded stage list without file IO\n" ++
  "  --print-verified-presets  print the verified-stage schedules\n" ++
  "  --print-coverage    print Binaryen pass coverage (silmaril / verified stages / none)\n" ++
  "Also accepted on the verified-stages path: --PASS, --passes, -O*, --rounds, -o/--output, -, -all."

def extraPresets : List CleanupPreset := [.o1, .o2, .o3, .o4, .os, .oz]

/-! ## `--stats`: per-stage firing counts

A separate, unverified replay of the same stage sequence for reporting only; the
written output is always the certified `extraSelectedCompatBytes` result. -/

structure StageStat where
  name : String
  applied : Nat := 0
  changed : Nat := 0
  saved : Int := 0

def encodedSize (m : BModule) : Nat :=
  match encodeModule? m.lower with
  | .ok bs => bs.length
  | .error _ => 0

def recordStat (stats : List StageStat) (name : String) (before after : Nat) : List StageStat :=
  let delta : Nat := if before != after then 1 else 0
  let saved : Int := (before : Int) - (after : Int)
  let upd (s : StageStat) : StageStat :=
    ⟨s.name, s.applied + 1, s.changed + delta, s.saved + saved⟩
  if stats.any (·.name == name) then stats.map fun s => if s.name == name then upd s else s
  else stats ++ [upd ⟨name, 0, 0, 0⟩]

def stageStats (stages : List ExtraStage) (rounds : Nat) (input : ByteArray) :
    Except String (List StageStat × List String) := do
  let prepared ← CompactInput.prepare input
  let source ← (Silmaril.Wasm.Binary.Core.Decode.decodeModule prepared.bytes).mapError ("stats: " ++ ·)
  let mut m := (checkedLift source).1
  let mut stats : List StageStat := []
  let mut size := encodedSize m
  let mut ssaLines : List String := []
  for r in List.range rounds do
    for stage in stages do
      if stage == .ssa then
        let rewritten := SsaStage.ssaReport m
        let lines := rewritten.map fun (g, ok) =>
          s!"  ssa iteration {r + 1} func {g}: " ++
            (if !SsaStage.inFragment m g then "outside the fragment"
             else if ok then "in the fragment, rewritten (export-certified)"
             else if SsaStage.fragRewritable m g then
               "in the fragment, not rewritten (no export certificate: imports, not a strict leaf, or checks failed)"
             else "in the fragment, not rewritten (out-of-SSA or validation failed)")
        let fallback := if rewritten.any (·.2) && !SsaStage.ssaAccept m { m with funcs := SsaStage.ssaFuncs m } then
            ["  ssa: combined module failed the Core checks; input kept"] else []
        ssaLines := ssaLines ++ lines ++ fallback
      let m' := stage.runValid m
      let size' := encodedSize m'
      stats := recordStat stats stage.name size size'
      m := m'
      size := size'
  pure (stats, ssaLines)

def runExtraPlan (plan : Plan) : IO UInt32 := do
  if plan.kind == .component then
    IO.eprintln "wasm-opt: --component is reserved; no component-model optimiser is registered"
    return 2
  let stages := plan.stages
  if plan.printPipeline then
    IO.println ("verified-stage pipeline; no files read or written.\npasses: " ++
      String.intercalate "," (stages.map ExtraStage.name) ++ "\nrounds: " ++ toString plan.rounds)
    return 0
  let some inputPath := plan.input | do IO.eprintln ("missing input file\n" ++ usage); return 2
  try
    let input ← if inputPath == "-" then (← IO.getStdin).readBinToEnd
      else IO.FS.readBinFile inputPath
    match extraSelectedCompatBytes stages plan.rounds input with
    | .error error =>
      IO.eprintln error
      return 1
    | .ok artifact =>
      if plan.stats then
        IO.eprintln s!"wasm-opt: {stages.length} stages x {plan.rounds} rounds; input {input.size} bytes, output {artifact.bytes.size} bytes"
        let cert := if !stages.all ExtraStage.exact then
            "output validity"
          else if stages.all ExtraStage.anyProfile then
            "exact export equivalence at every numerical profile"
          else "exact export equivalence at every deterministic profile"
        IO.eprintln s!"wasm-opt: certified: {cert}"
        match stageStats stages plan.rounds input with
        | .error e => IO.eprintln s!"wasm-opt: stats unavailable: {e}"
        | .ok (stats, ssaLines) =>
          for l in ssaLines do IO.eprintln l
          for st in stats do
            if st.changed > 0 then
              IO.eprintln s!"  {st.name}: changed the module in {st.changed}/{st.applied} applications, {st.saved} bytes"
      match plan.output with
      | none => pure ()
      | some "-" => (← IO.getStdout).write artifact.bytes
      | some path => IO.FS.writeBinFile path artifact.bytes
      return 0
  catch error =>
    IO.eprintln s!"wasm-opt: {error}"
    return 1

/-- The `wasm-opt` entry point. -/
def runExtraOpt (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] then
    IO.println usage
    return 0
  if args == ["--help-silmaril"] then
    IO.println optCompatUsage
    return 0
  if args == ["--version"] then
    IO.println "wasm-opt (silmaril scoped Binaryen CLI + verified stages)"
    return 0
  if args == ["--print-passes"] then
    IO.println passList
    return 0
  if args == ["--print-coverage"] then
    IO.println Coverage.report
    return 0
  if args == ["--print-verified-presets"] then
    IO.println (String.intercalate "\n\n" (extraPresets.map extraPresetReport))
    return 0
  if !usesVerifiedStages args then
    return ← runOptCompat args
  match parseArgs args {} with
  | .error error =>
    IO.eprintln error
    return 2
  | .ok plan => runExtraPlan plan

end Silmaril.Wasm.Binaryen.Driver
