import Silmaril.Cerberus.Codec.WellFormed.Defs
import Silmaril.Cerberus.Core.Startup.Defs
import Silmaril.Cerberus.Core.Outcome.Defs
import Silmaril.Compiler.Category.Cerberus.Process.Thms

/-! Execute genuine pinned Cerberus Core exports through the imported Core LTS.
This is differential regression evidence. `Run.trace` is a kernel-checked trace
construction; executing this test is not a proof of C elaboration equivalence,
all scheduling choices, or native compilation correctness.

Usage: `lake env lean --run tests/cerberus/GenuineOracle.lean EXPORT_DIRECTORY`
where each fixture contains `core.sexp` (or `core.sexp.gz`) and `oracle.json`.
-/

#print axioms Silmaril.Cerberus.Core.Dynamics.runWith_ending
#print axioms Silmaril.Compiler.Category.Cerberus.Process.coreBeh_of_run_exit
#print axioms Silmaril.Compiler.Category.Cerberus.Process.coreBeh_of_run_abort
#print axioms Silmaril.Compiler.Category.Cerberus.Process.coreUB_of_run_undefined

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics

private def compare (directory : System.FilePath) (name : String) : IO Unit := do
  let source := directory / name
  let text ← if ← (source / "core.sexp").pathExists then
      IO.FS.readFile (source / "core.sexp")
    else do
      let result ← IO.Process.output { cmd := "gzip", args := #["-dc", (source / "core.sexp.gz").toString] }
      unless result.exitCode == 0 do
        throw <| IO.userError s!"{name}: fixture decompression failed: {result.stderr}"
      pure result.stdout
  let before ← IO.monoMsNow
  let document ← match Codec.WellFormed.parseDocument text with
    | .ok document => pure document
    | .error error => throw <| IO.userError s!"{name}: document decoding failed: {repr error}"
  let decoded ← IO.monoMsNow
  let (initial, labels) ← match initial document.file
      (Map.ofList (document.enumBindings.getD [])) (Core.Startup.execArguments []) with
    | .ok result => pure result
    | .error why => throw <| IO.userError s!"{name}: Core startup failed: {(observation (some why)).json.compress}"
  let execution := run document.file labels 100000 initial
  let actual := (runObservation execution).json
  let executed ← IO.monoMsNow
  let expectedText ← IO.FS.readFile (source / "oracle.json")
  let expected ← match Lean.Json.parse expectedText with
    | .ok value => pure value
    | .error why => throw <| IO.userError s!"{name}: malformed oracle observation: {why}"
  unless actual == expected do
    throw <| IO.userError s!"{name}: Core/oracle mismatch\nexpected {expected.compress}\nactual {actual.compress}"
  IO.println s!"{name}: agreed; decode={decoded - before}ms, run={executed - decoded}ms, transitions={execution.actions.length}"

def main (args : List String) : IO UInt32 := do
  let [directory] := args
    | throw <| IO.userError "expected genuine pinned exporter output directory"
  for name in ["constant-return", "arithmetic", "control-flow", "enum-return", "parameter-unused", "call-zeroarg", "global-integer", "global-independent",
      "global-pointer-null", "global-pointer-zero", "global-pointer-void-null",
      "cast-narrow", "cast-sign-extend", "cast-nested",
      "call-id", "call-two", "call-narrow", "call-nested"] do
    compare directory name
  return 0
