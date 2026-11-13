import WasmTools.GenCommon
import Silmaril.Wasm.Tools.Gen.Cmd.Shrink.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.Model.Defs
import Silmaril.Wasm.Perf.CoreDecode.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.Input.Defs

/-!
# `wasm-tools shrink` (gentool track)

Grammar `spec` (upstream 1.262.0's options) and the IO around the pure shrinker: the
candidates `Silmaril.Wasm.Tools.Gen.Cmd.Shrink.candidates` (valid in the model, strictly smaller)
are run by the generic API's `Shrinker.shrinkM` (`Silmaril.Wasm.Tools.Gen.API`) with the
predicate script as an `IO` predicate. In `Id` the loop is the API's `Shrinker.shrink`
(`shrinkM_id`), which keeps the predicate, validity (`Gen.Cmd.Inst.shrinkSh_validIn`, where
`Inst.shrinkSh S seed` is `Shrink.shrinker S seed`) and stops at a local minimum
(`shrink_local_min`); with a script those hold for the answers the script gave.

The input is binary or text (`Silmaril.Wasm.Tools.Gen.Cmd.Input.readModule`); every candidate is
written with the input's custom sections put back (`Sections.restore`).

As upstream: the predicate script must exist; it runs with the path of a temporary file
holding a candidate (status 0: interesting); the input must be interesting and (without
`--allow-empty`) the empty module must not be; each improvement prints
`N bytes (P% smaller)`; the result goes to `-o` (default: the input path with extension
`shrunken.wasm`, or `shrunken.wasm` for stdin), its text next to it with extension `wat`, and a
summary with the text is printed. `--attempts` bounds the number of consecutive uninteresting
candidates.
-/

namespace WasmTools.GenShrink

open Silmaril.Wasm.Tools.Gen.Cmd

def spec : Args.Spec where
  path := "wasm-tools shrink"
  positionals := [("<PREDICATE>", true), ("[INPUT]", false)]
  usage := "wasm-tools shrink [OPTIONS] <PREDICATE> [INPUT]"
  opts := [
    { long := "attempts", short := some 'a', kind := .ranged 4294967295, valName := "ATTEMPTS" },
    { long := "allow-empty" },
    { long := "seed", short := some 's', kind := .u64, valName := "SEED" },
    Args.outputOpt, Args.verboseOpt, Args.colorOpt]

/-- `(1 - new/old) · 100` with two decimals. -/
def pct (old new : Nat) : String :=
  if old = 0 then "0.00" else
  let r := ((old - new) * 1000000 / old + 50) / 100
  let f := r % 100
  s!"{r / 100}.{if f < 10 then "0" else ""}{f}"

/-- Rust's `Path::with_extension`. -/
def withExtension (p : String) (ext : String) : String :=
  let fp : System.FilePath := p
  (fp.withExtension ext).toString

/-- Run the predicate on bytes: its exit code, stdout and stderr. -/
def runPred (pred : String) (b : ByteArray) : IO (UInt32 × String × String) := do
  IO.FS.withTempFile fun h path => do
    h.write b; h.flush
    let out ← IO.Process.output { cmd := pred, args := #[path.toString] }
    return (out.exitCode, out.stdout, out.stderr)

/-- The diagnostic of a predicate run. -/
def predReport (head : String) (code : UInt32) (so se : String) : String :=
  s!"{head}predicate script exit status: exit status: {code}\n\n" ++
  s!"=== predicate script stdout ===\n{so}\n===============================\n\n" ++
  s!"=== predicate script stderr ===\n{se}\n==============================="

def rule : String := String.ofList (List.replicate 80 '=')

/-- What `shrink` reads from its command line. -/
structure ShrinkArgs where
  /-- `<PREDICATE>` -/
  predicate : String
  /-- `[INPUT]` (none or `-`: stdin) -/
  input : Option String
  /-- `-a, --attempts <ATTEMPTS>` (default 1000) -/
  attempts : Nat
  allowEmpty : Bool
  /-- `-s, --seed <SEED>` (default 42) -/
  seed : Nat
  /-- `-o, --output <OUTPUT>` (default: next to the input) -/
  output : Option String
  verbose : Nat
  deriving Repr, BEq

/-- The record of the typed values the specification's matches give (`GenCommon.ofMatches`). -/
def ShrinkArgs.ofParsed (p : Args.Parsed) : ShrinkArgs where
  predicate := p.pos.headD ""
  input := p.pos[1]?
  attempts := (p.num? "attempts").getD 1000
  allowEmpty := p.flag "allow-empty"
  seed := (p.num? "seed").getD 42
  output := p.str? "output"
  verbose := p.count "verbose"

/-- The body on its arguments (`run`: from the specification's matches). -/
def body (a : ShrinkArgs) : IO UInt32 := do
  let pred := a.predicate
  unless ← System.FilePath.pathExists pred do
    return ← GenCommon.fail s!"The predicate script '{pred}' does not exist."
  let inPath := a.input
  match ← GenCommon.readInput inPath (fun path => s!"failed to read from `{path}`") with
  | .error e => GenCommon.fail e
  | .ok input =>
    let S := Model.default
    let m ← match Input.readModule input with
      | .ok m => pure m
      | .error e =>
        let msg := if Input.isBinary input then
            match Silmaril.Wasm.Binary.Core.Decode.decodeModule input with
            | .error e => e
            | .ok _ => "malformed module"
          else e
        return ← GenCommon.fail (GenCommon.caused "The input is not valid Wasm." msg)
    let customs := Input.customs input
    let hint := if Input.isBinary input then input else .empty
    let encodeK (cand : Silmaril.Wasm.Module) : Except String ByteArray :=
      (GenCommon.encode hint cand).map (Sections.restore customs)
    unless Silmaril.Wasm.Tools.Gen.Core.featCheck S m do
      return ← GenCommon.fail (GenCommon.caused "The input is not valid Wasm."
        "the module is not valid in the default model")
    -- the input must be interesting
    let inputBin := if Input.isBinary input then input
      else match encodeK m with
        | .ok b => b
        | .error _ => input
    let (c, so, se) ← runPred pred inputBin
    if c != 0 then
      return ← GenCommon.fail (predReport
        "The predicate does not consider the input Wasm interesting: " c so se)
    if !a.allowEmpty then
      let empty : ByteArray := ⟨Smith.emptyBytes.toArray⟩
      let (c, so, se) ← runPred pred empty
      if c == 0 then
        return ← GenCommon.fail (predReport
          ("The predicate considers the empty Wasm module interesting, which is usually " ++
           "not desired and is a symptom of a bug in the predicate:\n\n") c so se)
    let attempts := a.attempts
    let seed := a.seed
    let allowEmpty := a.allowEmpty
    -- upstream parses text to binary first: sizes are relative to that binary
    let original := inputBin.size
    let failures ← IO.mkRef 0
    let out ← IO.getStdout
    let interesting (cand : Silmaril.Wasm.Module) : IO Bool := do
      if (← failures.get) ≥ attempts then return false
      if !allowEmpty && Shrink.msize cand == 0 then return false
      match encodeK cand with
      | .error _ => failures.modify (· + 1); return false
      | .ok b =>
        let (c, _, _) ← runPred pred b
        if c == 0 then
          failures.set 0
          out.putStrLn s!"{b.size} bytes ({pct original b.size}% smaller)"
          out.flush
          return true
        failures.modify (· + 1)
        return false
    let sh := Shrink.shrinker S seed
    let res ← sh.shrinkM interesting (Shrink.msize m + 1) m
    let bytes ← match encodeK res with
      | .ok b => pure b
      | .error e => return ← GenCommon.fail s!"failed to encode the shrunken module: {e}"
    let outPath := match a.output with
      | some o => o
      | none => match inPath with
        | none | some "-" => "shrunken.wasm"
        | some i => withExtension i "shrunken.wasm"
    match ← GenCommon.writeBytes (some outPath) bytes with
    | .error e => return ← GenCommon.fail e
    | .ok () => pure ()
    let text := match GenCommon.printText res with
      | .ok s => s
      | .error e => s!";; {e}\n"
    match ← GenCommon.writeText (some (withExtension outPath "wat")) text with
    | .error e => return ← GenCommon.fail e
    | .ok () => pure ()
    out.putStr s!"\n{outPath} :: {bytes.size} bytes ({pct original bytes.size}% smaller)\n"
    out.putStr s!"{rule}\n{text}{rule}\n"
    return 0

/-- Run on the specification's matches (`GenCommon.runMatches`). -/
def run (m : Silmaril.Cli.Matches) : IO UInt32 :=
  GenCommon.runMatches spec (fun p => body (ShrinkArgs.ofParsed p)) m

end WasmTools.GenShrink
