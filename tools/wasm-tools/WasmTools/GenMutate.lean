import WasmTools.GenCommon
import Silmaril.Wasm.Tools.Gen.Cmd.Mutate.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.Model.Defs
import Silmaril.Wasm.Perf.CoreDecode.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.Input.Defs

/-!
# `wasm-tools mutate` (gentool track)

Grammar `spec` (upstream 1.262.0's options), and a thin body: read the input, binary or text
(`Silmaril.Wasm.Tools.Gen.Cmd.Input.readModule`, sound: `Input.Thms.readModule_sound`), check
it is valid in the default model, run the pure mutation `Silmaril.Wasm.Tools.Gen.Cmd.Mutate.mutate`
(output valid: `Mutate.Thms.mutate_validIn`; with `--preserve-semantics` observationally
equivalent to the input: `Equiv.Thms.mutate_preserve_equiv`), and write the encoding
(`Silmaril.Wasm.Binaryen.Exe.encodeModule`, sound) with the input's custom sections put back
(`Sections.restore`, `Sections.Thms.restore_spec`), or its text (`-t`).

Upstream's statuses: a malformed or invalid input prints `Failed to parse the input Wasm
module.` (status 2); no applicable mutation prints `There are not applicable mutations for the
input Wasm module.` (status 3). `--fuel` is accepted and has no effect (every mutation here is bounded).
-/

namespace WasmTools.GenMutate

open Silmaril.Wasm.Tools.Gen.Cmd

def spec : Args.Spec where
  path := "wasm-tools mutate"
  positionals := [("[INPUT]", false)]
  usage := "wasm-tools mutate [OPTIONS] [INPUT]"
  opts := [Args.outputOpt, Args.verboseOpt, Args.colorOpt, Args.watOpt,
    { long := "seed", short := some 's', kind := .u64, valName := "SEED" },
    { long := "preserve-semantics" },
    { long := "fuel", short := some 'f', kind := .u64, valName := "FUEL" },
    { long := "reduce" }]

/-- What `mutate` reads from its command line. -/
structure MutateArgs where
  /-- `[INPUT]` (none or `-`: stdin) -/
  input : Option String
  /-- `-o, --output <OUTPUT>` -/
  output : Option String
  /-- `-t, --wat` -/
  wat : Bool
  /-- `-s, --seed <SEED>` (default 42) -/
  seed : Nat
  preserveSemantics : Bool
  reduce : Bool
  /-- `-f, --fuel <FUEL>` (accepted, without effect) -/
  fuel : Option Nat
  verbose : Nat
  deriving Repr, BEq

/-- The record of the typed values the specification's matches give (`GenCommon.ofMatches`). -/
def MutateArgs.ofParsed (p : Args.Parsed) : MutateArgs where
  input := p.pos.head?
  output := p.str? "output"
  wat := p.flag "wat"
  seed := (p.num? "seed").getD 42
  preserveSemantics := p.flag "preserve-semantics"
  reduce := p.flag "reduce"
  fuel := p.num? "fuel"
  verbose := p.count "verbose"

/-- The body on its arguments (`run`: from the specification's matches). -/
def body (a : MutateArgs) : IO UInt32 := do
  match ← GenCommon.readInput a.input (fun path => s!"failed to read from `{path}`") with
  | .error e => GenCommon.fail e
  | .ok input =>
    let S := Model.default
    -- upstream parses text first (`wat::parse_bytes`): a text error is `error: …`, status 1
    -- read once: the text reader is the expensive part on large text inputs
    let read := Input.readModule input
    if !Input.isBinary input then
      if let .error e := read then
        return ← GenCommon.fail e
    let parsed := match read with
      | .ok m => if Silmaril.Wasm.Tools.Gen.Core.featCheck S m then some m else none
      | .error _ => none
    match parsed with
    | none =>
      (← IO.getStderr).putStr "Failed to parse the input Wasm module.\n"
      return 2
    | some m =>
      let o : Mutate.Opts := { preserveSemantics := a.preserveSemantics, reduce := a.reduce }
      let seed := a.seed.toUInt64
      match Mutate.mutate S {} o seed m with
      | none =>
        (← IO.getStderr).putStr "There are not applicable mutations for the input Wasm module.\n"
        return 3
      | some m' =>
        let hint := if Input.isBinary input then input else .empty
        match GenCommon.encode hint m' with
        | .error e => GenCommon.fail s!"failed to encode the mutated module: {e}"
        | .ok b =>
          let customs := Input.customs input
          let out := Sections.restore customs b
          if a.wat then
            let text := if customs.isEmpty then GenCommon.printText m' else
              match Print.printModuleC? m'
                  (Sections.printAnchors out) with
              | some s => .ok s
              | none => .error ("the custom sections of this module are outside the " ++
                  "printer of this wasm-tools (see docs/projects/wasm-components.md, Known limitations)")
            match text with
            | .error e => GenCommon.fail e
            | .ok s =>
              match ← GenCommon.writeText a.output s with
              | .error e => GenCommon.fail e
              | .ok () => return 0
          else
            match ← GenCommon.writeBytes a.output out with
            | .error e => GenCommon.fail e
            | .ok () => return 0

/-- Run on the specification's matches (`GenCommon.runMatches`). -/
def run (m : Silmaril.Cli.Matches) : IO UInt32 :=
  GenCommon.runMatches spec (fun p => body (MutateArgs.ofParsed p)) m

end WasmTools.GenMutate
