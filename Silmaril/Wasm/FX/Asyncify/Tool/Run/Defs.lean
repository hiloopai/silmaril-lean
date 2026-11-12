module

public import Silmaril.Wasm.FX.Asyncify.Tool.Sys.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# The core of `wasm-asyncify`: bytes, and runs of the model for differential tests

* `asyncifyBytes`: decode with silmaril-lean's `Binary.Core.decode?`, run the pass `asyncify`,
  encode with `Binaryen.Exe.encodeModule?` (theorems in `Silmaril.Wasm.FX.Asyncify.Tool.Thms`).
* `envOfLax`, `globalsOfLax`: read any module's function imports and `i32` functions (and
  constant `i32` globals) into the machine, for running the *output* binary in the model.
* `testHost`: the deterministic host of the differential suite (also implemented in
  `tools/wasm-asyncify/differential.mjs`): the answer `j` to the `c`-th call (from 0) of import
  `f` with arguments `as` is `31 · Σ as + 7 f + 1000 c + j`; the state logs the calls.
* `runSrc`, `runTgt`: run the source or target system for at most `fuel` steps.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- Decode, asyncify, encode. -/
def asyncifyBytes (b : ByteArray) (pages : Nat := 1) : Except String ByteArray :=
  match Binary.Core.decode? b with
  | none => .error "the input does not decode as a Core module"
  | some m =>
    match asyncify m pages with
    | .error e => .error e
    | .ok m' =>
      match Binaryen.Exe.encodeModule? m' with
      | .ok bs => .ok ⟨bs.toArray⟩
      | .error e => .error s!"encoding failed: {e}"

/-- A function import. -/
def isFuncImport (im : Import) : Bool :=
  match im.type with
  | .func _ => true
  | _ => false

/-- Function imports and `i32` functions of any module (other sections are ignored). -/
def envOfLax (m : Module) : Option Env :=
  match (m.imports.filter isFuncImport).mapM (impSig m), m.funcs.mapM (fnDefOf m) with
  | some imps, some fns => some ⟨imps, fns⟩
  | _, _ => none

/-- Initial values of globals initialised by one `i32.const`. -/
def globalsOfLax (m : Module) : Option (List W) :=
  m.globals.mapM fun g => match g.init with
    | [.intConst .i32 b] => some b
    | _ => none

/-- The host state of the differential suite: the calls so far (import, arguments, answers). -/
abbrev TestLog := List (Nat × List W × List W)

/-- The host of the differential suite. Answers are padded or cut to the result count by the
systems; `testHost` answers 4 words. -/
def testHost : Host TestLog where
  answer log f as :=
    let ans := (List.range 4).map fun j =>
      BitVec.ofNat 32 (31 * (as.map BitVec.toNat).sum + 7 * f + 1000 * log.length + j)
    (log ++ [(f, as, ans)], ans)

/-- The index of an exported function. -/
def exportFunc (m : Module) (name : String) : Option Nat :=
  m.exports.findSome? fun e => if e.name == name then
    match e.index with
    | .func f => some f.value.val
    | _ => none
  else none

/-- Run a closed system for at most `fuel` steps; `none` if it is still running. -/
def runFuel {X σ : Type} (step : X → SRes X σ) : Nat → X → Option (Obs σ)
  | 0, _ => none
  | n + 1, x =>
    match step x with
    | .next x' => runFuel step n x'
    | .stop o => some o

/-- Run export `name` of a source module in the source system. -/
def runSrc (m : Module) (name : String) (args : List W) (fuel : Nat) :
    Except String (Option (Obs TestLog)) := do
  let some E := envOfLax m | throw "the module is outside the i32 function fragment"
  let some e := exportFunc m name | throw s!"no exported function {name}"
  let some c := srcInit E e args | throw "the export is not a defined function"
  pure (runFuel (srcStep E testHost) fuel (c, []))

/-- Run export `name` of an asyncified module in the target system. -/
def runTgt (m : Module) (name : String) (args : List W) (fuel : Nat) :
    Except String (Option (Obs TestLog)) := do
  let some E := envOfLax m | throw "the module is outside the i32 function fragment"
  let some gs := globalsOfLax m | throw "the globals are not i32 constants"
  let some e := exportFunc m name | throw s!"no exported function {name}"
  let some c := srcInit E e args | throw "the export is not a defined function"
  pure (runFuel (tgtStep E testHost) fuel ⟨{ c with globals := gs }, [], e, args⟩)

/-- A word as an unsigned decimal. -/
def showW (w : W) : String := toString w.toNat

/-- Print an outcome on one line (the JSON format of the differential suite). -/
def showObs : Option (Obs TestLog) → String
  | none => "{\"outcome\":\"fuel\"}"
  | some .diverges => "{\"outcome\":\"diverges\"}"
  | some (.trap log) => "{\"outcome\":\"trap\",\"log\":" ++ showLog log ++ "}"
  | some (.done vs log) =>
    "{\"outcome\":\"done\",\"results\":" ++ showWs vs.reverse ++ ",\"log\":" ++ showLog log ++ "}"
where
  showWs (ws : List W) : String := "[" ++ ",".intercalate (ws.map showW) ++ "]"
  showLog (log : TestLog) : String :=
    "[" ++ ",".intercalate (log.map fun (f, as, ans) =>
      "{\"import\":" ++ toString f ++ ",\"args\":" ++ showWs as ++ ",\"answers\":" ++
        showWs ans ++ "}") ++ "]"

end Silmaril.Wasm.FX.Asyncify.Tool
