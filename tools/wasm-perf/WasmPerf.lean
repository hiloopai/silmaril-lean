import Silmaril.Wasm.Perf.CoreDecode.Defs
import Silmaril.Wasm.Perf.WatPrint.Defs
import Silmaril.Wasm.Perf.WatRead.Defs
import Silmaril.Wasm.Perf.WatReadB.Defs
import Silmaril.Wasm.Wit.Tool.Defs
import Silmaril.Wasm.JcoTool.Front.Defs
import Silmaril.Wasm.JcoTool.StreamSem.Defs
import Silmaril.Wasm.Perf.JcoMain.Defs
import Silmaril.Wasm.Perf.ValidateR.Defs
import Silmaril.Wasm.JcoTool.Adapt.Defs
import Silmaril.Wasm.Validation.Check.Validate

/-!
# `wasm-perf`

Micro-benchmarks of the specification functions and their fast implementations, for
`tools/wasm-perf/tests/bench.sh`. Each command runs one function on a file and prints a
digest of the result, so that the work is not optimised away and the two implementations can
be compared.

```
wasm-perf decode-core spec|fast CORE.wasm   silmaril's decode? or CoreDecode.decodeF
wasm-perf print-wat spec|fast COMP.wasm     Wat.print or WatPrint.printF of the parsed component
wasm-perf parse-wat spec|fast|bytes COMP.wat  Wit.Tool.parseWat, WatRead.parseWatF or WatReadB.parseWatB
```
-/

def digestModule : Option Silmaril.Wasm.Module → String
  | none => "none"
  | some m => s!"funcs {m.funcs.length} imports {m.imports.length} exports {m.exports.length}"

/-- Time one pure computation (forced inside a thunk) and print its digest. -/
def phase {α : Type} (label : String) (f : Unit → α) (dig : α → String) : IO α := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0) / 1000000} ms ({dig a})"
  pure a

def exceptDig {α : Type} : Except String α → String
  | .ok _ => "ok"
  | .error e => s!"error {(e.take 80).toString}"

/-- The phases of `wasm-jco new` on a core module (no `--wit`), each timed on its own. -/
def phases (f : String) : IO UInt32 := do
  let b ← IO.FS.readBinFile f
  let dm ← phase "decodeF" (fun _ => Silmaril.Wasm.Perf.CoreDecode.decodeF b) digestModule
  let _ ← phase "validateR" (fun _ => dm.bind Silmaril.Wasm.Perf.ValidateR.validateR)
    (fun r => if r.isSome then "valid" else "invalid")
  let wf ← phase "worldFullOf" (fun _ => Silmaril.Wasm.JcoTool.Front.worldFullOf b none) exceptDig
  let some wf := wf.toOption | pure 1
  IO.println s!"inOld: {Silmaril.Wasm.JcoTool.ToolI.inOld wf.world}"
  let core' ← phase "prepareCore" (fun _ => Silmaril.Wasm.JcoTool.Front.prepareCore b) exceptDig
  let some core' := core'.toOption | pure 1
  let p ← phase "planF" (fun _ => Silmaril.Wasm.Perf.JcoNew.planF core' wf) exceptDig
  let some p := p.toOption | pure 1
  let o ← phase "newIP" (fun _ => Silmaril.Wasm.Perf.JcoNew.newIP p) exceptDig
  let some o := o.toOption | pure 1
  let _ ← phase "helpersOk" (fun _ => Silmaril.Wasm.JcoTool.Helpers.helpersOk o) toString
  let _ ← phase "checkLayoutP" (fun _ => Silmaril.Wasm.Perf.JcoNew.checkLayoutP p o) exceptDig
  let _ ← phase "refOf" (fun _ => Silmaril.Wasm.JcoTool.ToolV.refOf o) exceptDig
  let _ ← phase "refCheckLine" (fun _ => Silmaril.Wasm.JcoTool.ToolV.refCheckLine o.bytes) (fun s => (s.take 30).toString)
  let _ ← phase "refCheckX" (fun _ => Silmaril.Wasm.JcoTool.ToolV.refCheckX o.bytes) exceptDig
  let _ ← phase "report" (fun _ => Silmaril.Wasm.JcoTool.StreamSem.report b wf.world) (·.length.repr)
  let _ ← phase "newValid (all)" (fun _ => Silmaril.Wasm.JcoTool.Front.newValid b wf) exceptDig
  pure 0

/-- The phases of `wasm-jco new`'s default mode (no `--wit`), as the tool runs them. -/
def phasesDefault (f : String) : IO UInt32 := do
  let b ← IO.FS.readBinFile f
  let d₀ ← phase "decodeF" (fun _ => Silmaril.Wasm.Perf.CoreDecode.decodeF b) digestModule
  let _ ← phase "needsGeneralOf" (fun _ => Silmaril.Wasm.JcoTool.Adapt.needsGeneralOf d₀ b) toString
  let s ← phase "newStage1D" (fun _ => Silmaril.Wasm.Perf.JcoMain.newStage1D b d₀ none) exceptDig
  let some (wf, _, core', d') := s.toOption | pure 1
  let dm ← phase "pick (decode of the prepared module)" (fun _ => Silmaril.Wasm.Perf.JcoMain.pick d' core') digestModule
  let dec := Silmaril.Wasm.Perf.JcoMain.memo core' dm Silmaril.Wasm.Perf.CoreDecode.decodeF
  let o ← phase "newFullLWith" (fun _ => Silmaril.Wasm.Perf.JcoMain.newFullLWith dec core' wf) exceptDig
  let some o := o.toOption | pure 1
  let _ ← phase "refOf" (fun _ => Silmaril.Wasm.JcoTool.ToolV.refOf o) exceptDig
  let _ ← phase "refCheckXWith" (fun _ => Silmaril.Wasm.Perf.JcoMain.refCheckXWith dec o.bytes) exceptDig
  let _ ← phase "newDefaultD (all)" (fun _ => Silmaril.Wasm.Perf.JcoMain.newDefaultD b d₀ none) exceptDig
  pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["phases-default", f] => phasesDefault f
  | ["phases", f] => phases f
  | ["phases-validate", f] =>
    let b ← IO.FS.readBinFile f
    let _ ← phase "parse" (fun _ => Silmaril.Wasm.Component.Binary.parse b)
      (fun r => match r with | .ok _ => "ok" | .error _ => "error")
    let _ ← phase "xparse" (fun _ => Silmaril.Wasm.JcoTool.xparse b)
      (fun r => match r with | .ok _ => "ok" | .error _ => "error")
    let ks ← phase "coreModulesOf" (fun _ => Silmaril.Wasm.Perf.JcoMain.coreModulesOf b) (·.length.repr)
    let tbl ← phase "decodeAll" (fun _ => Silmaril.Wasm.Perf.JcoMain.decodeAll ks Silmaril.Wasm.Perf.CoreDecode.decodeF)
      (·.length.repr)
    let dec := Silmaril.Wasm.Perf.JcoMain.lookup tbl Silmaril.Wasm.Perf.CoreDecode.decodeF
    let _ ← phase "parseComponentWith" (fun _ => Silmaril.Wasm.Perf.JcoMain.parseComponentWith dec b) exceptDig
    let _ ← phase "refCore3XWith" (fun _ => Silmaril.Wasm.Perf.JcoMain.refCore3XWith dec b) exceptDig
    let _ ← phase "refCheckXWith" (fun _ => Silmaril.Wasm.Perf.JcoMain.refCheckXWith dec b) exceptDig
    let _ ← phase "validateLines" (fun _ => Silmaril.Wasm.Perf.JcoMain.validateLines b) (·.length.repr)
    pure 0
  | ["validate-core-fast", f] =>
    let b ← IO.FS.readBinFile f
    match Silmaril.Wasm.Perf.CoreDecode.decodeF b with
    | none => IO.println "undecodable"; pure 1
    | some m =>
      let _ ← phase "validateF" (fun _ => Silmaril.Wasm.Perf.ValidateF.validateF m)
        (fun r => if r.isSome then "valid" else "invalid")
      pure 0
  | ["validate-core-r", f] =>
    let b ← IO.FS.readBinFile f
    match Silmaril.Wasm.Perf.CoreDecode.decodeF b with
    | none => IO.println "undecodable"; pure 1
    | some m =>
      let _ ← phase "validateR" (fun _ => Silmaril.Wasm.Perf.ValidateR.validateR m)
        (fun r => if r.isSome then "valid" else "invalid")
      pure 0
  | ["validate-core", f] =>
    let b ← IO.FS.readBinFile f
    match Silmaril.Wasm.Perf.CoreDecode.decodeF b with
    | none => IO.println "undecodable"; pure 1
    | some m =>
      let _ ← phase "validate?" (fun _ => Silmaril.Wasm.Validation.validate? m)
        (fun r => if r.isSome then "valid" else "invalid")
      pure 0
  | ["decode-core", which, f] =>
    let b ← IO.FS.readBinFile f
    let r := match which with
      | "spec" => Silmaril.Wasm.Binary.Core.decode? b
      | _ => Silmaril.Wasm.Perf.CoreDecode.decodeF b
    IO.println (digestModule r)
    pure 0
  | ["print-wat", which, f] =>
    let b ← IO.FS.readBinFile f
    match Silmaril.Wasm.Component.Binary.parse b with
    | .error _ => IO.eprintln "malformed component"; pure 1
    | .ok c =>
      let t := match which with
        | "spec" => Silmaril.Wasm.Component.Wat.print c
        | _ => Silmaril.Wasm.Perf.WatPrint.printF c
      IO.println s!"{t.length} chars, {t.utf8ByteSize} bytes, hash {hash t}"
      pure 0
  | ["parse-wat", which, f] =>
    let t ← IO.FS.readFile f
    let r := match which with
      | "spec" => Silmaril.Wasm.Wit.Tool.parseWat t
      | "bytes" => Silmaril.Wasm.Perf.WatReadB.parseWatB t
      | _ => Silmaril.Wasm.Perf.WatRead.parseWatF t
    match r with
    | .ok b => IO.println s!"{b.size} bytes, hash {hash b}"; pure 0
    | .error e => IO.println s!"error {e}"; pure 1
  | _ => IO.eprintln "usage: wasm-perf decode-core spec|fast CORE.wasm"; pure 2
