module

public import Silmaril.Wasm.Perf.JcoCore.Defs
public import Silmaril.Wasm.JcoTool.StreamSem.Defs

/-!
# `wasm-jco new` and `validate` with each core module decoded once and validated once

`wasm-jco new` (default mode) ran `Front.worldFullOf`, `Front.newValid` and
`StreamSem.report`; together they decoded the input core module seven times (the world's import
names, the plan, the reference check `ToolV.refCheckLine` inside `JcoNew.newFullRF`, the
reference check `ToolV.refCheckX` in `Front.newValid`, the world again for the report, and the
report's plan twice) and ran silmaril's validator (`Reference.check?`, which validates every
function body) twice, once per reference check. `wasm-jco validate` decoded each core module
twice (`parseComponent`, `refCheckX`).

The memo decoders, the `…With dec` functions (the decoder as an argument), the reference check
and `wasm-jco validate` (`validateLines`) are in `Silmaril.Wasm.Perf.JcoCore`, which does not
depend on the streams development; this module adds the **stream report**:

* `reportWith dec`: `StreamSem.report` with the decoder `dec`.
* `newDefault core wit`: the world, the component and the report lines of `wasm-jco new`, with
  the input decoded once and the prepared module (`Front.prepareCore`, which drops the
  `component-type` sections) once more when it differs from the input; the reference validator
  runs once (`refCheckX`). Its summary ends with `refCheckX`'s verdict line instead of
  `refCheckLine`'s (`fixSummary`): the other reading of the same bytes, which `Front.newValid`
  also requires and which the tool used to print twice in effect.

`Thms.lean`: `newDefault_eq` (the result is that of `Front.worldFullOf`, `Front.newValid` and
`StreamSem.report`, with the summary's last line replaced) and `newDefault_fst` (its component
is `JcoCore`'s `newDefaultC`).
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.JcoMain

open Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Wit.Binary (WorldFull World)

/-- `StreamSem.report` with the decoder `dec`. -/
def reportWith (dec : Dec) (core : ByteArray) (w : World) : List String :=
  match newPlanWith dec core w with
  | .ok p => (p.exports.filter fun f => StreamSem.xfShape p f.name).map fun f =>
      s!"proc:  export {f.name} has the shape of a Proc stream transformer (StreamSem.newWith_stream_semantics)"
  | .error _ => []

/-- The first stage of `newDefault`: the world, the stream report and the prepared module, with
the input decoded once; and the input's decoded module when the prepared module is the input
(`none` otherwise, so that it is not kept alive while the prepared module is decoded and
validated). Not inlined: the tuple is built, the report computed, when the stage returns. -/
@[noinline] def newStage1 (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (WorldFull × List String × ByteArray × Option (Option Silmaril.Wasm.Module)) := do
  let d₀ := Silmaril.Wasm.Perf.CoreDecode.decodeF core
  let dec₀ := memo core d₀ Silmaril.Wasm.Perf.CoreDecode.decodeF
  let wf ← worldFullOfWith dec₀ core wit
  let rep := reportWith dec₀ core wf.world
  let core' ← Front.prepareCore core
  pure (wf, rep, core', if core' == core then some d₀ else none)

/-- **`wasm-jco new`, default mode**: the component and the stream report, each core module
decoded once (the input; the prepared module when it differs, after the input's decoded module
is dropped) and validated once (`newDefault_eq`). -/
def newDefault (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (Tool.Out × List String) := do
  let (wf, rep, core', d') ← newStage1 core wit
  let o ← newValidWith (memo core' (pick d' core') Silmaril.Wasm.Perf.CoreDecode.decodeF) core' wf
  pure (o, rep)

/-- `newStage1` with the input's decoded module `d₀` given by the caller (`wasm-jco new` decodes
the input once, for `Adapt.needsGeneralOf` and for this stage). -/
@[noinline] def newStage1D (core : ByteArray) (d₀ : Option Silmaril.Wasm.Module)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (WorldFull × List String × ByteArray × Option (Option Silmaril.Wasm.Module)) := do
  let dec₀ := memo core d₀ Silmaril.Wasm.Perf.CoreDecode.decodeF
  let wf ← worldFullOfWith dec₀ core wit
  let rep := reportWith dec₀ core wf.world
  let core' ← Front.prepareCore core
  pure (wf, rep, core', if core' == core then some d₀ else none)

/-- `newDefault` with the input's decoded module `d₀` given (`newDefaultD_eq`: on
`decodeF core` it is `newDefault core`). -/
def newDefaultD (core : ByteArray) (d₀ : Option Silmaril.Wasm.Module)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (Tool.Out × List String) := do
  let (wf, rep, core', d') ← newStage1D core d₀ wit
  let o ← newValidWith (memo core' (pick d' core') Silmaril.Wasm.Perf.CoreDecode.decodeF) core' wf
  pure (o, rep)

end Silmaril.Wasm.Perf.JcoMain
