module

public import Silmaril.Wasm.Perf.JcoMain.Defs
public import Silmaril.Wasm.JcoTool.Adapt.Defs

/-!
# `wasm-jco new`, default mode, with the general-layout test on the same decode

`wasm-jco new` first asks whether the module needs the general layout (`Adapt.needsGeneral`:
it exports `__wasm_task_hook` or `_initialize`), then runs `Perf.JcoMain.newDefault`. Both
decoded the input; here the decoded module of `newDefault`'s first stage also answers
`needsGeneral` (`needsGeneralOf`), so the input is decoded once. `newMain_eq` (`Thms`):
`newMain core wit` is `none` when `needsGeneral core`, else `newDefault core wit`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.NewMain

open Silmaril.Wasm.Perf.JcoMain
open Silmaril.Wasm.Wit.Binary (WorldFull)

/-- `Perf.JcoMain.newStage1`, which first answers `needsGeneral` from the decoded input
(`none`: the module needs the general layout). -/
@[noinline] def stage1G (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String
      (Option (WorldFull × List String × ByteArray × Option (Option Silmaril.Wasm.Module))) := do
  let d₀ := Silmaril.Wasm.Perf.CoreDecode.decodeF core
  if Adapt.needsGeneralOf d₀ core then pure none else
  let dec₀ := memo core d₀ Silmaril.Wasm.Perf.CoreDecode.decodeF
  let wf ← worldFullOfWith dec₀ core wit
  let rep := reportWith dec₀ core wf.world
  let core' ← Front.prepareCore core
  pure (some (wf, rep, core', if core' == core then some d₀ else none))

/-- **`wasm-jco new`, default mode**: `none` when the module needs the general layout, else the
component and the stream report of `Perf.JcoMain.newDefault`, the input decoded once in all
(`newMain_eq`). -/
def newMain (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (Option (Tool.Out × List String)) := do
  match ← stage1G core wit with
  | none => pure none
  | some (wf, rep, core', d') =>
    let o ← newValidWith (memo core' (pick d' core') Silmaril.Wasm.Perf.CoreDecode.decodeF) core' wf
    pure (some (o, rep))

end Silmaril.Wasm.JcoTool.NewMain
