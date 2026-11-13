module

public import Silmaril.Wasm.Perf.JcoCore.Defs
public import Silmaril.Wasm.JcoTool.Adapt.Defs

/-!
# `wasm-jco new`'s default mode without the stream report

`NewMain.newMain` answers `needsGeneral` from the input decoded once, then runs
`Perf.JcoMain.newDefault`: the component and wasm-jco's **stream report** (the plan read against
the `Proc` model of `Silmaril.Wasm.Component.Streams`). `wasm-tools component new` writes the
component only; `newMainC` is `newMain` without the report, on `Perf.JcoCore` alone, so the
runtime closure of the `component` subcommands has no streams development.

`Thms`: `newMainC_eq` (`newMainC core wit` is `none` when `needsGeneral core`, else
`newDefaultC core wit`); `NewMain.Thms`: `newMain_fst` (`newMain`'s component is `newMainC`'s).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.NewCore

open Silmaril.Wasm.Perf.JcoMain
open Silmaril.Wasm.Wit.Binary (WorldFull)

/-- `Perf.JcoMain.newStage1C`, which first answers `needsGeneral` from the decoded input
(`none`: the module needs the general layout). -/
@[noinline] def stage1GC (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (Option (WorldFull × ByteArray × Option (Option Silmaril.Wasm.Module))) := do
  let d₀ := Silmaril.Wasm.Perf.CoreDecode.decodeF core
  if Adapt.needsGeneralOf d₀ core then pure none else
  let dec₀ := memo core d₀ Silmaril.Wasm.Perf.CoreDecode.decodeF
  let wf ← worldFullOfWith dec₀ core wit
  let core' ← Front.prepareCore core
  pure (some (wf, core', if core' == core then some d₀ else none))

/-- **`wasm-jco new`, default mode, without the stream report**: `none` when the module needs
the general layout, else the component of `Perf.JcoMain.newDefaultC`, the input decoded once in
all (`newMainC_eq`). -/
def newMainC (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (Option Tool.Out) := do
  match ← stage1GC core wit with
  | none => pure none
  | some (wf, core', d') =>
    let o ← newValidWith (memo core' (pick d' core') Silmaril.Wasm.Perf.CoreDecode.decodeF) core' wf
    pure (some o)

end Silmaril.Wasm.JcoTool.NewCore
