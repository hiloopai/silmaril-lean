module

public import Silmaril.Wasm.Perf.JcoMain.Defs
public import Silmaril.Wasm.Perf.JcoCore.Thms

/-!
# `wasm-jco new` with the stream report, one decode per module, is the specification function

The stream-free part (the decoder lemmas, `newValidWith_eq`, `newDefaultC_eq`,
`validateLines_eq`) is `Silmaril.Wasm.Perf.JcoCore.Thms`.

* `reportWith_eq`: with silmaril's decoder, `reportWith` is `StreamSem.report`.
* **`newDefault_eq`**: `newDefault core wit` is `Front.worldFullOf`, then `Front.newValid` (its
  output through `fixSummary`) and `StreamSem.report`: the bytes `wasm-jco new` writes are those
  of `Front.newValid`, so `Front.newValid_valid` and every `ToolV.newFullR` theorem apply.
* **`newDefault_fst`**: the component of `newDefault` is `newDefaultC`'s (the report changes
  nothing in it).
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.JcoMain

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower
open Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Wit.Binary (WorldFull World)

theorem reportWith_eq : reportWith spec = StreamSem.report := by
  funext core w
  unfold reportWith StreamSem.report
  rw [newPlanWith_eq]
  rfl

/-- The first stage: the world, the report, the prepared module, and the input's decoded module
when the prepared module is the input. -/
theorem newStage1_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    newStage1 core wit = (do
      let wf ← Front.worldFullOf core wit
      let core' ← Front.prepareCore core
      pure (wf, StreamSem.report core wf.world, core',
        if core' == core then some (spec core) else none)) := by
  unfold newStage1
  rw [decodeF_spec]
  simp only [memo_self, worldFullOfWith_eq, reportWith_eq]

/-- **`wasm-jco new` with one decode per module**: the world, then `Front.newValid` (its last
summary line replaced by `refCheckX`'s verdict), then the stream report. -/
theorem newDefault_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    newDefault core wit = (do
      let wf ← Front.worldFullOf core wit
      let o ← Front.newValid core wf
      pure (fixSummary o, StreamSem.report core wf.world)) := by
  have ok_bind : ∀ {α β : Type} (a : α) (f : α → Except String β), (Except.ok a >>= f) = f a :=
    fun _ _ => rfl
  unfold newDefault
  rw [newStage1_eq, decodeF_spec]
  cases Front.worldFullOf core wit with
  | error e => rfl
  | ok wf =>
    simp only [bind_assoc, pure_bind, ok_bind, pick_eq, memo_self]
    show (Front.prepareCore core >>= fun core' => newValidWith spec core' wf >>= fun o =>
        pure (o, StreamSem.report core wf.world)) =
      (Front.newValid core wf >>= fun o => pure (fixSummary o, StreamSem.report core wf.world))
    rw [← bind_assoc, newValid_fix, map_eq_pure_bind, bind_assoc]
    simp only [pure_bind]

/-- The input decoded by the caller: `newDefaultD` on the input's decoded module is
`newDefault`. -/
theorem newDefaultD_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    newDefaultD core (Silmaril.Wasm.Perf.CoreDecode.decodeF core) wit = newDefault core wit :=
  rfl

/-- **The component of `newDefault` is `newDefaultC`'s**: the stream report is computed beside
the component and changes nothing in it. -/
theorem newDefault_fst (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Prod.fst <$> newDefault core wit = newDefaultC core wit := by
  rw [newDefault_eq, newDefaultC_eq]
  cases Front.worldFullOf core wit with
  | error e => rfl
  | ok wf =>
    show (Prod.fst <$> (Front.newValid core wf >>= fun o =>
        pure (fixSummary o, StreamSem.report core wf.world))) =
      (Front.newValid core wf >>= fun o => pure (fixSummary o))
    cases Front.newValid core wf <;> rfl

end Silmaril.Wasm.Perf.JcoMain
