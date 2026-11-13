module

public import Silmaril.Wasm.Perf.JcoNew.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Thms
public import Silmaril.Wasm.Perf.CoreMod.Thms
public import Silmaril.Wasm.Perf.XEncodeB.Thms

/-!
# `wasm-jco new` with one decode is `wasm-jco new`

`planF_eq : planF = NewI.plan` and `newFullRF_eq : newFullRF = ToolV.newFullR`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.JcoNew

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Wit.Binary (WorldFull)

theorem coreMod_split (b : ByteArray) : Lower.coreMod b =
    match Silmaril.Wasm.Binary.Core.decode? b with
    | some m => coreModOf b m
    | none => throw "embedded core module rejected by silmaril's core decoder (outside its fragment)" := by
  unfold Lower.coreMod coreModOf
  cases Silmaril.Wasm.Binary.Core.decode? b <;> rfl

theorem hasMemory_split (b : ByteArray) : New.hasMemory b =
    match Silmaril.Wasm.Binary.Core.decode? b with
    | some m => hasMemoryOf m
    | none => false := by
  unfold New.hasMemory hasMemoryOf
  rw [Silmaril.Wasm.Perf.CoreDecode.decodeF_eq]
  cases Silmaril.Wasm.Binary.Core.decode? b <;> rfl

theorem planF_eq : planF = NewI.plan := by
  funext core wf
  rw [NewI.plan, Silmaril.Wasm.Perf.CoreMod.coreModF_eq, coreMod_split, hasMemory_split, planF,
    Silmaril.Wasm.Perf.CoreDecode.decodeF_eq]
  cases Silmaril.Wasm.Binary.Core.decode? core <;> rfl

theorem newI_eq (core : ByteArray) (wf : WorldFull) :
    ToolI.newI core wf = NewI.plan core wf >>= newIP := by
  unfold ToolI.newI
  congr 1
  funext p
  simp only [newIP, ← Silmaril.Wasm.Perf.XEncodeB.xencodeF_eq]

theorem checkLayout_eq {core : ByteArray} {wf : WorldFull} {p : NewI.Plan} (o : Tool.Out)
    (hold : ToolI.inOld wf.world = false) (hp : NewI.plan core wf = .ok p) :
    ToolV.checkLayout core wf o = checkLayoutP p o := by
  unfold ToolV.checkLayout checkLayoutP
  rw [hold, hp]
  cases xparse o.bytes <;> rfl

theorem newFullLF_eq : newFullLF = ToolV.newFullL := by
  funext core wf
  cases hold : ToolI.inOld wf.world
  · cases hp : NewI.plan core wf with
    | error e =>
      simp only [newFullLF, ToolV.newFullL, ToolV.newFullV, ToolI.newFull, hold, newI_eq, hp,
        planF_eq]
      rfl
    | ok p =>
      have ok_bind : ∀ {β : Type} (f : NewI.Plan → Except String β), (Except.ok p >>= f) = f p :=
        fun _ => rfl
      simp only [newFullLF, ToolV.newFullL, ToolV.newFullV, ToolI.newFull, hold, newI_eq, hp,
        planF_eq, checkLayout_eq _ hold hp, Bool.false_eq_true, ite_false, ok_bind, bind_assoc,
        pure_bind]
  · simp only [newFullLF, hold, ite_true]

/-- **`wasm-jco new` with one decode is `wasm-jco new`.** -/
theorem newFullRF_eq : newFullRF = ToolV.newFullR := by
  funext core wf
  simp only [newFullRF, ToolV.newFullR, newFullLF_eq]

end Silmaril.Wasm.Perf.JcoNew
