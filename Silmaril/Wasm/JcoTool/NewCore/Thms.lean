module

public import Silmaril.Wasm.JcoTool.NewCore.Defs
public import Silmaril.Wasm.Perf.JcoCore.Thms

/-!
# `NewCore.newMainC` is `needsGeneral`, then `Perf.JcoMain.newDefaultC`

* `stage1GC_eq`: the first stage is `needsGeneral`, then `newStage1C`.
* **`newMainC_eq`**: `newMainC core wit = if needsGeneral core then pure none else
  some <$> newDefaultC core wit`; so, by `Perf.JcoMain.newDefaultC_eq`, the bytes written on the
  certified path are those of `Front.newValid`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.NewCore

open Silmaril.Wasm.Perf.JcoMain

theorem stage1GC_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    stage1GC core wit =
      if Adapt.needsGeneral core then pure none else some <$> newStage1C core wit := by
  unfold stage1GC newStage1C Adapt.needsGeneral
  rw [decodeF_spec]
  by_cases h : Adapt.needsGeneralOf (spec core) core = true
  · simp only [h, ite_true]
  · simp only [h]
    simp only [Bool.false_eq_true, ite_false, map_eq_pure_bind, bind_assoc, pure_bind]

/-- **The default mode of `wasm-jco new` without the report**, the input decoded once: `none`
exactly when the module needs the general layout, else `Perf.JcoMain.newDefaultC`. -/
theorem newMainC_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    newMainC core wit =
      if Adapt.needsGeneral core then pure none else some <$> newDefaultC core wit := by
  unfold newMainC newDefaultC
  rw [stage1GC_eq]
  by_cases h : Adapt.needsGeneral core = true
  · simp only [h, ite_true, pure_bind]
  · simp only [h, Bool.false_eq_true, ite_false, map_eq_pure_bind, bind_assoc, pure_bind]

end Silmaril.Wasm.JcoTool.NewCore
