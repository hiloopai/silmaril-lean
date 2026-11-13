module

public import Silmaril.Wasm.JcoTool.NewMain.Defs
public import Silmaril.Wasm.Perf.JcoMain.Thms
public import Silmaril.Wasm.JcoTool.NewCore.Thms

/-!
# `NewMain.newMain` is `needsGeneral`, then `Perf.JcoMain.newDefault`

* `stage1G_eq`: the first stage is `needsGeneral`, then `newStage1`.
* **`newMain_eq`**: `newMain core wit = if needsGeneral core then pure none else
  some <$> newDefault core wit`; so, by `Perf.JcoMain.newDefault_eq`, the bytes `wasm-jco new`
  writes on the certified path are those of `Front.newValid`.
* **`newMain_fst`**: without its stream report, `newMain` is `NewCore.newMainC`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.NewMain

open Silmaril.Wasm.Perf.JcoMain

theorem stage1G_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    stage1G core wit =
      if Adapt.needsGeneral core then pure none else some <$> newStage1 core wit := by
  unfold stage1G newStage1 Adapt.needsGeneral
  rw [decodeF_spec]
  by_cases h : Adapt.needsGeneralOf (spec core) core = true
  · simp only [h, ite_true]
  · simp only [h]
    simp only [Bool.false_eq_true, ite_false, map_eq_pure_bind, bind_assoc, pure_bind]

/-- **The default mode of `wasm-jco new`**, the input decoded once: `none` exactly when the
module needs the general layout, else `Perf.JcoMain.newDefault`. -/
theorem newMain_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    newMain core wit =
      if Adapt.needsGeneral core then pure none else some <$> newDefault core wit := by
  unfold newMain newDefault
  rw [stage1G_eq]
  by_cases h : Adapt.needsGeneral core = true
  · simp only [h, ite_true, pure_bind]
  · simp only [h, Bool.false_eq_true, ite_false, map_eq_pure_bind, bind_assoc, pure_bind]

/-- **`newMain` without its stream report is `NewCore.newMainC`** (what `wasm-tools component
new` runs). -/
theorem newMain_fst (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Option.map Prod.fst <$> newMain core wit = NewCore.newMainC core wit := by
  rw [newMain_eq, NewCore.newMainC_eq, ← newDefault_fst]
  by_cases h : Adapt.needsGeneral core = true
  · simp only [h, ite_true]
    rfl
  · simp only [h, Bool.false_eq_true, ite_false]
    cases newDefault core wit <;> rfl

end Silmaril.Wasm.JcoTool.NewMain
