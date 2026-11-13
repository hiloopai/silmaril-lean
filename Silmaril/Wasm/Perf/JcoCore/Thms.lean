module

public import Silmaril.Wasm.Perf.JcoCore.Defs
public import Silmaril.Wasm.Perf.JcoNew.Thms
public import Silmaril.Wasm.Perf.LowerF.Thms
public import Silmaril.Wasm.Perf.ValidateComp.Thms

/-!
# The stream-free part of `wasm-jco new` and `validate` is the specification functions

* `memo_self`, `lookup_decodeAll`: a memo filled by the decoder is the decoder.
* `worldFullOfWith_eq`, `planWith_eq`, `newFullLWith_eq`, `refCheckXWith_eq`, `newPlanWith_eq`,
  `parseComponentWith_eq`: with silmaril's decoder (or `decodeF`, equal to it), each `…With`
  function is its original.
* `newValidWith_eq`: `newValidWith` is `ToolV.newFullR` followed by the reference check
  `refCheckX`, with the summary's last line replaced (`fixSummary`).
* **`newDefaultC_eq`**: `newDefaultC core wit` is `Front.worldFullOf`, then `Front.newValid`
  (its output through `fixSummary`): the bytes `wasm-tools component new` writes on the
  certified path are those of `Front.newValid`, so `Front.newValid_valid` and every
  `ToolV.newFullR` theorem apply.
* **`validateLines_eq`**: `validateLines b = Tool.validate b ++ [ToolV.refCheckXLine b]`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.JcoMain

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower
open Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Wit.Binary (WorldFull World)

/-- Silmaril's decoder. -/
abbrev spec : Dec := Silmaril.Wasm.Binary.Core.decode?

theorem decodeF_spec : (Silmaril.Wasm.Perf.CoreDecode.decodeF : Dec) = spec :=
  Silmaril.Wasm.Perf.CoreDecode.decodeF_eq

/-! ## The memo -/

/-- **A memo filled by the decoder is the decoder.** -/
theorem memo_self (k : ByteArray) (d : Dec) : memo k (d k) d = d := by
  funext b
  unfold memo
  split
  · rename_i h
    rw [eq_of_beq h]
  · rfl

theorem lookup_decodeAll (ks : List ByteArray) (d : Dec) : lookup (decodeAll ks d) d = d := by
  funext b
  unfold lookup decodeAll
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [List.map_cons, List.find?_cons]
    by_cases hk : (k == b) = true
    · simp only [hk]
      rw [eq_of_beq hk]
    · simp only [hk]
      exact ih

/-! ## The functions with the decoder as an argument -/

theorem coreModWith_eq : coreModWith spec = Lower.coreMod := by
  funext b
  rw [Silmaril.Wasm.Perf.JcoNew.coreMod_split]
  unfold coreModWith spec
  cases Silmaril.Wasm.Binary.Core.decode? b <;> rfl

theorem hasMemoryWith_eq : hasMemoryWith spec = New.hasMemory := by
  funext b
  rw [Silmaril.Wasm.Perf.JcoNew.hasMemory_split]
  unfold hasMemoryWith spec
  cases Silmaril.Wasm.Binary.Core.decode? b <;> rfl

theorem worldFullOfWith_eq : worldFullOfWith spec = Front.worldFullOf := by
  funext core wit
  unfold worldFullOfWith Front.worldFullOf WorldMerge.coreImportNames
  rw [coreModWith_eq]

theorem planWith_eq : planWith spec = NewI.plan := by
  rw [← Silmaril.Wasm.Perf.JcoNew.planF_eq, ← decodeF_spec]
  rfl

theorem newFullLWith_eq : newFullLWith spec = ToolV.newFullL := by
  rw [← Silmaril.Wasm.Perf.JcoNew.newFullLF_eq, ← decodeF_spec]
  rfl

theorem refCheckXWith_eq : refCheckXWith spec = ToolV.refCheckX := by
  funext b
  unfold refCheckXWith ToolV.refCheckX ToolV.refCore3X
  rw [← decodeF_spec]
  rfl

theorem newPlanWith_eq : newPlanWith spec = New.plan := by
  funext core w
  unfold newPlanWith New.plan
  rw [Silmaril.Wasm.Perf.CoreMod.coreModF_eq, coreModWith_eq, hasMemoryWith_eq]

theorem sectionWith_eq : sectionWith spec = Lower.section_ := by
  funext sec
  unfold sectionWith Lower.section_
  rw [coreModWith_eq]
  rfl

theorem parseComponentWith_eq : parseComponentWith spec = parseComponent := by
  funext b
  unfold parseComponentWith parseComponent lower
  rw [sectionWith_eq]
  rfl

/-! ## `wasm-jco new` -/

theorem fixSummary_append (o : Tool.Out) (s : List String) (l : String) :
    fixSummary { o with summary := s ++ [l] } = { o with summary := s ++ [refXYes] } := by
  unfold fixSummary
  rw [List.dropLast_concat]

/-- **`newValidWith` is `ToolV.newFullR`, then `refCheckX`**, with `fixSummary`. -/
theorem newValidWith_eq (core : ByteArray) (wf : WorldFull) :
    newValidWith spec core wf = (do
      let o ← ToolV.newFullR core wf
      match ToolV.refCheckX o.bytes with
      | .ok _ => pure (fixSummary o)
      | .error e => throw s!"refusing to write an output the reference validator rejects: {e}") := by
  unfold newValidWith ToolV.newFullR
  rw [newFullLWith_eq, refCheckXWith_eq]
  cases ToolV.newFullL core wf with
  | error e => rfl
  | ok o =>
    simp only [bind, Except.bind, pure, Except.pure]
    cases ToolV.refOf o with
    | error e => rfl
    | ok c =>
      simp only
      cases ToolV.refCheckX o.bytes with
      | error e => rfl
      | ok ct =>
        simp only
        rw [fixSummary_append]
        rfl

/-- `Front.newValid` with its output through `fixSummary`. -/
theorem newValid_fix (core : ByteArray) (wf : WorldFull) :
    (Front.prepareCore core >>= fun core' => newValidWith spec core' wf) =
      (fixSummary <$> Front.newValid core wf) := by
  unfold Front.newValid
  rw [Silmaril.Wasm.Perf.JcoNew.newFullRF_eq]
  cases Front.prepareCore core with
  | error e => rfl
  | ok core' =>
    simp only [bind, Except.bind]
    rw [newValidWith_eq]
    cases ToolV.newFullR core' wf with
    | error e => rfl
    | ok o =>
      simp only [bind, Except.bind]
      cases ToolV.refCheckX o.bytes with
      | error e => rfl
      | ok ct => rfl

/-- The module the second stage validates with is the prepared module's. -/
theorem pick_eq (core core' : ByteArray) :
    pick (if core' == core then some (spec core) else none) core' = spec core' := by
  unfold pick
  rw [decodeF_spec]
  by_cases h : (core' == core) = true
  · rw [ite_eq_left h, eq_of_beq h]
  · rw [ite_eq_right h]

/-- The first stage without the report. -/
theorem newStage1C_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    newStage1C core wit = (do
      let wf ← Front.worldFullOf core wit
      let core' ← Front.prepareCore core
      pure (wf, core', if core' == core then some (spec core) else none)) := by
  unfold newStage1C
  rw [decodeF_spec]
  simp only [memo_self, worldFullOfWith_eq]

/-- **The component of `wasm-jco new`'s default mode, one decode per module**: the world, then
`Front.newValid` (its last summary line replaced by `refCheckX`'s verdict). -/
theorem newDefaultC_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    newDefaultC core wit = (do
      let wf ← Front.worldFullOf core wit
      let o ← Front.newValid core wf
      pure (fixSummary o)) := by
  have ok_bind : ∀ {α β : Type} (a : α) (f : α → Except String β), (Except.ok a >>= f) = f a :=
    fun _ _ => rfl
  unfold newDefaultC
  rw [newStage1C_eq, decodeF_spec]
  cases Front.worldFullOf core wit with
  | error e => rfl
  | ok wf =>
    simp only [bind_assoc, pure_bind, ok_bind, pick_eq, memo_self]
    show (Front.prepareCore core >>= fun core' => newValidWith spec core' wf) =
      (Front.newValid core wf >>= fun o => pure (fixSummary o))
    rw [newValid_fix, map_eq_pure_bind]

/-- The input decoded by the caller: `newDefaultDC` on the input's decoded module is
`newDefaultC`. -/
theorem newDefaultDC_eq (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    newDefaultDC core (Silmaril.Wasm.Perf.CoreDecode.decodeF core) wit = newDefaultC core wit :=
  rfl

/-! ## `wasm-jco validate` -/

/-- **`wasm-jco validate` with one decode per module** prints `Tool.validate`'s lines and
`refCheckX`'s verdict. -/
theorem validateLines_eq (b : ByteArray) :
    validateLines b = Tool.validate b ++ [ToolV.refCheckXLine b] := by
  unfold validateLines
  rw [lookup_decodeAll, decodeF_spec]
  unfold validateLinesWith Tool.validate ToolV.refCheckXLine
  rw [parseComponentWith_eq, refCheckXWith_eq, Silmaril.Wasm.Perf.LowerF.parseComponentF_eq]
  rfl

end Silmaril.Wasm.Perf.JcoMain
