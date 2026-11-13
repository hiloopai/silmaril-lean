module

public import Silmaril.Wasm.JcoTool.Layout.Defs
public import Silmaril.Wasm.JcoTool.Helpers.Thms

/-!
# The entry point with the layout checked

**`newFullL_correct`**: an output of `wasm-jco new` (`ToolV.newFullL`, what the tool runs in
thin-wrapper mode) is that of `newFull` with its helper modules checked
(`ToolV.newFullV_correct`: `newFull_correct`, every shim and fixup encodes the specified
module), and, for a world outside an earlier fragment (interfaces, named types, resources), its
bytes parse (`xparse`) to a component whose **component-level reading** (`Layout.read`: the
exports with their lifts, the main module's core imports resolved through the inline instances,
the shim and the fixup to lowers of world or interface functions, resource built-ins of
imported or exported resources and async built-ins, the resources with their destructors) is
**the layout the world describes** (`Layout.expected` of the plan, whose functions are those of
the world, `exportFns wf`, at their canonical core types, `NewIOk`).

This is translation validation: the check runs on every output and the tool refuses an output
that fails it; it is not a proof that the emitter always passes it. The reading is defined
here after the Component Model's index spaces, not derived from a semantics of components.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.ToolV

open Silmaril.Wasm.Wit.Binary (WorldFull)
open New (bind_ok)
open Layout

theorem checkLayout_ok {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : checkLayout core wf o = .ok ()) (hw : ToolI.inOld wf.world = false) :
    ∃ p x, NewI.plan core wf = .ok p ∧ xparse o.bytes = .ok x ∧
      read p.mod.importNames x = some (expected p) := by
  unfold checkLayout at h
  rw [hw] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · rename_i p x hp hx
    split at h
    · rename_i hl
      exact ⟨p, x, hp, hx, by simpa [layoutOk] using hl⟩
    · cases h
  · cases h

/-- **The correctness theorem of `wasm-jco new`** (thin wrapper), with the helper modules and
the component-level layout checked. -/
theorem newFullL_correct {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newFullL core wf = .ok o) :
    ∃ o', ToolI.newFull core wf = .ok o' ∧ Checked o o' ∧
      ((ToolI.inOld wf.world = true ∧ Tool.newWith core wf.world = .ok o') ∨
        (ToolI.inOld wf.world = false ∧ ToolI.NewIOk core wf o' ∧
          ∃ p x, NewI.plan core wf = .ok p ∧ xparse o.bytes = .ok x ∧
            read p.mod.importNames x = some (expected p))) := by
  obtain ⟨o₁, h₁, h₂⟩ := bind_ok h
  obtain ⟨u, hc, h₃⟩ := bind_ok h₂
  cases h₃
  obtain ⟨o', ho, ⟨hb, ha, hi, hcs, hh⟩, hcase⟩ := newFullV_correct h₁
  refine ⟨o', ho, ⟨hb, ha, hi, hcs, hh⟩, ?_⟩
  rcases hcase with hold | ⟨hw, hok⟩
  · exact .inl hold
  · exact .inr ⟨hw, hok, checkLayout_ok hc hw⟩

end Silmaril.Wasm.JcoTool.ToolV
