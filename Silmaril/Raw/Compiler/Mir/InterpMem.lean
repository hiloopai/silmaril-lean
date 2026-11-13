module

public import Silmaril.Compiler.Mir.Semantics.Defs
@[expose] public section

/-! # Byte access in the interpreter's paged memory -/

namespace Silmaril.Compile.Mir.Interp.Mem

open Silmaril.Machine

/-- Allocated pages are either the shared zero page or a full page. -/
def WellFormed (m : Mem) : Prop :=
  ∀ i < m.pages.size, (m.pages[i]!).size = 0 ∨ (m.pages[i]!).size = pageSize

@[simp] theorem getByte_zero (size a : Nat) : (zero size).getByte a = 0 := by
  unfold getByte zero
  by_cases h : a >>> pageBits < (size + pageSize - 1) / pageSize
  · rw [getElem!_pos (Array.replicate ((size + pageSize - 1) / pageSize) ByteArray.empty)
      (a >>> pageBits) (by simpa using h), Array.getElem_replicate]
    rfl
  · rw [getElem!_neg (Array.replicate ((size + pageSize - 1) / pageSize) ByteArray.empty)
      (a >>> pageBits) (by simpa using h)]
    rfl

@[simp] theorem zero_wellFormed (size : Nat) : (zero size).WellFormed := by
  intro i hi
  left
  change ((Array.replicate ((size + pageSize - 1) / pageSize) ByteArray.empty)[i]!).size = 0
  have hi' : i < (Array.replicate ((size + pageSize - 1) / pageSize) ByteArray.empty).size := hi
  rw [getElem!_pos _ i hi', Array.getElem_replicate]
  rfl

@[simp] theorem zero_toLir (size : Nat) : (zero size).toLir = ⟨size, fun _ => 0⟩ := by
  change Lir.Memory.mk size _ = Lir.Memory.mk size _
  congr 1
  funext a
  simp only [getByte_zero]
  rfl

end Silmaril.Compile.Mir.Interp.Mem
