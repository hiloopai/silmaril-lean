module

public meta import Mathlib.Tactic.NormNum
public meta import Lean.Elab.Tactic.Omega
public import Silmaril.Compiler.Native.Assembly.Defs
/-! Exact byte coverage, layout length, and non-truncating displacements for
range-checked assembly derivations. No machine or source semantics is replaced. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Assembly
open Silmaril Silmaril.X86

variable {labels : Labels} {pc endPc : Nat} {statements : List Statement} {bytes : List Byte}

/-- All emitted bytes belong to real canonical typed instruction encodings. -/
theorem Assembles.covered (assembled : Assembles labels pc statements bytes endPc) :
    Ext.Covered bytes := by
  induction assembled with
  | nil => exact ⟨[], rfl⟩
  | label _ _ ih => exact ih
  | @plain pc instruction statements bytes endPc rest ih =>
      obtain ⟨instructions, same⟩ := ih
      exact ⟨instruction :: instructions, by simpa using congrArg (Ext.encode instruction ++ ·) same⟩
  | @jump8 pc name target statements bytes endPc found fits rest ih =>
      obtain ⟨instructions, same⟩ := ih
      refine ⟨.jmp8 (BitVec.ofInt 8 (displacement target (pc + 2))) :: instructions, ?_⟩
      simpa using congrArg (Ext.encode (.jmp8 (BitVec.ofInt 8 (displacement target (pc + 2)))) ++ ·) same
  | @jump32 pc name target statements bytes endPc found fits rest ih =>
      obtain ⟨instructions, same⟩ := ih
      refine ⟨.jmp (BitVec.ofInt 32 (displacement target (pc + 5))) :: instructions, ?_⟩
      simpa using congrArg (Ext.encode (.jmp (BitVec.ofInt 32 (displacement target (pc + 5)))) ++ ·) same

/-- Layout consumes exactly the number of bytes emitted by the typed encoder. -/
theorem Assembles.length (assembled : Assembles labels pc statements bytes endPc) :
    endPc = pc + bytes.length := by
  induction assembled with
  | nil => simp
  | label _ _ ih => exact ih
  | plain _ ih => simpa [List.length_append, Nat.add_assoc] using ih
  | @jump8 pc name target statements bytes endPc found fits rest ih =>
      simp only [List.length_append]
      change endPc = pc + (2 + bytes.length)
      omega
  | @jump32 pc name target statements bytes endPc found fits rest ih =>
      simp only [List.length_append]
      change endPc = pc + (5 + bytes.length)
      omega

/-- Range checking makes the resolved displacement reach the actual label,
without truncation. This is a mathematical instruction-target fact, not just
agreement with an encoding function. -/
theorem displacement_target {width : Nat} (positive : 0 < width) {target next : Nat}
    (fits : Fits width (displacement target next)) :
    (next : Int) + (BitVec.ofInt width (displacement target next)).toInt = target := by
  rw [BitVec.toInt_ofInt_eq_self positive fits.1 fits.2]
  unfold displacement
  omega

/-- The frame operand denotes the parsed signed displacement exactly. -/
theorem frame_displacement {offset : Nat} (range : offset ≤ 2^31) :
    (frame offset).disp.toInt = -(offset : Int) := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · norm_num
    omega
  · norm_num
    omega

end Silmaril.Compiler.Native.Assembly
