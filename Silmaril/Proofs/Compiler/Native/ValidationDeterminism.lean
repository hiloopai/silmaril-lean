module

public import Silmaril.Compiler.Native.Optimize.Validation.Determinism.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Determinism
open Silmaril.Machine
open Silmaril.Compile

theorem instruction {calls : OpenCalls} {instruction : Mir.Instr}
    {frame leftFrame rightFrame : Lir.Frame Nat} {memory leftMemory rightMemory : Lir.Memory}
    (admitted : Lists.AdmittedInstr instruction)
    (left : InstructionExec calls instruction frame memory leftFrame leftMemory)
    (right : InstructionExec calls instruction frame memory rightFrame rightMemory) :
    leftFrame = rightFrame ∧ leftMemory = rightMemory := by
  cases instruction with
  | op op =>
    cases left with
    | op leftExec =>
      cases right with
      | op rightExec => exact Prod.mk.inj (Option.some.inj (leftExec.symm.trans rightExec))
  | fop op dest a b => cases admitted
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem instructions {calls : OpenCalls} {body : List Mir.Instr}
    {frame leftFrame rightFrame : Lir.Frame Nat} {memory leftMemory rightMemory : Lir.Memory}
    (admitted : Lists.Admitted body)
    (left : InstructionsExec calls body frame memory leftFrame leftMemory)
    (right : InstructionsExec calls body frame memory rightFrame rightMemory) :
    leftFrame = rightFrame ∧ leftMemory = rightMemory := by
  induction body generalizing frame memory leftFrame leftMemory rightFrame rightMemory with
  | nil =>
    cases left
    cases right
    exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases left with
    | cons leftHead leftTail =>
      cases right with
      | cons rightHead rightTail =>
        obtain ⟨sameFrame, sameMemory⟩ := instruction (admitted head (by simp)) leftHead rightHead
        subst sameFrame
        subst sameMemory
        exact ih (fun i member => admitted i (by simp [member])) leftTail rightTail

theorem term {term : Lir.Term Nat} {frame : Lir.Frame Nat} {leftExit rightExit : BlockExit}
    (left : TermExec term frame leftExit) (right : TermExec term frame rightExit) :
    leftExit = rightExit := by
  cases left <;> cases right <;> simp_all

theorem block {calls : OpenCalls} {body : Mir.Block}
    {frame leftFrame rightFrame : Lir.Frame Nat} {memory leftMemory rightMemory : Lir.Memory}
    {leftExit rightExit : BlockExit} (admitted : Lists.Admitted body.instrs.toList)
    (left : BlockExec calls body frame memory leftExit leftFrame leftMemory)
    (right : BlockExec calls body frame memory rightExit rightFrame rightMemory) :
    leftExit = rightExit ∧ leftFrame = rightFrame ∧ leftMemory = rightMemory := by
  obtain ⟨sameFrame, sameMemory⟩ := instructions admitted left.1 right.1
  subst rightFrame
  subst rightMemory
  exact ⟨term left.2 right.2, rfl, rfl⟩

end Silmaril.Compiler.Native.Optimize.Validation.Determinism
