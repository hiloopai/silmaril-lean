module

public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Soundness.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Floating.Soundness
open Silmaril.Machine Silmaril.Compile
open Effects.Soundness

theorem instruction_registers (calls : OpenCalls) (instruction : Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Floating.AdmittedInstr instruction)
    (executed : InstructionExec calls instruction frame memory final finalMemory) :
    ∀ reg, reg ∉ Validation.defs instruction → final.get reg = frame.get reg := by
  cases instruction with
  | op operation =>
    cases executed with
    | op actual => exact op_registers operation frame final memory finalMemory actual
  | fop operation dest left right =>
    cases executed with
    | fop actual =>
      obtain ⟨x, _, y, _, written⟩ : ∃ x, frame.get left = some x ∧ ∃ y,
          frame.get right = some y ∧ frame.set dest (operation.eval x y) = final := by
        simpa only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] using actual
      rw [← written]
      exact (PureSoundness.set_preserves frame dest (operation.eval x y)).2
  | addr dest symbol offset | call symbol args results | callIndirect target args results =>
    cases admitted

theorem instructions_registers (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Floating.Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory final finalMemory) :
    ∀ reg, reg ∉ instructions.flatMap Validation.defs → final.get reg = frame.get reg := by
  induction executed with
  | nil => exact fun _ _ => rfl
  | @cons instruction rest frame memory middle middleMemory final finalMemory first later ih =>
    have firstPreserves := instruction_registers calls instruction frame middle memory middleMemory
      (admitted instruction (by simp)) first
    have tailPreserves := ih (fun instruction member => admitted instruction (by simp [member]))
    intro reg outside
    have split : reg ∉ Validation.defs instruction ∧ reg ∉ rest.flatMap Validation.defs := by
      simpa only [List.flatMap_cons, List.mem_append, not_or] using outside
    exact (tailPreserves reg split.2).trans (firstPreserves reg split.1)

/-- Acceptance derives both the actual effectful candidate run and equality
of every original low register, including unwritten partial-frame entries. -/
theorem accepted_block_refines (calls : OpenCalls) (base : Nat) (source candidate : Mir.Block)
    (frame sourceFrame : Lir.Frame Nat) (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceAdmitted : Floating.Admitted source.instrs.toList)
    (candidateAdmitted : Floating.Admitted candidate.instrs.toList)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory)
    (accepted : check base source candidate = true) :
    ∃ candidateFrame values, BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (∀ reg, reg < base → candidateFrame.get reg = sourceFrame.get reg) ∧
      (Acceptance.observedRegs source).mapM sourceFrame.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  obtain ⟨candidateFrame, values, candidateExecuted, sameSlots, sourceRead, candidateRead⟩ :=
    Candidate.accepted_block_success calls base source candidate frame sourceFrame memory sourceMemory exit
      sourceAdmitted candidateAdmitted sourceExecuted accepted
  have sourcePreserves := instructions_registers calls source.instrs.toList frame sourceFrame memory sourceMemory
    sourceAdmitted sourceExecuted.1
  have candidatePreserves := instructions_registers calls candidate.instrs.toList frame candidateFrame memory sourceMemory
    candidateAdmitted candidateExecuted.1
  have facts : Acceptance.Accepted base source candidate :=
    (Acceptance.check_eq_true_iff base source candidate).mp accepted
  refine ⟨candidateFrame, values, candidateExecuted, sameSlots, ?_, sourceRead, candidateRead⟩
  intro reg below
  by_cases observed : reg ∈ Acceptance.observedRegs source
  · exact (PureSoundness.mapM_agrees _ sourceFrame.get candidateFrame.get values sourceRead candidateRead reg observed).symm
  · show candidateFrame.get reg = sourceFrame.get reg
    have sourceOutside : reg ∉ source.instrs.toList.flatMap Validation.defs := by
      simpa only [Acceptance.observedRegs, List.mem_dedup] using observed
    have candidateOutside : reg ∉ candidate.instrs.toList.flatMap Validation.defs := by
      intro written
      obtain ⟨instruction, member, defined⟩ := List.mem_flatMap.mp written
      have allowed : base ≤ reg ∨ reg ∈ Acceptance.observedRegs source :=
        Acceptance.candidate_write base source candidate facts instruction (by simpa using member) reg defined
      rcases allowed with fresh | original
      · omega
      · exact observed original
    exact (candidatePreserves reg candidateOutside).trans (sourcePreserves reg sourceOutside).symm

/-- Actual checker soundness for floating instructions and all primitives,
including finite loads, stores, slots and successful faulting arithmetic. -/
theorem check_sound (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Floating.Admitted source.instrs.toList)
    (candidateAdmitted : Floating.Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) : Preserves base source candidate := by
  intro calls frame sourceFrame memory sourceMemory exit sourceExecuted
  obtain ⟨candidateFrame, values, candidateExecuted, sameSlots, sameRegisters, sourceRead, candidateRead⟩ :=
    accepted_block_refines calls base source candidate frame sourceFrame memory sourceMemory exit
      sourceAdmitted candidateAdmitted sourceExecuted accepted
  exact ⟨candidateFrame, candidateExecuted, sameSlots, sameRegisters⟩

end Silmaril.Compiler.Native.Optimize.Validation.Floating.Soundness
