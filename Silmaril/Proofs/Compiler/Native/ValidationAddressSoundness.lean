module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Soundness.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Soundness
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract

/-- Mixed successful instructions preserve every register they do not define.
Address execution is a real register write; ordinary op/fop facts are reused. -/
theorem instruction_registers (calls : OpenCalls) (instruction : Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : AdmittedInstr instruction)
    (executed : InstructionExec calls instruction frame memory final finalMemory) :
    ∀ reg, reg ∉ Validation.defs instruction → final.get reg = frame.get reg := by
  cases instruction with
  | op operation =>
    exact Floating.Soundness.instruction_registers calls (.op operation)
      frame final memory finalMemory trivial executed
  | fop operation dest left right =>
    exact Floating.Soundness.instruction_registers calls
      (.fop operation dest left right) frame final memory finalMemory trivial executed
  | addr dest symbol offset =>
    cases executed with
    | addr resolved => exact (PureSoundness.set_preserves frame dest _).2
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem instructions_registers (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Admitted instructions)
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

/-- Real source execution and actual boolean acceptance derive the candidate's
same exit, source final memory, whole slots and all observed source values.
No completed source invariant, candidate execution or chosen load map is supplied. -/
theorem accepted_block_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (base : Nat) (source candidate : Mir.Block) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceAdmitted : Admitted source.instrs.toList) (candidateAdmitted : Admitted candidate.instrs.toList)
    (sourceExecuted : BlockExec (calls units placement) source frame memory exit sourceFrame sourceMemory)
    (accepted : check base source candidate = true) :
    ∃ candidateFrame values,
      BlockExec (calls units placement) candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (Acceptance.observedRegs source).mapM sourceFrame.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  have facts : Acceptance.Accepted base source candidate := (Acceptance.check_eq_true_iff base source candidate).mp accepted
  obtain ⟨meaning, sourceWords, values, sourceRead, sourceResult⟩ :=
    Source.source_block units placement source frame sourceFrame memory sourceMemory exit sourceAdmitted sourceExecuted
  obtain ⟨candidateExit, candidateFrame, candidateValues, newMeaning, candidateExecuted, candidateRead, candidateResult, _, _⟩ :=
    Candidate.accepted_block_result units placement base source candidate candidateAdmitted frame sourceFrame memory sourceMemory
      sourceWords meaning sourceResult.invariant accepted
  obtain ⟨sameExit, sameValues, slotsSame⟩ := Validation.Effects.Candidate.accepted_results_match sourceResult candidateResult facts
  exact ⟨candidateFrame, values, sameExit ▸ candidateExecuted, slotsSame, sourceRead, sameValues ▸ candidateRead⟩

/-- All original optional register values below the fresh boundary agree,
including registers absent from the genuine partial incoming frame. -/
theorem accepted_block_refines (units : Array Mir.Unit) (placement : MirSem.Placement)
    (base : Nat) (source candidate : Mir.Block) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceAdmitted : Admitted source.instrs.toList) (candidateAdmitted : Admitted candidate.instrs.toList)
    (sourceExecuted : BlockExec (calls units placement) source frame memory exit sourceFrame sourceMemory)
    (accepted : check base source candidate = true) :
    ∃ candidateFrame values,
      BlockExec (calls units placement) candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (∀ reg, reg < base → candidateFrame.get reg = sourceFrame.get reg) ∧
      (Acceptance.observedRegs source).mapM sourceFrame.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  obtain ⟨candidateFrame, values, candidateExecuted, sameSlots, sourceRead, candidateRead⟩ :=
    accepted_block_success units placement base source candidate frame sourceFrame memory sourceMemory exit
      sourceAdmitted candidateAdmitted sourceExecuted accepted
  have sourcePreserves := instructions_registers (calls units placement) source.instrs.toList frame sourceFrame memory sourceMemory
    sourceAdmitted sourceExecuted.1
  have candidatePreserves := instructions_registers (calls units placement) candidate.instrs.toList frame candidateFrame memory sourceMemory
    candidateAdmitted candidateExecuted.1
  have facts : Acceptance.Accepted base source candidate := (Acceptance.check_eq_true_iff base source candidate).mp accepted
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

/-- Same-frame ordinary-address checker soundness at the actual resolver. -/
theorem check_sound (units : Array Mir.Unit) (placement : MirSem.Placement)
    (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Admitted source.instrs.toList) (candidateAdmitted : Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) : Preserves units placement base source candidate := by
  intro frame sourceFrame memory sourceMemory exit sourceExecuted
  obtain ⟨candidateFrame, _, candidateExecuted, sameSlots, sameRegisters, _, _⟩ :=
    accepted_block_refines units placement base source candidate frame sourceFrame memory sourceMemory exit
      sourceAdmitted candidateAdmitted sourceExecuted accepted
  exact ⟨candidateFrame, candidateExecuted, sameSlots, sameRegisters⟩

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Soundness
