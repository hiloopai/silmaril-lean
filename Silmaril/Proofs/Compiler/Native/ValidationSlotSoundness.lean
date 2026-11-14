module

public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Candidate.Thms
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Slots
open Silmaril.Machine Silmaril.Compile
open Validation.Roots

namespace Soundness

theorem accepted_block_success_with_reads (calls : OpenCalls) (base : Nat)
    (source candidate : Mir.Block) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory)
    (sourceAdmitted : Admitted source.instrs.toList)
    (candidateAdmitted : Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) (values : List Lir.Word)
    (sourceRead : (Acceptance.observedRegs source).mapM sourceFrame.get = some values) :
    ∃ candidateFrame, BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  have facts : Acceptance.Accepted base source candidate :=
    (Acceptance.check_eq_true_iff base source candidate).mp accepted
  obtain ⟨sameMemory, sourceMeaning, sourceResult⟩ :=
    Source.source_block_with_reads calls source frame sourceFrame memory sourceMemory exit
      sourceExecuted sourceAdmitted (Acceptance.observedRegs source) values sourceRead
  change Observation.BlockResult {} (Acceptance.sourceRun source).2 sourceFrame
    (Acceptance.sourceRun source).1.1 (Acceptance.sourceRun source).1.2
    exit values (Total.initialMeaning frame) sourceMeaning at sourceResult
  obtain ⟨candidateExit, candidateFrame, candidateValues, candidateMeaning,
      candidateExecuted, candidateRead, candidateResult⟩ :=
    Candidate.seeded_block_success calls candidate candidateAdmitted (Acceptance.observedRegs source)
      frame sourceFrame memory (Acceptance.sourceRun source).2 sourceMeaning
      sourceResult.term.result sourceResult.term.total facts.partialLeaves
  change Observation.BlockResult { nodes := (Acceptance.sourceRun source).2.nodes }
    (Acceptance.candidateRun source candidate).2 candidateFrame
    (Acceptance.candidateRun source candidate).1.1 (Acceptance.candidateRun source candidate).1.2
    candidateExit candidateValues sourceMeaning candidateMeaning at candidateResult
  have sourceExit : Observation.termExit candidateMeaning (Acceptance.sourceRun source).1.1 = some exit :=
    (Observation.termExit_preserved _ candidateResult.term.result.extension
      sourceResult.term.wellScoped).trans sourceResult.term.selected
  rw [facts.term] at sourceExit
  have exitSame : candidateExit = exit := Option.some.inj (candidateResult.term.selected.symm.trans sourceExit)
  have sourceValues : (Acceptance.sourceRun source).1.2.mapM candidateMeaning.value = some values :=
    (Observation.values_preserved _ candidateResult.term.result.extension
      sourceResult.observedBounded).trans sourceResult.observed
  rw [facts.observed] at sourceValues
  have valuesSame : candidateValues = values := Option.some.inj (candidateResult.observed.symm.trans sourceValues)
  have slotsSame : candidateFrame.slots = sourceFrame.slots :=
    states_slots_agree (Acceptance.sourceRun source).2 (Acceptance.candidateRun source candidate).2
      sourceFrame candidateFrame sourceMeaning candidateMeaning sourceResult.term.result.rooted
      candidateResult.term.result.rooted candidateResult.term.result.extension candidateResult.term.result.grows facts.slots
  rw [sameMemory]
  exact ⟨candidateFrame, exitSame ▸ candidateExecuted, slotsSame, valuesSame ▸ candidateRead⟩

theorem op_registers_preserve (operation : Lir.Op Nat) (frame frame' : Lir.Frame Nat)
    (memory memory' : Lir.Memory) (admitted : AdmittedOp operation)
    (executed : operation.exec frame memory = some (frame', memory')) :
    ∀ reg, reg ∉ Validation.defs (.op operation) → frame'.get reg = frame.get reg := by
  cases operation with
  | const dest word => exact (PureSoundness.op_preserves (.const dest word) frame frame' memory memory' admitted executed).2
  | move dest source => exact (PureSoundness.op_preserves (.move dest source) frame frame' memory memory' admitted executed).2
  | unary op dest source => exact (PureSoundness.op_preserves (.unary op dest source) frame frame' memory memory' admitted executed).2
  | binary op dest left right => exact (PureSoundness.op_preserves (.binary op dest left right) frame frame' memory memory' admitted executed).2
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.slots slot = some word ∧
        (frame.set dest word = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    rw [← output.1]
    exact (PureSoundness.set_preserves frame dest word).2
  | slotSet slot source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.setSlot slot word = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    rw [← output.1]
    exact fun _ _ => rfl

theorem instruction_registers_preserve (calls : OpenCalls) (instruction : Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : AdmittedInstr instruction)
    (executed : InstructionExec calls instruction frame memory frame' memory') :
    ∀ reg, reg ∉ Validation.defs instruction → frame'.get reg = frame.get reg := by
  cases instruction with
  | op operation =>
    cases executed with
    | op actual => exact op_registers_preserve operation frame frame' memory memory' admitted actual
  | fop op dest left right => cases admitted
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem instructions_registers_preserve (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory frame' memory') :
    ∀ reg, reg ∉ instructions.flatMap Validation.defs → frame'.get reg = frame.get reg := by
  induction executed with
  | nil => exact fun _ _ => rfl
  | @cons instruction rest frame memory middle middleMemory frame' memory' first later ih =>
    have firstPreserves := instruction_registers_preserve calls instruction frame middle memory middleMemory
      (admitted instruction (by simp)) first
    have tailPreserves := ih (fun i member => admitted i (by simp [member]))
    intro reg outside
    have split : reg ∉ Validation.defs instruction ∧ reg ∉ rest.flatMap Validation.defs := by
      simpa only [List.flatMap_cons, List.mem_append, not_or] using outside
    exact (tailPreserves reg split.2).trans (firstPreserves reg split.1)

theorem accepted_block_refines_with_reads (calls : OpenCalls) (base : Nat)
    (source candidate : Mir.Block) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory)
    (sourceAdmitted : Admitted source.instrs.toList)
    (candidateAdmitted : Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) (values : List Lir.Word)
    (sourceRead : (Acceptance.observedRegs source).mapM sourceFrame.get = some values) :
    ∃ candidateFrame, BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (∀ reg, reg < base → candidateFrame.get reg = sourceFrame.get reg) ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  obtain ⟨candidateFrame, candidateExecuted, slotsSame, candidateRead⟩ :=
    accepted_block_success_with_reads calls base source candidate frame sourceFrame memory sourceMemory exit
      sourceExecuted sourceAdmitted candidateAdmitted accepted values sourceRead
  have sourcePreserves : ∀ reg, reg ∉ source.instrs.toList.flatMap Validation.defs → sourceFrame.get reg = frame.get reg :=
    instructions_registers_preserve calls source.instrs.toList frame sourceFrame memory sourceMemory sourceAdmitted sourceExecuted.1
  have candidatePreserves : ∀ reg, reg ∉ candidate.instrs.toList.flatMap Validation.defs → candidateFrame.get reg = frame.get reg :=
    instructions_registers_preserve calls candidate.instrs.toList frame candidateFrame memory sourceMemory candidateAdmitted candidateExecuted.1
  have facts : Acceptance.Accepted base source candidate :=
    (Acceptance.check_eq_true_iff base source candidate).mp accepted
  refine ⟨candidateFrame, candidateExecuted, slotsSame, ?_, candidateRead⟩
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
      rcases allowed with fresh | old
      · omega
      · exact observed old
    exact (candidatePreserves reg candidateOutside).trans (sourcePreserves reg sourceOutside).symm

/-- Actual checker acceptance preserves every finite successful source block
execution in the admitted integer/slot fragment. Source observations and the candidate
execution are derived; the original incoming frame may be partial. -/
theorem accepted_block_refines (calls : OpenCalls) (base : Nat)
    (source candidate : Mir.Block) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory)
    (sourceAdmitted : Admitted source.instrs.toList)
    (candidateAdmitted : Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) :
    ∃ candidateFrame values,
      BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (∀ reg, reg < base → candidateFrame.get reg = sourceFrame.get reg) ∧
      (Acceptance.observedRegs source).mapM sourceFrame.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  obtain ⟨values, sourceRead⟩ := Source.observed_success calls source frame sourceFrame memory sourceMemory
    sourceAdmitted sourceExecuted.1
  obtain ⟨candidateFrame, candidateExecuted, slotsSame, registersSame, candidateRead⟩ :=
    accepted_block_refines_with_reads calls base source candidate frame sourceFrame memory sourceMemory exit
      sourceExecuted sourceAdmitted candidateAdmitted accepted values sourceRead
  exact ⟨candidateFrame, values, candidateExecuted, slotsSame, registersSame, sourceRead, candidateRead⟩

/-- Soundness of the real checker for its explicitly admitted integer/slot fragment.
No candidate execution or successful read is a premise. -/
theorem check_sound (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Admitted source.instrs.toList)
    (candidateAdmitted : Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) : PureSoundness.Preserves base source candidate := by
  intro calls frame sourceFrame memory sourceMemory exit sourceExecuted
  obtain ⟨candidateFrame, values, candidateExecuted, slotsSame, registersSame, sourceRead, candidateRead⟩ :=
    accepted_block_refines calls base source candidate frame sourceFrame memory sourceMemory exit
      sourceExecuted sourceAdmitted candidateAdmitted accepted
  exact ⟨candidateFrame, candidateExecuted, slotsSame, registersSame⟩

end Soundness
end Silmaril.Compiler.Native.Optimize.Validation.Slots
