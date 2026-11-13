module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Soundness.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects.Soundness
open Silmaril.Machine Silmaril.Compile

theorem op_registers (operation : Lir.Op Nat) (frame final : Lir.Frame Nat)
    (memory finalMemory : Lir.Memory) (executed : operation.exec frame memory = some (final, finalMemory)) :
    ∀ reg, reg ∉ Validation.defs (.op operation) → final.get reg = frame.get reg := by
  cases operation with
  | const dest value =>
    have result : frame.set dest value = final ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] using executed
    exact result.1 ▸ (PureSoundness.set_preserves frame dest value).2
  | move dest source =>
    have result : ∃ value, frame.get source = some value ∧
        frame.set dest value = final ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨value, _, written, _⟩ := result
    exact written ▸ (PureSoundness.set_preserves frame dest value).2
  | unary operation dest source =>
    have result : ∃ value, frame.get source = some value ∧
        frame.set dest (operation.eval value) = final ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨value, _, written, _⟩ := result
    exact written ▸ (PureSoundness.set_preserves frame dest (operation.eval value)).2
  | binary operation dest left right =>
    have result : ∃ x, frame.get left = some x ∧ ∃ y, frame.get right = some y ∧
        ∃ value, operation.eval x y = some value ∧ frame.set dest value = final ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨_, _, _, _, value, _, written, _⟩ := result
    exact written ▸ (PureSoundness.set_preserves frame dest value).2
  | load width extension dest base offset =>
    have result : ∃ address, frame.get base = some address ∧ ∃ value,
        memory.load width extension (address.toNat + offset) = some value ∧
        frame.set dest value = final ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨_, _, value, _, written, _⟩ := result
    exact written ▸ (PureSoundness.set_preserves frame dest value).2
  | store width base offset source =>
    have result : ∃ address, frame.get base = some address ∧ ∃ value, frame.get source = some value ∧
        ∃ after, memory.store width (address.toNat + offset) value = some after ∧
          frame = final ∧ after = finalMemory := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨_, _, _, _, _, _, same, _⟩ := result
    exact same ▸ fun _ _ => rfl
  | slotGet dest slot =>
    have result : ∃ value, frame.slots slot = some value ∧
        frame.set dest value = final ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨value, _, written, _⟩ := result
    exact written ▸ (PureSoundness.set_preserves frame dest value).2
  | slotSet slot source =>
    have result : ∃ value, frame.get source = some value ∧
        frame.setSlot slot value = final ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨_, _, written, _⟩ := result
    exact written ▸ fun _ _ => rfl

theorem instruction_registers (calls : OpenCalls) (instruction : Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Effects.AdmittedInstr instruction)
    (executed : InstructionExec calls instruction frame memory final finalMemory) :
    ∀ reg, reg ∉ Validation.defs instruction → final.get reg = frame.get reg := by
  cases instruction with
  | op operation =>
    cases executed with
    | op actual => exact op_registers operation frame final memory finalMemory actual
  | fop operation dest left right | addr dest symbol offset | call symbol args results | callIndirect target args results =>
    cases admitted

theorem instructions_registers (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Effects.Admitted instructions)
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
    (sourceAdmitted : Effects.Admitted source.instrs.toList)
    (candidateAdmitted : Effects.Admitted candidate.instrs.toList)
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

/-- Actual checker soundness for all primitive instructions, including finite
loads, stores, slots and successful potentially faulting arithmetic. -/
theorem check_sound (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Effects.Admitted source.instrs.toList)
    (candidateAdmitted : Effects.Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) : Preserves base source candidate := by
  intro calls frame sourceFrame memory sourceMemory exit sourceExecuted
  obtain ⟨candidateFrame, values, candidateExecuted, sameSlots, sameRegisters, sourceRead, candidateRead⟩ :=
    accepted_block_refines calls base source candidate frame sourceFrame memory sourceMemory exit
      sourceAdmitted candidateAdmitted sourceExecuted accepted
  exact ⟨candidateFrame, candidateExecuted, sameSlots, sameRegisters⟩

end Silmaril.Compiler.Native.Optimize.Validation.Effects.Soundness
