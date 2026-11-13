module

public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Context.Defs
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Slots.Context
open Silmaril.Machine Silmaril.Compile
open PureSoundness

theorem agrees_setSlot {base : Nat} {source target : Lir.Frame Nat}
    (agrees : FrameAgrees base source target) (slot : Nat) (word : Lir.Word) :
    FrameAgrees base (source.setSlot slot word) (target.setSlot slot word) := by
  refine ⟨?_, agrees.registers⟩
  change (fun other => if other = slot then some word else target.slots other) =
    (fun other => if other = slot then some word else source.slots other)
  rw [agrees.slots]

/-- Actual slot writes and reads transport across different partial incoming
frames using whole-slot equality and original register read bounds. -/
theorem op_transport (base : Nat) (operation : Lir.Op Nat) (admitted : Slots.AdmittedOp operation)
    (bounds : ∀ reg ∈ Mir.DeadCode.opUses operation, reg < base)
    (source target sourceFinal : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (memory finalMemory : Lir.Memory) (executed : operation.exec source memory = some (sourceFinal, finalMemory)) :
    ∃ targetFinal, operation.exec target memory = some (targetFinal, finalMemory) ∧
      FrameAgrees base sourceFinal targetFinal := by
  cases operation with
  | const dest word => exact Validation.Context.op_transport base (.const dest word) admitted bounds source target sourceFinal agrees memory finalMemory executed
  | move dest reg => exact Validation.Context.op_transport base (.move dest reg) admitted bounds source target sourceFinal agrees memory finalMemory executed
  | unary op dest reg => exact Validation.Context.op_transport base (.unary op dest reg) admitted bounds source target sourceFinal agrees memory finalMemory executed
  | binary op dest left right => exact Validation.Context.op_transport base (.binary op dest left right) admitted bounds source target sourceFinal agrees memory finalMemory executed
  | load width ext dest reg offset => cases admitted
  | store width reg offset source => cases admitted
  | slotGet dest slot =>
    have output : ∃ word, source.slots slot = some word ∧ source.set dest word = sourceFinal ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨word, read, final, sameMemory⟩ := output
    have targetRead : target.slots slot = some word := (congrFun agrees.slots slot).trans read
    rw [← final, ← sameMemory]
    exact ⟨target.set dest word, by simp only [Lir.Op.exec, targetRead, Option.map_some],
      Validation.Context.agrees_set agrees dest word⟩
  | slotSet slot reg =>
    have output : ∃ word, source.get reg = some word ∧ source.setSlot slot word = sourceFinal ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨word, read, final, sameMemory⟩ := output
    have targetRead : target.get reg = some word :=
      (agrees.registers reg (bounds reg (by simp [Mir.DeadCode.opUses]))).trans read
    rw [← final, ← sameMemory]
    exact ⟨target.setSlot slot word, by simp only [Lir.Op.exec, targetRead, Option.map_some], agrees_setSlot agrees slot word⟩

theorem instructions_transport (calls : OpenCalls) (base : Nat) (instructions : List Mir.Instr)
    (admitted : Slots.Admitted instructions)
    (bounds : ∀ instruction ∈ instructions, ∀ reg ∈ Optimize.uses instruction, reg < base)
    (source target sourceFinal : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (memory finalMemory : Lir.Memory)
    (executed : InstructionsExec calls instructions source memory sourceFinal finalMemory) :
    ∃ targetFinal, InstructionsExec calls instructions target memory targetFinal finalMemory ∧
      FrameAgrees base sourceFinal targetFinal := by
  induction executed generalizing target with
  | nil => exact ⟨target, .nil, agrees⟩
  | @cons instruction rest source memory middle middleMemory sourceFinal finalMemory first later ih =>
    show ∃ targetFinal, InstructionsExec calls (instruction :: rest) target memory targetFinal finalMemory ∧
      FrameAgrees base sourceFinal targetFinal
    have headAdmitted : Slots.AdmittedInstr instruction := admitted instruction (by simp)
    have step : ∃ targetMiddle, InstructionExec calls instruction target memory targetMiddle middleMemory ∧
        FrameAgrees base middle targetMiddle := by
      cases instruction with
      | op op =>
        cases first with
        | op actual =>
          obtain ⟨targetMiddle, run, nextAgree⟩ := op_transport base op headAdmitted
            (bounds (.op op) (by simp)) source target middle agrees memory middleMemory actual
          exact ⟨targetMiddle, .op run, nextAgree⟩
      | fop op dest left right => cases headAdmitted
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect reg args results => cases headAdmitted
    obtain ⟨targetMiddle, headRun, middleAgree⟩ := step
    obtain ⟨targetFinal, tailRun, finalAgree⟩ := ih
      (fun i h => admitted i (by simp [h])) (fun i h => bounds i (by simp [h])) targetMiddle middleAgree
    exact ⟨targetFinal, .cons headRun tailRun, finalAgree⟩


theorem block_transport (calls : OpenCalls) (base : Nat) (block : Mir.Block)
    (admitted : Slots.Admitted block.instrs.toList) (bounds : Validation.Context.ReadsBelow base block)
    (source target sourceFinal : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block source memory exit sourceFinal finalMemory) :
    ∃ targetFinal, BlockExec calls block target memory exit targetFinal finalMemory ∧
      FrameAgrees base sourceFinal targetFinal := by
  obtain ⟨targetFinal, bodyRun, finalAgree⟩ := instructions_transport calls base block.instrs.toList
    admitted bounds.1 source target sourceFinal agrees memory finalMemory executed.1
  exact ⟨targetFinal, ⟨bodyRun, Validation.Context.term_transport base block.term bounds.2 sourceFinal targetFinal finalAgree exit executed.2⟩, finalAgree⟩

/-- A checked pure block refines source execution even when incoming frames
already differ in the fresh range, as they do at later CFG block boundaries. -/
theorem checked_contextual (calls : OpenCalls) (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Slots.Admitted source.instrs.toList)
    (candidateAdmitted : Slots.Admitted candidate.instrs.toList) (bounds : Validation.Context.ReadsBelow base source)
    (accepted : check base source candidate = true)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees base sourceInput candidateInput) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees base sourceFinal candidateFinal := by
  obtain ⟨transportedFinal, transportedRun, transportedAgree⟩ := block_transport calls base source sourceAdmitted bounds
    sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ :=
    Slots.Soundness.check_sound base source candidate sourceAdmitted candidateAdmitted accepted calls candidateInput transportedFinal
      memory finalMemory exit transportedRun
  exact ⟨candidateFinal, candidateRun, Validation.Context.agrees_trans transportedAgree candidateAgree⟩



theorem function_checked_contextual {function : Mir.Func} {source candidate : Mir.Block}
    (member : source ∈ function.blocks.toList)
    (sourceAdmitted : Slots.Admitted source.instrs.toList)
    (candidateAdmitted : Slots.Admitted candidate.instrs.toList)
    (accepted : check (freshBase function) source candidate = true)
    (calls : OpenCalls) (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal :=
  checked_contextual calls (freshBase function) source candidate sourceAdmitted candidateAdmitted
    (Validation.Context.freshBase_reads member) accepted sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed

end Silmaril.Compiler.Native.Optimize.Validation.Slots.Context
