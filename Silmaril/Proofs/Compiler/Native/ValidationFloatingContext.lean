module

public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Context.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Floating.Context
open Silmaril.Machine Silmaril.Compile
open PureSoundness Effects.Context

/-- Both actual floating operand reads transport; evaluation is the identical
existing word function and never changes memory. -/
theorem fop_transport (base : Nat) (op : Lir.FOp) (dest left right : Nat)
    (bounds : ∀ reg ∈ Optimize.uses (.fop op dest left right), reg < base)
    (source target sourceFinal : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (executed : Lir.FOp.exec op dest left right source = some sourceFinal) :
    ∃ targetFinal, Lir.FOp.exec op dest left right target = some targetFinal ∧
      FrameAgrees base sourceFinal targetFinal := by
  obtain ⟨x, leftRead, y, rightRead, written⟩ : ∃ x, source.get left = some x ∧ ∃ y,
      source.get right = some y ∧ source.set dest (op.eval x y) = sourceFinal := by
    simpa only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] using executed
  have targetLeft : target.get left = some x :=
    (agrees.registers left (bounds left (by simp [Optimize.uses]))).trans leftRead
  have targetRight : target.get right = some y :=
    (agrees.registers right (bounds right (by simp [Optimize.uses]))).trans rightRead
  exact ⟨target.set dest (op.eval x y), by
    simp only [Lir.FOp.exec, targetLeft, targetRight, Option.bind_some, Option.map_some],
    written ▸ Validation.Context.agrees_set agrees dest (op.eval x y)⟩

theorem instructions_transport (calls : OpenCalls) (base : Nat) (instructions : List Mir.Instr)
    (admitted : Floating.Admitted instructions)
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
    have headAdmitted : Floating.AdmittedInstr instruction := admitted instruction (by simp)
    have step : ∃ targetMiddle, InstructionExec calls instruction target memory targetMiddle middleMemory ∧
        FrameAgrees base middle targetMiddle := by
      cases instruction with
      | op op =>
        cases first with
        | op actual =>
          obtain ⟨targetMiddle, run, nextAgree⟩ := op_transport base op
            (bounds (.op op) (by simp)) source target middle agrees memory middleMemory actual
          exact ⟨targetMiddle, .op run, nextAgree⟩
      | fop op dest left right =>
        cases first with
        | fop actual =>
          obtain ⟨targetMiddle, run, nextAgree⟩ := fop_transport base op dest left right
            (bounds (.fop op dest left right) (by simp)) source target middle agrees actual
          exact ⟨targetMiddle, .fop run, nextAgree⟩
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect reg args results => cases headAdmitted
    obtain ⟨targetMiddle, headRun, middleAgree⟩ := step
    obtain ⟨targetFinal, tailRun, finalAgree⟩ := ih
      (fun i h => admitted i (by simp [h])) (fun i h => bounds i (by simp [h])) targetMiddle middleAgree
    exact ⟨targetFinal, .cons headRun tailRun, finalAgree⟩


theorem block_transport (calls : OpenCalls) (base : Nat) (block : Mir.Block)
    (admitted : Floating.Admitted block.instrs.toList) (bounds : Validation.Context.ReadsBelow base block)
    (source target sourceFinal : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block source memory exit sourceFinal finalMemory) :
    ∃ targetFinal, BlockExec calls block target memory exit targetFinal finalMemory ∧
      FrameAgrees base sourceFinal targetFinal := by
  obtain ⟨targetFinal, bodyRun, finalAgree⟩ := instructions_transport calls base block.instrs.toList
    admitted bounds.1 source target sourceFinal agrees memory finalMemory executed.1
  exact ⟨targetFinal, ⟨bodyRun, Validation.Context.term_transport base block.term bounds.2 sourceFinal targetFinal finalAgree exit executed.2⟩, finalAgree⟩

/-- A checked primitive/floating block refines source execution when incoming frames
already differ in the fresh range, as they do at later CFG block boundaries. -/
theorem checked_contextual (calls : OpenCalls) (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Floating.Admitted source.instrs.toList)
    (candidateAdmitted : Floating.Admitted candidate.instrs.toList) (bounds : Validation.Context.ReadsBelow base source)
    (accepted : check base source candidate = true)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees base sourceInput candidateInput) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees base sourceFinal candidateFinal := by
  obtain ⟨transportedFinal, transportedRun, transportedAgree⟩ := block_transport calls base source sourceAdmitted bounds
    sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ :=
    Floating.Soundness.check_sound base source candidate sourceAdmitted candidateAdmitted accepted calls candidateInput transportedFinal
      memory finalMemory exit transportedRun
  exact ⟨candidateFinal, candidateRun, Validation.Context.agrees_trans transportedAgree candidateAgree⟩



theorem function_checked_contextual {function : Mir.Func} {source candidate : Mir.Block}
    (member : source ∈ function.blocks.toList)
    (sourceAdmitted : Floating.Admitted source.instrs.toList)
    (candidateAdmitted : Floating.Admitted candidate.instrs.toList)
    (accepted : check (freshBase function) source candidate = true)
    (calls : OpenCalls) (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal :=
  checked_contextual calls (freshBase function) source candidate sourceAdmitted candidateAdmitted
    (Validation.Context.freshBase_reads member) accepted sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed

end Silmaril.Compiler.Native.Optimize.Validation.Floating.Context
