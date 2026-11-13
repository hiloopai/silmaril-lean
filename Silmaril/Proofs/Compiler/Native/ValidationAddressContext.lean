module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Context.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Context
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract
open PureSoundness Validation.Effects.Context Validation.Floating.Context

theorem instructions_transport (calls : OpenCalls) (base : Nat) (instructions : List Mir.Instr)
    (admitted : Admitted instructions)
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
    have headAdmitted : AdmittedInstr instruction := admitted instruction (by simp)
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
      | addr dest symbol offset =>
        cases first with
        | addr resolved =>
          exact ⟨target.set dest _, .addr resolved, Validation.Context.agrees_set agrees dest _⟩
      | call symbol args results => cases headAdmitted
      | callIndirect reg args results => cases headAdmitted
    obtain ⟨targetMiddle, headRun, middleAgree⟩ := step
    obtain ⟨targetFinal, tailRun, finalAgree⟩ := ih
      (fun i h => admitted i (by simp [h])) (fun i h => bounds i (by simp [h])) targetMiddle middleAgree
    exact ⟨targetFinal, .cons headRun tailRun, finalAgree⟩


theorem block_transport (calls : OpenCalls) (base : Nat) (block : Mir.Block)
    (admitted : Admitted block.instrs.toList) (bounds : Validation.Context.ReadsBelow base block)
    (source target sourceFinal : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block source memory exit sourceFinal finalMemory) :
    ∃ targetFinal, BlockExec calls block target memory exit targetFinal finalMemory ∧
      FrameAgrees base sourceFinal targetFinal := by
  obtain ⟨targetFinal, bodyRun, finalAgree⟩ := instructions_transport calls base block.instrs.toList
    admitted bounds.1 source target sourceFinal agrees memory finalMemory executed.1
  exact ⟨targetFinal, ⟨bodyRun, Validation.Context.term_transport base block.term bounds.2 sourceFinal targetFinal finalAgree exit executed.2⟩, finalAgree⟩

/-- Transport the actual mixed source run first, then use the existing
same-frame checker theorem. No candidate run or completed invariant is assumed. -/
theorem checked_contextual (units : Array Mir.Unit) (placement : MirSem.Placement)
    (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Admitted source.instrs.toList)
    (candidateAdmitted : Admitted candidate.instrs.toList)
    (bounds : Validation.Context.ReadsBelow base source) (accepted : check base source candidate = true) :
    Preserves units placement base source candidate := by
  intro sourceInput candidateInput sourceFinal memory finalMemory exit agrees executed
  obtain ⟨transportedFinal, transportedRun, transportedAgree⟩ := block_transport
    (calls units placement) base source sourceAdmitted bounds sourceInput candidateInput sourceFinal
      agrees memory finalMemory exit executed
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ := Soundness.check_sound
    units placement base source candidate sourceAdmitted candidateAdmitted accepted candidateInput transportedFinal
      memory finalMemory exit transportedRun
  exact ⟨candidateFinal, candidateRun, Validation.Context.agrees_trans transportedAgree candidateAgree⟩

/-- Source definitions in the real function bound every actual checker output.
No candidate inventory or manually chosen fresh range supplies this bound. -/
theorem function_observed_below {function : Mir.Func} {source : Mir.Block}
    (member : source ∈ function.blocks.toList) :
    ∀ reg ∈ Acceptance.observedRegs source, reg < freshBase function := by
  intro reg observed
  obtain ⟨instruction, inBlock, written⟩ := List.mem_flatMap.mp
    (List.mem_dedup.mp observed)
  have same : Validation.defs instruction = Optimize.defs instruction := by cases instruction <;> rfl
  rw [same] at written
  exact LambdaSSA.SourceView.freshBase_defs member inBlock written

/-- Optional low-register agreement transports ordered output reads, including
failure of an absent read. This helper is shared by checker and caller tails. -/
theorem output_reads_agree (base : Nat) (registers : List Nat)
    (source target : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (bounds : ∀ reg ∈ registers, reg < base) :
    registers.mapM target.get = registers.mapM source.get := by
  induction registers with
  | nil => rfl
  | cons reg rest ih =>
    have first := agrees.registers reg (bounds reg (by simp))
    have later := ih (fun other member => bounds other (by simp [member]))
    simp only [List.mapM_cons, first, later]

/-- Actual source execution constructs defined source observations; the real
function bound and final partial-frame agreement derive the same target reads. -/
theorem function_output_reads (units : Array Mir.Unit) (placement : MirSem.Placement)
    {function : Mir.Func} {source : Mir.Block} (member : source ∈ function.blocks.toList)
    (admitted : Admitted source.instrs.toList)
    (sourceInput sourceFinal targetFinal : Lir.Frame Nat)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec (calls units placement) source sourceInput memory exit sourceFinal finalMemory)
    (agrees : FrameAgrees (freshBase function) sourceFinal targetFinal) :
    ∃ values, (Acceptance.observedRegs source).mapM sourceFinal.get = some values ∧
      (Acceptance.observedRegs source).mapM targetFinal.get = some values := by
  obtain ⟨_, _, values, sourceRead, _⟩ :=
    Source.source_block units placement source sourceInput sourceFinal memory finalMemory exit admitted executed
  refine ⟨values, sourceRead, ?_⟩
  rw [output_reads_agree (freshBase function) _ sourceFinal targetFinal agrees (function_observed_below member)]
  exact sourceRead

/-- Real function membership supplies all source read bounds. Different incoming
frames yield the same exact exit/memory, all slots/low optional registers and
ordered checker output reads, solely from actual source execution and checking. -/
theorem function_checked_contextual (units : Array Mir.Unit) (placement : MirSem.Placement)
    {function : Mir.Func} {source candidate : Mir.Block}
    (member : source ∈ function.blocks.toList)
    (sourceAdmitted : Admitted source.instrs.toList)
    (candidateAdmitted : Admitted candidate.instrs.toList)
    (accepted : check (freshBase function) source candidate = true)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec (calls units placement) source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal values,
      BlockExec (calls units placement) candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal ∧
      (Acceptance.observedRegs source).mapM sourceFinal.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFinal.get = some values := by
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ := checked_contextual units placement
    (freshBase function) source candidate sourceAdmitted candidateAdmitted (Validation.Context.freshBase_reads member)
      accepted sourceInput candidateInput sourceFinal memory finalMemory exit agrees executed
  obtain ⟨values, sourceRead, candidateRead⟩ := function_output_reads units placement member sourceAdmitted
    sourceInput sourceFinal candidateFinal memory finalMemory exit executed candidateAgree
  exact ⟨candidateFinal, values, candidateRun, candidateAgree, sourceRead, candidateRead⟩

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Context
