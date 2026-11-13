module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Context.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects.Context
open Silmaril.Machine Silmaril.Compile
open PureSoundness

theorem agrees_setSlot {base : Nat} {source target : Lir.Frame Nat}
    (agrees : FrameAgrees base source target) (slot : Nat) (word : Lir.Word) :
    FrameAgrees base (source.setSlot slot word) (target.setSlot slot word) := by
  refine ⟨?_, agrees.registers⟩
  change (fun other => if other = slot then some word else target.slots other) =
    (fun other => if other = slot then some word else source.slots other)
  rw [agrees.slots]

/-- Transport the actual successful source primitive across partial incoming
frames agreeing only on the source register range. -/
theorem op_transport (base : Nat) (op : Lir.Op Nat)
    (bounds : ∀ reg ∈ Mir.DeadCode.opUses op, reg < base)
    (source target sourceFinal : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (memory finalMemory : Lir.Memory) (executed : op.exec source memory = some (sourceFinal, finalMemory)) :
    ∃ targetFinal, op.exec target memory = some (targetFinal, finalMemory) ∧
      FrameAgrees base sourceFinal targetFinal := by
  cases op with
  | const dest word =>
    have output : source.set dest word = sourceFinal ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] using executed
    rw [← output.1, ← output.2]
    exact ⟨target.set dest word, rfl, Validation.Context.agrees_set agrees dest word⟩
  | move dest reg =>
    have output : ∃ word, source.get reg = some word ∧ source.set dest word = sourceFinal ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨word, read, final, sameMemory⟩ := output
    have targetRead : target.get reg = some word := (agrees.registers reg (bounds reg (by simp [Mir.DeadCode.opUses]))).trans read
    rw [← final, ← sameMemory]
    exact ⟨target.set dest word, by simp only [Lir.Op.exec, targetRead, Option.map_some], Validation.Context.agrees_set agrees dest word⟩
  | unary operation dest reg =>
    show ∃ targetFinal, (Lir.Op.unary operation dest reg).exec target memory = some (targetFinal, finalMemory) ∧
      FrameAgrees base sourceFinal targetFinal
    have output : ∃ word, source.get reg = some word ∧
        source.set dest (operation.eval word) = sourceFinal ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨word, read, final, sameMemory⟩ := output
    have targetRead : target.get reg = some word := (agrees.registers reg (bounds reg (by simp [Mir.DeadCode.opUses]))).trans read
    rw [← final, ← sameMemory]
    exact ⟨target.set dest (operation.eval word), by simp only [Lir.Op.exec, targetRead, Option.map_some],
      Validation.Context.agrees_set agrees dest (operation.eval word)⟩
  | binary operation dest left right =>
    show ∃ targetFinal, (Lir.Op.binary operation dest left right).exec target memory = some (targetFinal, finalMemory) ∧
      FrameAgrees base sourceFinal targetFinal
    have output : ∃ x, source.get left = some x ∧ ∃ y, source.get right = some y ∧
        ∃ word, operation.eval x y = some word ∧ source.set dest word = sourceFinal ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨x, leftRead, y, rightRead, word, computed, final, sameMemory⟩ := output
    have targetLeft : target.get left = some x :=
      (agrees.registers left (bounds left (by simp [Mir.DeadCode.opUses]))).trans leftRead
    have targetRight : target.get right = some y :=
      (agrees.registers right (bounds right (by simp [Mir.DeadCode.opUses]))).trans rightRead
    rw [← final, ← sameMemory]
    exact ⟨target.set dest word, by
      simp only [Lir.Op.exec, targetLeft, targetRight, computed, Option.bind_some, Option.map_some], Validation.Context.agrees_set agrees dest word⟩
  | load width ext dest reg offset =>
    show ∃ targetFinal, (Lir.Op.load width ext dest reg offset).exec target memory = some (targetFinal, finalMemory) ∧
      FrameAgrees base sourceFinal targetFinal
    have output : ∃ address, source.get reg = some address ∧ ∃ word,
        memory.load width ext (address.toNat + offset) = some word ∧
        source.set dest word = sourceFinal ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨address, read, word, loaded, final, sameMemory⟩ := output
    have targetRead : target.get reg = some address :=
      (agrees.registers reg (bounds reg (by simp [Mir.DeadCode.opUses]))).trans read
    rw [← final, ← sameMemory]
    exact ⟨target.set dest word, by
      simp only [Lir.Op.exec, targetRead, loaded, Option.bind_some, Option.map_some],
      Validation.Context.agrees_set agrees dest word⟩
  | store width reg offset value =>
    show ∃ targetFinal, (Lir.Op.store width reg offset value).exec target memory = some (targetFinal, finalMemory) ∧
      FrameAgrees base sourceFinal targetFinal
    have output : ∃ address, source.get reg = some address ∧ ∃ word, source.get value = some word ∧
        ∃ afterMemory, memory.store width (address.toNat + offset) word = some afterMemory ∧
        source = sourceFinal ∧ afterMemory = finalMemory := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨address, baseRead, word, valueRead, afterMemory, stored, final, sameMemory⟩ := output
    have targetBase : target.get reg = some address :=
      (agrees.registers reg (bounds reg (by simp [Mir.DeadCode.opUses]))).trans baseRead
    have targetValue : target.get value = some word :=
      (agrees.registers value (bounds value (by simp [Mir.DeadCode.opUses]))).trans valueRead
    rw [← final, ← sameMemory]
    exact ⟨target, by
      simp only [Lir.Op.exec, targetBase, targetValue, stored, Option.bind_some, Option.map_some], agrees⟩
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
    (admitted : Effects.Admitted instructions)
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
    have headAdmitted : Effects.AdmittedInstr instruction := admitted instruction (by simp)
    have step : ∃ targetMiddle, InstructionExec calls instruction target memory targetMiddle middleMemory ∧
        FrameAgrees base middle targetMiddle := by
      cases instruction with
      | op op =>
        cases first with
        | op actual =>
          obtain ⟨targetMiddle, run, nextAgree⟩ := op_transport base op
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
    (admitted : Effects.Admitted block.instrs.toList) (bounds : Validation.Context.ReadsBelow base block)
    (source target sourceFinal : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block source memory exit sourceFinal finalMemory) :
    ∃ targetFinal, BlockExec calls block target memory exit targetFinal finalMemory ∧
      FrameAgrees base sourceFinal targetFinal := by
  obtain ⟨targetFinal, bodyRun, finalAgree⟩ := instructions_transport calls base block.instrs.toList
    admitted bounds.1 source target sourceFinal agrees memory finalMemory executed.1
  exact ⟨targetFinal, ⟨bodyRun, Validation.Context.term_transport base block.term bounds.2 sourceFinal targetFinal finalAgree exit executed.2⟩, finalAgree⟩

/-- A checked all-primitive block refines source execution when incoming frames
already differ in the fresh range, as they do at later CFG block boundaries. -/
theorem checked_contextual (calls : OpenCalls) (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Effects.Admitted source.instrs.toList)
    (candidateAdmitted : Effects.Admitted candidate.instrs.toList) (bounds : Validation.Context.ReadsBelow base source)
    (accepted : check base source candidate = true)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees base sourceInput candidateInput) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees base sourceFinal candidateFinal := by
  obtain ⟨transportedFinal, transportedRun, transportedAgree⟩ := block_transport calls base source sourceAdmitted bounds
    sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ :=
    Effects.Soundness.check_sound base source candidate sourceAdmitted candidateAdmitted accepted calls candidateInput transportedFinal
      memory finalMemory exit transportedRun
  exact ⟨candidateFinal, candidateRun, Validation.Context.agrees_trans transportedAgree candidateAgree⟩



theorem function_checked_contextual {function : Mir.Func} {source candidate : Mir.Block}
    (member : source ∈ function.blocks.toList)
    (sourceAdmitted : Effects.Admitted source.instrs.toList)
    (candidateAdmitted : Effects.Admitted candidate.instrs.toList)
    (accepted : check (freshBase function) source candidate = true)
    (calls : OpenCalls) (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal :=
  checked_contextual calls (freshBase function) source candidate sourceAdmitted candidateAdmitted
    (Validation.Context.freshBase_reads member) accepted sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed

end Silmaril.Compiler.Native.Optimize.Validation.Effects.Context
