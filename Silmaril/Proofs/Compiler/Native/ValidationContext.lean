module

public import Silmaril.Compiler.Native.Optimize.Validation.Context.Defs
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Context
open Silmaril.Machine Silmaril.Compile
open PureSoundness

theorem agrees_refl (base : Nat) (frame : Lir.Frame Nat) : FrameAgrees base frame frame :=
  ⟨rfl, fun _ _ => rfl⟩

theorem agrees_trans {base : Nat} {source middle target : Lir.Frame Nat}
    (earlier : FrameAgrees base source middle) (later : FrameAgrees base middle target) :
    FrameAgrees base source target :=
  ⟨later.slots.trans earlier.slots, fun reg below => (later.registers reg below).trans (earlier.registers reg below)⟩

theorem agrees_set {base : Nat} {source target : Lir.Frame Nat}
    (agrees : FrameAgrees base source target) (dest : Nat) (word : Lir.Word) :
    FrameAgrees base (source.set dest word) (target.set dest word) := by
  refine ⟨agrees.slots, ?_⟩
  intro reg below
  by_cases same : reg = dest
  · simp [same]
  · simpa only [Lir.Frame.get_set, ite_eq_right same] using agrees.registers reg below

/-- Transport the actual successful source primitive across partial incoming
frames agreeing only on the source register range. -/
theorem op_transport (base : Nat) (op : Lir.Op Nat) (admitted : Roots.Admitted op)
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
    exact ⟨target.set dest word, rfl, agrees_set agrees dest word⟩
  | move dest reg =>
    have output : ∃ word, source.get reg = some word ∧ source.set dest word = sourceFinal ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨word, read, final, sameMemory⟩ := output
    have targetRead : target.get reg = some word := (agrees.registers reg (bounds reg (by simp [Mir.DeadCode.opUses]))).trans read
    rw [← final, ← sameMemory]
    exact ⟨target.set dest word, by simp only [Lir.Op.exec, targetRead, Option.map_some], agrees_set agrees dest word⟩
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
      agrees_set agrees dest (operation.eval word)⟩
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
      simp only [Lir.Op.exec, targetLeft, targetRight, computed, Option.bind_some, Option.map_some], agrees_set agrees dest word⟩
  | load width ext dest reg offset => cases admitted
  | store width reg offset source => cases admitted
  | slotGet dest slot => cases admitted
  | slotSet slot reg => cases admitted

theorem instructions_transport (calls : OpenCalls) (base : Nat) (instructions : List Mir.Instr)
    (admitted : Lists.Admitted instructions)
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
    have headAdmitted : Lists.AdmittedInstr instruction := admitted instruction (by simp)
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

theorem readAll_agrees (base : Nat) (source target : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (locations : List (Lir.Loc Nat)) (bounds : ∀ reg, Lir.Loc.reg reg ∈ locations → reg < base) :
    target.readAll locations = source.readAll locations := by
  induction locations with
  | nil => rfl
  | cons location rest ih =>
    have first : target.read location = source.read location := by
      cases location with
      | reg reg => exact agrees.registers reg (bounds reg (by simp))
      | slot slot => exact congrFun agrees.slots slot
    have tail : target.readAll rest = source.readAll rest := ih (fun r h => bounds r (by simp [h]))
    simp only [Lir.Frame.readAll, List.mapM_cons] at tail ⊢
    rw [first, tail]

theorem term_transport (base : Nat) (term : Lir.Term Nat)
    (bounds : ∀ reg ∈ Mir.DeadCode.termUses term, reg < base)
    (source target : Lir.Frame Nat) (agrees : FrameAgrees base source target) (exit : BlockExit)
    (executed : TermExec term source exit) : TermExec term target exit := by
  cases executed with
  | jump => exact .jump
  | zero read =>
    exact .zero ((agrees.registers _ (bounds _ (by simp [Mir.DeadCode.termUses]))).trans read)
  | nonzero read nonzero =>
    exact .nonzero ((agrees.registers _ (bounds _ (by simp [Mir.DeadCode.termUses]))).trans read) nonzero
  | @ret locations source words read =>
    apply TermExec.ret
    rw [readAll_agrees base source target agrees locations]
    · exact read
    · intro reg member
      exact bounds reg (List.mem_filterMap.mpr ⟨.reg reg, member, rfl⟩)
  | trap => exact .trap

/-- Source execution transports between different incoming partial frames. -/
theorem block_transport (calls : OpenCalls) (base : Nat) (block : Mir.Block)
    (admitted : Lists.Admitted block.instrs.toList) (bounds : ReadsBelow base block)
    (source target sourceFinal : Lir.Frame Nat) (agrees : FrameAgrees base source target)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block source memory exit sourceFinal finalMemory) :
    ∃ targetFinal, BlockExec calls block target memory exit targetFinal finalMemory ∧
      FrameAgrees base sourceFinal targetFinal := by
  obtain ⟨targetFinal, bodyRun, finalAgree⟩ := instructions_transport calls base block.instrs.toList
    admitted bounds.1 source target sourceFinal agrees memory finalMemory executed.1
  exact ⟨targetFinal, ⟨bodyRun, term_transport base block.term bounds.2 sourceFinal targetFinal finalAgree exit executed.2⟩, finalAgree⟩

/-- A checked pure block refines source execution even when incoming frames
already differ in the fresh range, as they do at later CFG block boundaries. -/
theorem checked_contextual (calls : OpenCalls) (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Lists.Admitted source.instrs.toList)
    (candidateAdmitted : Lists.Admitted candidate.instrs.toList) (bounds : ReadsBelow base source)
    (accepted : check base source candidate = true)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees base sourceInput candidateInput) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees base sourceFinal candidateFinal := by
  obtain ⟨transportedFinal, transportedRun, transportedAgree⟩ := block_transport calls base source sourceAdmitted bounds
    sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ :=
    check_sound base source candidate sourceAdmitted candidateAdmitted accepted calls candidateInput transportedFinal
      memory finalMemory exit transportedRun
  exact ⟨candidateFinal, candidateRun, agrees_trans transportedAgree candidateAgree⟩


private theorem foldl_max_initial (registers : List Nat) (initial : Nat) :
    initial ≤ registers.foldl Nat.max initial := by
  induction registers generalizing initial with
  | nil => exact Nat.le_refl _
  | cons register rest ih => exact (Nat.le_max_left initial register).trans (ih (max initial register))

private theorem member_le_foldl_max {registers : List Nat} {reg : Nat} (member : reg ∈ registers)
    (initial : Nat) : reg ≤ registers.foldl Nat.max initial := by
  induction registers generalizing initial with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with equal | later
    · subst reg
      exact (Nat.le_max_right initial head).trans (foldl_max_initial rest (max initial head))
    · exact ih later (max initial head)

/-- Every actual member block reads only the original function range, including
its terminator. No candidate temporary range enters this source inventory. -/
theorem freshBase_reads {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) : ReadsBelow (freshBase function) block := by
  constructor
  · intro instruction inBlock reg used
    have inventoried : reg ∈ function.params ++ function.blocks.toList.flatMap (fun block =>
        Mir.DeadCode.termUses block.term ++ block.instrs.toList.flatMap (fun instruction =>
          Optimize.uses instruction ++ Optimize.defs instruction)) := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨block, member, List.mem_append_right _ ?_⟩
      exact List.mem_flatMap.mpr ⟨instruction, inBlock, List.mem_append_left _ used⟩
    exact Nat.lt_succ_of_le (member_le_foldl_max inventoried 0)
  · intro reg used
    have inventoried : reg ∈ function.params ++ function.blocks.toList.flatMap (fun block =>
        Mir.DeadCode.termUses block.term ++ block.instrs.toList.flatMap (fun instruction =>
          Optimize.uses instruction ++ Optimize.defs instruction)) := by
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨block, member, List.mem_append_left _ used⟩
    exact Nat.lt_succ_of_le (member_le_foldl_max inventoried 0)

/-- Actual function membership and actual freshBase discharge the source-read
bounds needed to compose checked blocks across different incoming frames. -/
theorem function_checked_contextual {function : Mir.Func} {source candidate : Mir.Block}
    (member : source ∈ function.blocks.toList)
    (sourceAdmitted : Lists.Admitted source.instrs.toList)
    (candidateAdmitted : Lists.Admitted candidate.instrs.toList)
    (accepted : check (freshBase function) source candidate = true)
    (calls : OpenCalls) (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal :=
  checked_contextual calls (freshBase function) source candidate sourceAdmitted candidateAdmitted
    (freshBase_reads member) accepted sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed

end Silmaril.Compiler.Native.Optimize.Validation.Context
