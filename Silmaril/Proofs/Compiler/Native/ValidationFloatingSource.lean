module

public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Source.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Floating.Source
open Silmaril.Machine Silmaril.Compile
open Effects Effects.Source

/-- Successful real operand reads construct the same float DAG meaning as
actual FOp.exec. This reuses the existing word function, without numeric facts. -/
theorem fop_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Roots.Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning)
    (op : Lir.FOp) (dest left right : Nat) (x y : Lir.Word)
    (leftRead : frame.get left = some x) (rightRead : frame.get right = some y) :
    ∃ newMeaning, Roots.OpResult state ((evalInstr (.fop op dest left right)).run state).2
      (frame.set dest (op.eval x y)) meaning newMeaning ∧
      Total.TotalNodes ((evalInstr (.fop op dest left right)).run state).2.nodes newMeaning := by
  let first := (readReg left).run state
  let second := (readReg right).run first.2
  obtain ⟨firstMeaning, firstRead, firstTotal⟩ := Total.readReg_sound state frame meaning rooted total left x leftRead
  obtain ⟨secondMeaning, secondRead, secondTotal⟩ :=
    Total.readReg_sound first.2 frame firstMeaning firstRead.rooted firstTotal right y rightRead
  have firstBound : first.1 < second.2.nodes.size := Nat.lt_of_lt_of_le firstRead.bounded secondRead.grows
  have firstSelected : secondMeaning.value first.1 = some x :=
    (secondRead.extension.values first.1 firstRead.bounded).trans firstRead.selected
  have secondSelected : secondMeaning.value second.1 = some y := secondRead.selected
  have selected : (Expr.float op first.1 second.1).eval secondMeaning = some (op.eval x y) := by
    simp only [Expr.eval, firstSelected, secondSelected, Option.bind_some, Option.map_some]
  obtain ⟨newMeaning, actualIntern, totalAfter⟩ := Total.intern_sound second.2 frame secondMeaning secondRead.rooted
    secondTotal (.float op first.1 second.1) ⟨firstBound, secondRead.bounded⟩ (op.eval x y) selected
  have combined := firstRead.trans (secondRead.trans actualIntern)
  exact ⟨newMeaning, ⟨Roots.writeReg_rooted _ frame newMeaning actualIntern.rooted dest _ _ actualIntern.bounded actualIntern.selected,
    combined.extension, combined.grows, combined.effects⟩, totalAfter⟩

theorem safe_fop (op : Lir.FOp) (dest left right : Nat) :
    Safe (evalInstr (.fop op dest left right)) :=
  safe_bind _ _ (safe_readReg left) (fun a => safe_bind _ _ (safe_readReg right) (fun b =>
    safe_bind _ _ (safe_intern (.float op a b) (fun _ => trivial)) (fun output => safe_writeReg dest output)))

/-- A real floating step adds no memory event and preserves every earlier
load result, while actual optional operand reads remain mandatory. -/
theorem fop_invariant {address : String → Nat → Option Lir.Word} (initialFrame frame final : Lir.Frame Nat) (initialMemory memory : Lir.Memory)
    (state : State) (words : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : InvariantWith address initialFrame initialMemory state frame memory words meaning)
    (op : Lir.FOp) (dest left right : Nat)
    (executed : Lir.FOp.exec op dest left right frame = some final) :
    ∃ newMeaning, InvariantWith address initialFrame initialMemory ((evalInstr (.fop op dest left right)).run state).2
      final memory words newMeaning := by
  obtain ⟨x, leftRead, y, rightRead, written⟩ : ∃ x, frame.get left = some x ∧ ∃ y,
      frame.get right = some y ∧ frame.set dest (op.eval x y) = final := by
    simpa only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] using executed
  obtain ⟨newMeaning, actual, afterTotal⟩ := fop_sound state frame meaning invariant.rooted invariant.total
    op dest left right x y leftRead rightRead
  have common : Result state ((evalInstr (.fop op dest left right)).run state).2
      (frame.set dest (op.eval x y)) meaning newMeaning :=
    ⟨actual.rooted, afterTotal, safe_fop op dest left right state invariant.loads,
      prefix_of_extends actual.extension _, actual.grows⟩
  exact ⟨newMeaning, written ▸ invariant_pure invariant common actual.effects actual.extension.load⟩

theorem instructions_invariant (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Floating.Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory final finalMemory)
    (initialFrame : Lir.Frame Nat) (initialMemory : Lir.Memory) (state : State)
    (words : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : Invariant initialFrame initialMemory state frame memory words meaning) :
    ∃ newMeaning newWords, Invariant initialFrame initialMemory ((instructions.forM evalInstr).run state).2
      final finalMemory newWords newMeaning := by
  induction executed generalizing state words meaning with
  | nil => exact ⟨meaning, words, invariant⟩
  | @cons instruction rest frame memory middle middleMemory final finalMemory first later ih =>
    show ∃ newMeaning newWords, Invariant initialFrame initialMemory
      (((instruction :: rest).forM evalInstr).run state).2 final finalMemory newWords newMeaning
    have headAdmitted : Floating.AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Floating.Admitted rest := fun i member => admitted i (by simp [member])
    cases instruction with
    | op operation =>
      show ∃ newMeaning newWords, Invariant initialFrame initialMemory
        (((Mir.Instr.op operation :: rest).forM evalInstr).run state).2 final finalMemory newWords newMeaning
      cases first with
      | op actual =>
        obtain ⟨middleMeaning, middleWords, actualResult⟩ := evalOp_invariant initialFrame frame middle
          initialMemory memory middleMemory state words meaning invariant operation actual
        obtain ⟨newMeaning, newWords, finalInvariant⟩ := ih tailAdmitted ((evalInstr (.op operation)).run state).2
          middleWords middleMeaning actualResult
        rw [Lists.forM_cons_run]
        exact ⟨newMeaning, newWords, finalInvariant⟩
    | fop op dest left right =>
      show ∃ newMeaning newWords, Invariant initialFrame initialMemory
        (((Mir.Instr.fop op dest left right :: rest).forM evalInstr).run state).2 final finalMemory newWords newMeaning
      cases first with
      | fop actual =>
        obtain ⟨middleMeaning, actualResult⟩ := fop_invariant initialFrame frame middle initialMemory memory state words meaning
          invariant op dest left right actual
        obtain ⟨newMeaning, newWords, finalInvariant⟩ := ih tailAdmitted ((evalInstr (.fop op dest left right)).run state).2
          words middleMeaning actualResult
        rw [Lists.forM_cons_run]
        exact ⟨newMeaning, newWords, finalInvariant⟩
    | addr dest symbol offset => cases headAdmitted
    | call symbol args results => cases headAdmitted
    | callIndirect target args results => cases headAdmitted

/-- Start from the genuine empty checker state and actual partial input frame.
All real source load results, event operands and complete retained DAG values
are constructed from actual successful source execution. -/
theorem source_instructions_invariant (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Floating.Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory final finalMemory) :
    ∃ meaning words, Invariant frame memory ((instructions.forM evalInstr).run {}).2 final finalMemory words meaning :=
  instructions_invariant calls instructions frame final memory finalMemory admitted executed frame memory {} []
    (Total.initialMeaning frame) (initial_invariant frame memory)


theorem instruction_written (calls : OpenCalls) (instruction : Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Floating.AdmittedInstr instruction)
    (executed : InstructionExec calls instruction frame memory final finalMemory) :
    SourceReads.Written frame final (Validation.defs instruction) := by
  cases instruction with
  | op operation =>
    cases executed with
    | op actual => exact op_written operation frame final memory finalMemory actual
  | fop op dest left right =>
    cases executed with
    | fop actual =>
      obtain ⟨x, _, y, _, written⟩ : ∃ x, frame.get left = some x ∧ ∃ y,
          frame.get right = some y ∧ frame.set dest (op.eval x y) = final := by
        simpa only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] using actual
      rw [← written]
      exact SourceReads.set_written frame dest (op.eval x y)
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem instructions_written (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Floating.Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory final finalMemory) :
    SourceReads.Written frame final (instructions.flatMap Validation.defs) := by
  induction executed with
  | nil => exact ⟨fun _ prior => prior, fun _ member => nomatch member⟩
  | @cons instruction rest frame memory middle middleMemory final finalMemory first later ih =>
    have firstWrite := instruction_written calls instruction frame middle memory middleMemory
      (admitted instruction (by simp)) first
    have laterWrite := ih (fun i member => admitted i (by simp [member]))
    exact SourceReads.written_trans firstWrite laterWrite

theorem observed_success (calls : OpenCalls) (block : Mir.Block)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Floating.Admitted block.instrs.toList)
    (executed : InstructionsExec calls block.instrs.toList frame memory final finalMemory) :
    ∃ values, (Acceptance.observedRegs block).mapM final.get = some values := by
  have written := instructions_written calls block.instrs.toList frame final memory finalMemory admitted executed
  apply SourceReads.defined_mapM
  intro reg member
  apply written.defined reg
  simpa only [Acceptance.observedRegs, List.mem_dedup] using member

/-- Actual source block execution constructs its complete effectful symbolic
meaning and real memory trace; term/observed evaluation adds no effects. -/
theorem block_with_reads (calls : OpenCalls) (block : Mir.Block) (frame final : Lir.Frame Nat)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (admitted : Floating.Admitted block.instrs.toList)
    (executed : BlockExec calls block frame memory exit final finalMemory)
    (observed : List Nat) (values : List Lir.Word) (read : observed.mapM final.get = some values) :
    ∃ meaning words, BlockResult frame memory ((evalBlock block observed).run {}).2 final finalMemory words
      ((evalBlock block observed).run {}).1.1 ((evalBlock block observed).run {}).1.2 exit values meaning := by
  obtain ⟨bodyMeaning, bodyWords, bodyInvariant⟩ := source_instructions_invariant calls block.instrs.toList frame final
    memory finalMemory admitted executed.1
  obtain ⟨meaning, result⟩ := Effects.Source.finish_block (fun _ _ => none) block frame final memory finalMemory exit
    bodyMeaning bodyWords bodyInvariant executed.2 observed values read
  exact ⟨meaning, bodyWords, result⟩

/-- No observed-read or abstract semantic premise: original register outputs
are defined by actual successful source writes, and the complete actual checker
source run obtains its real load map and exact ordered effect memory trace. -/
theorem source_block (calls : OpenCalls) (block : Mir.Block) (frame final : Lir.Frame Nat)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (admitted : Floating.Admitted block.instrs.toList)
    (executed : BlockExec calls block frame memory exit final finalMemory) :
    ∃ meaning words values,
      (Acceptance.observedRegs block).mapM final.get = some values ∧
      BlockResult frame memory (Acceptance.sourceRun block).2 final finalMemory words
        (Acceptance.sourceRun block).1.1 (Acceptance.sourceRun block).1.2 exit values meaning := by
  obtain ⟨values, read⟩ := observed_success calls block frame final memory finalMemory admitted executed.1
  obtain ⟨meaning, words, result⟩ := block_with_reads calls block frame final memory finalMemory exit admitted executed
    (Acceptance.observedRegs block) values read
  exact ⟨meaning, words, values, read, result⟩

end Silmaril.Compiler.Native.Optimize.Validation.Floating.Source
