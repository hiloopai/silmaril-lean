module

public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Roots.Thms
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Slots
open Silmaril.Machine Silmaril.Compile
open Validation.Roots

namespace Source
open Total

theorem slotGet_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (dest slot : Nat) (word : Lir.Word) (read : frame.slots slot = some word) :
    ∃ newMeaning, OpResult state ((evalOp (.slotGet dest slot)).run state).2
      (frame.set dest word) meaning newMeaning ∧
      TotalNodes ((evalOp (.slotGet dest slot)).run state).2.nodes newMeaning := by
  obtain ⟨newMeaning, actual, totalAfter⟩ := Observation.readSlot_sound state frame meaning rooted total slot word read
  exact ⟨newMeaning,
    ⟨writeReg_rooted _ frame newMeaning actual.rooted dest _ word actual.bounded actual.selected,
      actual.extension, actual.grows, actual.effects⟩, totalAfter⟩

theorem slotSet_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (slot source : Nat) (word : Lir.Word) (read : frame.get source = some word) :
    ∃ newMeaning, OpResult state ((evalOp (.slotSet slot source)).run state).2
      (frame.setSlot slot word) meaning newMeaning ∧
      TotalNodes ((evalOp (.slotSet slot source)).run state).2.nodes newMeaning := by
  obtain ⟨newMeaning, actual, totalAfter⟩ := Total.readReg_sound state frame meaning rooted total source word read
  exact ⟨newMeaning,
    ⟨writeSlot_rooted _ frame newMeaning actual.rooted slot _ word actual.bounded actual.selected,
      actual.extension, actual.grows, actual.effects⟩, totalAfter⟩

theorem evalOp_sound (state : State) (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (operation : Lir.Op Nat) (admitted : AdmittedOp operation)
    (executed : operation.exec frame memory = some (frame', memory')) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((evalOp operation).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((evalOp operation).run state).2.nodes newMeaning := by
  cases operation with
  | const dest word => exact Total.evalOp_sound state frame frame' memory memory' meaning rooted total _ admitted executed
  | move dest source => exact Total.evalOp_sound state frame frame' memory memory' meaning rooted total _ admitted executed
  | unary op dest source => exact Total.evalOp_sound state frame frame' memory memory' meaning rooted total _ admitted executed
  | binary op dest left right => exact Total.evalOp_sound state frame frame' memory memory' meaning rooted total _ admitted executed
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.slots slot = some word ∧
        (frame.set dest word = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact slotGet_sound state frame meaning rooted total dest slot word read
  | slotSet slot source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.setSlot slot word = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact slotSet_sound state frame meaning rooted total slot source word read

theorem evalInstr_op_sound (calls : OpenCalls) (state : State) (frame frame' : Lir.Frame Nat)
    (memory memory' : Lir.Memory) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (operation : Lir.Op Nat) (admitted : AdmittedOp operation)
    (executed : InstructionExec calls (.op operation) frame memory frame' memory') :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((evalInstr (.op operation)).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((evalInstr (.op operation)).run state).2.nodes newMeaning := by
  cases executed with
  | op actual => exact evalOp_sound state frame frame' memory memory' meaning rooted total operation admitted actual

theorem instructions_sound (calls : OpenCalls) (instructions : List Silmaril.Compile.Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (executed : InstructionsExec calls instructions frame memory frame' memory')
    (admitted : Admitted instructions) (state : State) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((instructions.forM evalInstr).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((instructions.forM evalInstr).run state).2.nodes newMeaning := by
  induction executed generalizing state meaning with
  | nil => exact ⟨rfl, meaning, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩, total⟩
  | @cons instruction rest frame memory middle middleMem frame' memory' first tail ih =>
    show memory' = memory ∧ ∃ newMeaning,
      OpResult state (((instruction :: rest).forM evalInstr).run state).2 frame' meaning newMeaning ∧
      TotalNodes (((instruction :: rest).forM evalInstr).run state).2.nodes newMeaning
    have headAdmitted : AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Admitted rest := fun i member => admitted i (by simp [member])
    have step : middleMem = memory ∧ ∃ middleMeaning,
        OpResult state ((evalInstr instruction).run state).2 middle meaning middleMeaning ∧
        TotalNodes ((evalInstr instruction).run state).2.nodes middleMeaning := by
      cases instruction with
      | op op => exact evalInstr_op_sound calls state frame middle memory middleMem meaning rooted total op headAdmitted first
      | fop op dest left right => cases headAdmitted
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect target args results => cases headAdmitted
    obtain ⟨stepMemory, middleMeaning, stepResult, stepTotal⟩ := step
    obtain ⟨tailMemory, newMeaning, tailResult, finalTotal⟩ := ih tailAdmitted
      ((evalInstr instruction).run state).2 middleMeaning stepResult.rooted stepTotal
    rw [Lists.forM_cons_run]
    exact ⟨tailMemory.trans stepMemory, newMeaning, Lists.result_trans stepResult tailResult, finalTotal⟩

/-- Start from the genuine empty validator DAG and actual partial input frame.
Initial Rooted and total-DAG invariants are constructed, not supplied by a
successful checker or an abstract simulation premise. -/
theorem source_instructions_sound (calls : OpenCalls) (instructions : List Silmaril.Compile.Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (executed : InstructionsExec calls instructions frame memory frame' memory')
    (admitted : Admitted instructions) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult {} ((instructions.forM evalInstr).run {}).2 frame' (initialMeaning frame) newMeaning ∧
      TotalNodes ((instructions.forM evalInstr).run {}).2.nodes newMeaning :=
  instructions_sound calls instructions frame frame' memory memory' executed admitted {} (initialMeaning frame)
    (initial_rooted frame) (empty_total _)

open Observation

theorem block_sound (calls : OpenCalls) (block : Silmaril.Compile.Mir.Block)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block frame memory exit frame' memory')
    (admitted : Admitted block.instrs.toList) (observed : List Nat) (values : List Lir.Word)
    (read : observed.mapM frame'.get = some values) (state : State) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning) :
    memory' = memory ∧ ∃ newMeaning,
      BlockResult state ((evalBlock block observed).run state).2 frame'
        ((evalBlock block observed).run state).1.1 ((evalBlock block observed).run state).1.2
        exit values meaning newMeaning := by
  let body := (block.instrs.toList.forM evalInstr).run state
  let term := (evalTerm block.term).run body.2
  let observations := (observed.mapM readReg).run term.2
  obtain ⟨memorySame, bodyMeaning, bodyResult, bodyTotal⟩ := instructions_sound calls block.instrs.toList
    frame frame' memory memory' executed.1 admitted state meaning rooted total
  obtain ⟨termMeaning, termResult⟩ := evalTerm_sound block.term frame' exit executed.2 body.2 bodyMeaning
    bodyResult.rooted bodyTotal
  obtain ⟨newMeaning, observedResult⟩ := readRegs_sound observed values frame' read term.2 termMeaning
    termResult.result.rooted termResult.total
  have common : OpResult state observations.2 frame' meaning newMeaning :=
    Lists.result_trans bodyResult (Lists.result_trans termResult.result observedResult.result)
  have scopedTerm : TermScoped observations.2.nodes.size term.1 :=
    termScoped_mono term.1 observedResult.result.grows termResult.wellScoped
  have decoded : termExit newMeaning term.1 = some exit :=
    (termExit_preserved term.1 observedResult.result.extension termResult.wellScoped).trans termResult.selected
  rw [Lists.evalBlock_run]
  exact ⟨memorySame, newMeaning, ⟨common, observedResult.total, scopedTerm, decoded⟩,
    observedResult.bounded, observedResult.selected⟩

/-- Construct the initial rooted/total interpretation from the actual partial
source frame and the genuine empty symbolic DAG before evaluating the block. -/
theorem source_block_with_reads (calls : OpenCalls) (block : Silmaril.Compile.Mir.Block)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block frame memory exit frame' memory')
    (admitted : Admitted block.instrs.toList) (observed : List Nat) (values : List Lir.Word)
    (read : observed.mapM frame'.get = some values) :
    memory' = memory ∧ ∃ newMeaning,
      BlockResult {} ((evalBlock block observed).run {}).2 frame'
        ((evalBlock block observed).run {}).1.1 ((evalBlock block observed).run {}).1.2
        exit values (Total.initialMeaning frame) newMeaning :=
  block_sound calls block frame frame' memory memory' exit executed admitted observed values read {} (Total.initialMeaning frame)
    (Total.initial_rooted frame) (Total.empty_total _)

open SourceReads

theorem op_written (operation : Lir.Op Nat) (frame frame' : Lir.Frame Nat)
    (memory memory' : Lir.Memory) (admitted : AdmittedOp operation)
    (executed : operation.exec frame memory = some (frame', memory')) :
    Written frame frame' (Validation.defs (.op operation)) := by
  cases operation with
  | const dest word => exact SourceReads.op_written _ frame frame' memory memory' admitted executed
  | move dest source => exact SourceReads.op_written _ frame frame' memory memory' admitted executed
  | unary op dest source => exact SourceReads.op_written _ frame frame' memory memory' admitted executed
  | binary op dest left right => exact SourceReads.op_written _ frame frame' memory memory' admitted executed
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.slots slot = some word ∧
        (frame.set dest word = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    rw [← output.1]
    exact SourceReads.set_written frame dest word
  | slotSet slot source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.setSlot slot word = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    rw [← output.1]
    exact ⟨fun _ prior => prior, fun _ member => nomatch member⟩

theorem instruction_written (calls : OpenCalls) (instruction : Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : AdmittedInstr instruction)
    (executed : InstructionExec calls instruction frame memory frame' memory') :
    Written frame frame' (Validation.defs instruction) := by
  cases instruction with
  | op op =>
    cases executed with
    | op actual => exact op_written op frame frame' memory memory' admitted actual
  | fop op dest left right => cases admitted
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem instructions_written (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory frame' memory') :
    Written frame frame' (instructions.flatMap Validation.defs) := by
  induction executed with
  | nil =>
    exact ⟨fun _ prior => prior, fun _ member => nomatch member⟩
  | @cons instruction rest frame memory middle middleMemory frame' memory' first later ih =>
    have firstWrite := instruction_written calls instruction frame middle memory middleMemory
      (admitted instruction (by simp)) first
    have laterWrite := ih (fun i member => admitted i (by simp [member]))
    exact written_trans firstWrite laterWrite

theorem observed_success (calls : OpenCalls) (block : Mir.Block)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : Admitted block.instrs.toList)
    (executed : InstructionsExec calls block.instrs.toList frame memory frame' memory') :
    ∃ values, (Acceptance.observedRegs block).mapM frame'.get = some values := by
  have written := instructions_written calls block.instrs.toList frame frame' memory memory' admitted executed
  apply defined_mapM
  intro reg member
  apply written.defined reg
  simpa only [Acceptance.observedRegs, List.mem_dedup] using member

theorem source_block_sound (calls : OpenCalls) (block : Mir.Block)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory) (exit : BlockExit)
    (admitted : Admitted block.instrs.toList)
    (executed : BlockExec calls block frame memory exit frame' memory') :
    ∃ values newMeaning, memory' = memory ∧
      (Acceptance.observedRegs block).mapM frame'.get = some values ∧
      Observation.BlockResult {} (Acceptance.sourceRun block).2 frame'
        (Acceptance.sourceRun block).1.1 (Acceptance.sourceRun block).1.2
        exit values (Total.initialMeaning frame) newMeaning := by
  obtain ⟨values, read⟩ := observed_success calls block frame frame' memory memory' admitted executed.1
  obtain ⟨sameMemory, newMeaning, actual⟩ := source_block_with_reads calls block frame frame'
    memory memory' exit executed admitted (Acceptance.observedRegs block) values read
  exact ⟨values, newMeaning, sameMemory, read, actual⟩

end Source
end Silmaril.Compiler.Native.Optimize.Validation.Slots
