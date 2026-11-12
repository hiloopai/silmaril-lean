module

public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Source.Thms
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Slots
open Silmaril.Machine Silmaril.Compile
open Validation.Roots

namespace Candidate
open Total Validation.Candidate

theorem growing_writeSlot (slot index : Nat) : Growing (writeSlot slot index) := fun state => .refl state.nodes

theorem growing_evalOp (operation : Lir.Op Nat) (admitted : AdmittedOp operation) : Growing (evalOp operation) := by
  cases operation with
  | const dest word => exact Validation.Candidate.growing_evalOp _ admitted
  | move dest source => exact Validation.Candidate.growing_evalOp _ admitted
  | unary op dest source => exact Validation.Candidate.growing_evalOp _ admitted
  | binary op dest left right => exact Validation.Candidate.growing_evalOp _ admitted
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot => exact growing_bind _ _ (growing_readSlot slot) (fun index => growing_writeReg dest index)
  | slotSet slot source => exact growing_bind _ _ (growing_readReg source) (fun index => growing_writeSlot slot index)

theorem growing_evalInstr (instruction : Silmaril.Compile.Mir.Instr)
    (admitted : AdmittedInstr instruction) : Growing (evalInstr instruction) := by
  cases instruction with
  | op op => exact growing_evalOp op admitted
  | fop op dest left right => cases admitted
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem growing_forM (instructions : List Silmaril.Compile.Mir.Instr)
    (admitted : Admitted instructions) : Growing (instructions.forM evalInstr) := by
  induction instructions with
  | nil => exact growing_pure ()
  | cons instruction rest ih =>
    intro state
    rw [Lists.forM_cons_run]
    exact (growing_evalInstr instruction (admitted instruction (by simp)) state).trans
      (ih (fun i h => admitted i (by simp [h])) ((evalInstr instruction).run state).2)

theorem growing_evalBlock (block : Silmaril.Compile.Mir.Block) (observed : List Nat)
    (admitted : Admitted block.instrs.toList) : Growing (evalBlock block observed) := by
  intro state
  rw [Lists.evalBlock_run]
  exact (growing_forM block.instrs.toList admitted state).trans
    ((growing_evalTerm block.term _).trans (growing_mapM readReg observed growing_readReg _))


theorem evalOp_exists (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (sourceSize : Nat)
    (old : sourceSize ≤ state.nodes.size) (operation : Lir.Op Nat) (admitted : AdmittedOp operation)
    (guarded : Guarded sourceSize ((evalOp operation).run state).2.nodes) :
    ∃ frame', operation.exec frame memory = some (frame', memory) := by
  cases operation with
  | const dest word => exact Validation.Candidate.evalOp_exists state frame memory meaning rooted total sourceSize old _ admitted guarded
  | move dest source => exact Validation.Candidate.evalOp_exists state frame memory meaning rooted total sourceSize old _ admitted guarded
  | unary op dest source => exact Validation.Candidate.evalOp_exists state frame memory meaning rooted total sourceSize old _ admitted guarded
  | binary op dest left right => exact Validation.Candidate.evalOp_exists state frame memory meaning rooted total sourceSize old _ admitted guarded
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot =>
    obtain ⟨word, read⟩ := readSlot_defined state frame meaning rooted total sourceSize old slot guarded
    exact ⟨frame.set dest word, by simp only [Lir.Op.exec, read, Option.map_some]⟩
  | slotSet slot source =>
    obtain ⟨word, read⟩ := readReg_defined state frame meaning rooted total sourceSize old source guarded
    exact ⟨frame.setSlot slot word, by simp only [Lir.Op.exec, read, Option.map_some]⟩

theorem evalOp_success (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (sourceSize : Nat)
    (old : sourceSize ≤ state.nodes.size) (op : Lir.Op Nat) (admitted : AdmittedOp op)
    (guarded : Guarded sourceSize ((evalOp op).run state).2.nodes) :
    ∃ frame' newMeaning, op.exec frame memory = some (frame', memory) ∧
      OpResult state ((evalOp op).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((evalOp op).run state).2.nodes newMeaning := by
  obtain ⟨frame', executed⟩ := evalOp_exists state frame memory meaning rooted total sourceSize old op admitted guarded
  obtain ⟨sameMemory, newMeaning, actual, afterTotal⟩ :=
    Source.evalOp_sound state frame frame' memory memory meaning rooted total op admitted executed
  exact ⟨frame', newMeaning, executed, actual, afterTotal⟩

/-- The real candidate list executes from the actual partial frame. The only
fragment restriction is the expanded integer/slot admitted instruction predicate. -/
theorem instructions_success (calls : OpenCalls) (instructions : List Silmaril.Compile.Mir.Instr)
    (admitted : Admitted instructions) (state : State) (frame : Lir.Frame Nat)
    (memory : Lir.Memory) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size)
    (guarded : Guarded sourceSize ((instructions.forM evalInstr).run state).2.nodes) :
    ∃ frame' newMeaning, InstructionsExec calls instructions frame memory frame' memory ∧
      OpResult state ((instructions.forM evalInstr).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((instructions.forM evalInstr).run state).2.nodes newMeaning := by
  induction instructions generalizing state frame meaning with
  | nil => exact ⟨frame, meaning, .nil, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩, total⟩
  | cons instruction rest ih =>
    show ∃ frame' newMeaning, InstructionsExec calls (instruction :: rest) frame memory frame' memory ∧
      OpResult state (((instruction :: rest).forM evalInstr).run state).2 frame' meaning newMeaning ∧
      TotalNodes (((instruction :: rest).forM evalInstr).run state).2.nodes newMeaning
    have headAdmitted : AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Admitted rest := fun i member => admitted i (by simp [member])
    have headGuard : Guarded sourceSize ((evalInstr instruction).run state).2.nodes := by
      have finalGuard : Guarded sourceSize ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.nodes := by
        simpa only [Lists.forM_cons_run] using guarded
      exact finalGuard.prefix (growing_forM rest tailAdmitted ((evalInstr instruction).run state).2)
    have step : ∃ middle middleMeaning,
        InstructionExec calls instruction frame memory middle memory ∧
        OpResult state ((evalInstr instruction).run state).2 middle meaning middleMeaning ∧
        TotalNodes ((evalInstr instruction).run state).2.nodes middleMeaning := by
      cases instruction with
      | op op =>
        obtain ⟨middle, middleMeaning, executed, actual, afterTotal⟩ :=
          evalOp_success state frame memory meaning rooted total sourceSize old op headAdmitted headGuard
        exact ⟨middle, middleMeaning, .op executed, actual, afterTotal⟩
      | fop op dest left right => cases headAdmitted
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect target args results => cases headAdmitted
    obtain ⟨middle, middleMeaning, headExecuted, headResult, headTotal⟩ := step
    have tailGuard : Guarded sourceSize ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.nodes := by
      simpa only [Lists.forM_cons_run] using guarded
    obtain ⟨frame', newMeaning, tailExecuted, tailResult, tailTotal⟩ :=
      ih tailAdmitted ((evalInstr instruction).run state).2 middle middleMeaning headResult.rooted headTotal
        (old.trans headResult.grows) tailGuard
    rw [Lists.forM_cons_run]
    exact ⟨frame', newMeaning, .cons headExecuted tailExecuted, Lists.result_trans headResult tailResult, tailTotal⟩


theorem block_success (calls : OpenCalls) (block : Silmaril.Compile.Mir.Block)
    (admitted : Admitted block.instrs.toList) (observed : List Nat)
    (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size)
    (guarded : Guarded sourceSize ((evalBlock block observed).run state).2.nodes) :
    ∃ exit frame' values newMeaning,
      BlockExec calls block frame memory exit frame' memory ∧
      observed.mapM frame'.get = some values ∧
      Observation.BlockResult state ((evalBlock block observed).run state).2 frame'
        ((evalBlock block observed).run state).1.1 ((evalBlock block observed).run state).1.2
        exit values meaning newMeaning := by
  let body := (block.instrs.toList.forM evalInstr).run state
  let term := (evalTerm block.term).run body.2
  let observations := (observed.mapM readReg).run term.2
  have afterTerm : Guarded sourceSize term.2.nodes := by
    rw [Lists.evalBlock_run] at guarded
    exact guarded.prefix (growing_mapM readReg observed growing_readReg term.2)
  have afterBody : Guarded sourceSize body.2.nodes :=
    afterTerm.prefix (growing_evalTerm block.term body.2)
  obtain ⟨frame', bodyMeaning, bodyExecuted, bodyResult, bodyTotal⟩ :=
    instructions_success calls block.instrs.toList admitted state frame memory meaning rooted total sourceSize old afterBody
  obtain ⟨exit, termMeaning, termExecuted, termResult⟩ :=
    evalTerm_success block.term frame' body.2 bodyMeaning bodyResult.rooted bodyTotal sourceSize
      (old.trans bodyResult.grows) afterTerm
  have afterObservations : Guarded sourceSize observations.2.nodes := by
    simpa only [Lists.evalBlock_run] using guarded
  obtain ⟨values, newMeaning, read, observedResult⟩ :=
    readRegs_success observed frame' sourceSize term.2 termMeaning termResult.result.rooted termResult.total
      ((old.trans bodyResult.grows).trans termResult.result.grows) afterObservations
  have common : OpResult state observations.2 frame' meaning newMeaning :=
    Lists.result_trans bodyResult (Lists.result_trans termResult.result observedResult.result)
  have scopedTerm : Observation.TermScoped observations.2.nodes.size term.1 :=
    Observation.termScoped_mono term.1 observedResult.result.grows termResult.wellScoped
  have decoded : Observation.termExit newMeaning term.1 = some exit :=
    (Observation.termExit_preserved term.1 observedResult.result.extension termResult.wellScoped).trans termResult.selected
  rw [Lists.evalBlock_run]
  exact ⟨exit, frame', values, newMeaning, ⟨bodyExecuted, termExecuted⟩, read,
    ⟨common, observedResult.total, scopedTerm, decoded⟩, observedResult.bounded, observedResult.selected⟩

theorem seeded_block_success (calls : OpenCalls) (block : Silmaril.Compile.Mir.Block)
    (admitted : Admitted block.instrs.toList) (observed : List Nat)
    (frame sourceFrame : Lir.Frame Nat) (memory : Lir.Memory) (sourceState : State) (meaning : Interpretation)
    (source : OpResult {} sourceState sourceFrame (Total.initialMeaning frame) meaning)
    (total : TotalNodes sourceState.nodes meaning)
    (guarded : ((evalBlock block observed).run { nodes := sourceState.nodes }).2.nodes.any
      Expr.isPartialLeaf sourceState.nodes.size = false) :
    ∃ exit frame' values newMeaning,
      BlockExec calls block frame memory exit frame' memory ∧
      observed.mapM frame'.get = some values ∧
      Observation.BlockResult { nodes := sourceState.nodes }
        ((evalBlock block observed).run { nodes := sourceState.nodes }).2 frame'
        ((evalBlock block observed).run { nodes := sourceState.nodes }).1.1
        ((evalBlock block observed).run { nodes := sourceState.nodes }).1.2
        exit values meaning newMeaning :=
  block_success calls block admitted observed { nodes := sourceState.nodes } frame memory meaning
    (seed_rooted frame sourceFrame sourceState meaning source) total sourceState.nodes.size (Nat.le_refl _)
    (guarded_of_any _ _ guarded)

end Candidate
end Silmaril.Compiler.Native.Optimize.Validation.Slots
