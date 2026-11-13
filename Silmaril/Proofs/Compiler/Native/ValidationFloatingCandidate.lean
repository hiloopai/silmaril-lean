module

public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Candidate.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Floating.Candidate
open Silmaril.Machine Silmaril.Compile
open Roots Effects Effects.Candidate

theorem growing_evalInstr (instruction : Mir.Instr) (admitted : Floating.AdmittedInstr instruction) :
    EffectGrowing (evalInstr instruction) := by
  cases instruction with
  | op operation => exact Effects.Candidate.growing_evalOp operation
  | fop op dest left right =>
    exact growing_bind _ _ (growing_readReg left) (fun a => growing_bind _ _ (growing_readReg right) (fun b =>
      growing_bind _ _ (growing_intern (.float op a b)) (fun output => growing_writeReg dest output)))
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem growing_forM (instructions : List Mir.Instr) (admitted : Floating.Admitted instructions) :
    EffectGrowing (instructions.forM evalInstr) := by
  induction instructions with
  | nil => exact growing_pure ()
  | cons instruction rest ih =>
    intro state
    rw [Lists.forM_cons_run]
    exact (growing_evalInstr instruction (admitted instruction (by simp)) state).trans
      (ih (fun i member => admitted i (by simp [member])) ((evalInstr instruction).run state).2)

theorem growing_evalBlock (block : Mir.Block) (observed : List Nat)
    (admitted : Floating.Admitted block.instrs.toList) : EffectGrowing (evalBlock block observed) := by
  intro state
  rw [Lists.evalBlock_run]
  exact (growing_forM block.instrs.toList admitted state).trans
    ((growing_evalTerm block.term _).trans (growing_mapM readReg observed growing_readReg _))

namespace Nodes
open Validation.Candidate

theorem evalInstr (instruction : Mir.Instr) (admitted : Floating.AdmittedInstr instruction) :
    Growing (Validation.evalInstr instruction) := by
  cases instruction with
  | op operation => exact Effects.Candidate.Nodes.evalOp operation
  | fop op dest left right =>
    exact Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_readReg left) (fun a =>
      Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_readReg right) (fun b =>
        Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_intern (.float op a b))
          (fun output => Validation.Candidate.growing_writeReg dest output)))
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem forM (instructions : List Mir.Instr) (admitted : Floating.Admitted instructions) :
    Growing (instructions.forM Validation.evalInstr) := by
  induction instructions with
  | nil => exact Validation.Candidate.growing_pure ()
  | cons instruction rest ih =>
    intro state
    rw [Lists.forM_cons_run]
    exact (evalInstr instruction (admitted instruction (by simp)) state).trans
      (ih (fun i member => admitted i (by simp [member])) ((Validation.evalInstr instruction).run state).2)

theorem evalBlock (block : Mir.Block) (observed : List Nat)
    (admitted : Floating.Admitted block.instrs.toList) : Growing (Validation.evalBlock block observed) := by
  intro state
  rw [Lists.evalBlock_run]
  exact (forM block.instrs.toList admitted state).trans
    ((Validation.Candidate.growing_evalTerm block.term _).trans (Validation.Candidate.growing_mapM readReg observed Validation.Candidate.growing_readReg _))

end Nodes

/-- Guarded candidate reads are defined even when the actual input frame is
partial. Both operands are required, including for unary conversion syntax. -/
theorem fop_success (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (op : Lir.FOp) (dest left right : Nat)
    (guarded : Validation.Candidate.Guarded source.nodes.size
      ((evalInstr (.fop op dest left right)).run state).2.nodes) :
    ∃ frame' newMeaning, Lir.FOp.exec op dest left right frame = some frame' ∧
      Result state ((evalInstr (.fop op dest left right)).run state).2 frame' meaning newMeaning ∧
      Trace source ((evalInstr (.fop op dest left right)).run state).2 newMeaning
        initialMemory memory finalMemory sourceWords words := by
  let first := (readReg left).run state
  let second := (readReg right).run first.2
  have secondPrefix : Validation.Candidate.Prefix second.2.nodes
      ((evalInstr (.fop op dest left right)).run state).2.nodes :=
    Validation.Candidate.growing_intern (.float op first.1 second.1) second.2
  have firstPrefix : Validation.Candidate.Prefix first.2.nodes
      ((evalInstr (.fop op dest left right)).run state).2.nodes :=
    (Validation.Candidate.growing_readReg right first.2).trans secondPrefix
  obtain ⟨x, firstMeaning, leftRead, firstRead, firstTotal⟩ := Validation.Candidate.readReg_success
    state frame meaning rooted total source.nodes.size old left (guarded.prefix firstPrefix)
  obtain ⟨y, rightRead⟩ := Validation.Candidate.readReg_defined first.2 frame firstMeaning firstRead.rooted
    firstTotal source.nodes.size (old.trans firstRead.grows) right (guarded.prefix secondPrefix)
  obtain ⟨newMeaning, actual, afterTotal⟩ := Source.fop_sound state frame meaning rooted total
    op dest left right x y leftRead rightRead
  exact ⟨frame.set dest (op.eval x y), newMeaning,
    by simp only [Lir.FOp.exec, leftRead, rightRead, Option.bind_some, Option.map_some],
    ⟨actual.rooted, afterTotal, actual.extension, actual.grows⟩,
    (trace.extend (extends_restrict actual.extension old)).restate actual.effects⟩

theorem instructions_success (calls : OpenCalls) (instructions : List Mir.Instr)
    (admitted : Floating.Admitted instructions) (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((instructions.forM evalInstr).run state).2.nodes)
    (afterPrefix : EffectPrefix ((instructions.forM evalInstr).run state).2.effects source.effects) :
    ∃ frame' memory' newMeaning nextWords,
      InstructionsExec calls instructions frame memory frame' memory' ∧
      Result state ((instructions.forM evalInstr).run state).2 frame' meaning newMeaning ∧
      Trace source ((instructions.forM evalInstr).run state).2 newMeaning
        initialMemory memory' finalMemory sourceWords nextWords := by
  induction instructions generalizing state frame meaning memory words with
  | nil => exact ⟨frame, memory, meaning, words, .nil, ⟨rooted, total, .refl _ _, Nat.le_refl _⟩, trace⟩
  | cons instruction rest ih =>
    show ∃ frame' memory' newMeaning nextWords,
      InstructionsExec calls (instruction :: rest) frame memory frame' memory' ∧
      Result state (((instruction :: rest).forM evalInstr).run state).2 frame' meaning newMeaning ∧
      Trace source (((instruction :: rest).forM evalInstr).run state).2 newMeaning
        initialMemory memory' finalMemory sourceWords nextWords
    have headAdmitted : Floating.AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Floating.Admitted rest := fun i member => admitted i (by simp [member])
    have tailGuard : Validation.Candidate.Guarded source.nodes.size
        ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.nodes := by
      simpa only [Lists.forM_cons_run] using guarded
    have headGuard : Validation.Candidate.Guarded source.nodes.size ((evalInstr instruction).run state).2.nodes :=
      tailGuard.prefix (Nodes.forM rest tailAdmitted ((evalInstr instruction).run state).2)
    have tailPrefix : EffectPrefix ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.effects source.effects := by
      simpa only [Lists.forM_cons_run] using afterPrefix
    have headPrefix : EffectPrefix ((evalInstr instruction).run state).2.effects source.effects :=
      (growing_forM rest tailAdmitted ((evalInstr instruction).run state).2).trans tailPrefix
    have step : ∃ middle middleMemory middleMeaning middleWords,
        InstructionExec calls instruction frame memory middle middleMemory ∧
        Result state ((evalInstr instruction).run state).2 middle meaning middleMeaning ∧
        Trace source ((evalInstr instruction).run state).2 middleMeaning
          initialMemory middleMemory finalMemory sourceWords middleWords := by
      cases instruction with
      | op operation =>
        obtain ⟨middle, middleMemory, middleMeaning, middleWords, executed, actual, afterTrace⟩ :=
          evalOp_success source state frame meaning rooted total old initialMemory memory finalMemory sourceWords words
            trace operation headGuard headPrefix
        exact ⟨middle, middleMemory, middleMeaning, middleWords, .op executed, actual, afterTrace⟩
      | fop op dest left right =>
        obtain ⟨middle, middleMeaning, executed, actual, afterTrace⟩ :=
          fop_success source state frame meaning rooted total old initialMemory memory finalMemory sourceWords words
            trace op dest left right headGuard
        exact ⟨middle, memory, middleMeaning, words, .fop executed, actual, afterTrace⟩
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect target args results => cases headAdmitted
    obtain ⟨middle, middleMemory, middleMeaning, middleWords, headExecuted, headResult, headTrace⟩ := step
    obtain ⟨frame', memory', newMeaning, nextWords, tailExecuted, tailResult, tailTrace⟩ :=
      ih tailAdmitted ((evalInstr instruction).run state).2 middle middleMeaning headResult.rooted headResult.total
        (old.trans headResult.grows) middleMemory middleWords headTrace tailGuard tailPrefix
    rw [Lists.forM_cons_run]
    exact ⟨frame', memory', newMeaning, nextWords, .cons headExecuted tailExecuted, headResult.trans tailResult, tailTrace⟩

/-- Complete actual candidate execution, including its terminator and observed
register reads, with real final frame, memory and consumed effect trace. -/
theorem block_success (calls : OpenCalls) (block : Mir.Block)
    (admitted : Floating.Admitted block.instrs.toList) (observed : List Nat)
    (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((evalBlock block observed).run state).2.nodes)
    (afterPrefix : EffectPrefix ((evalBlock block observed).run state).2.effects source.effects) :
    ∃ exit frame' memory' values newMeaning nextWords,
      BlockExec calls block frame memory exit frame' memory' ∧
      observed.mapM frame'.get = some values ∧
      BlockResult state ((evalBlock block observed).run state).2 frame'
        ((evalBlock block observed).run state).1.1 ((evalBlock block observed).run state).1.2
        exit values meaning newMeaning ∧
      Trace source ((evalBlock block observed).run state).2 newMeaning
        initialMemory memory' finalMemory sourceWords nextWords := by
  let body := (block.instrs.toList.forM evalInstr).run state
  let term := (evalTerm block.term).run body.2
  let observations := (observed.mapM readReg).run term.2
  have observationsGuard : Validation.Candidate.Guarded source.nodes.size observations.2.nodes := by
    simpa only [Lists.evalBlock_run] using guarded
  have termGuard : Validation.Candidate.Guarded source.nodes.size term.2.nodes :=
    observationsGuard.prefix (Validation.Candidate.growing_mapM readReg observed Validation.Candidate.growing_readReg term.2)
  have bodyGuard : Validation.Candidate.Guarded source.nodes.size body.2.nodes :=
    termGuard.prefix (Validation.Candidate.growing_evalTerm block.term body.2)
  have bodyPrefix : EffectPrefix body.2.effects source.effects := by
    have observationsPrefix : EffectPrefix observations.2.effects source.effects := by
      simpa only [Lists.evalBlock_run] using afterPrefix
    exact (growing_evalTerm block.term body.2).trans
      ((growing_mapM readReg observed growing_readReg term.2).trans observationsPrefix)
  obtain ⟨frame', memory', bodyMeaning, bodyWords, bodyExecuted, bodyResult, bodyTrace⟩ :=
    instructions_success calls block.instrs.toList admitted source state frame meaning rooted total old
      initialMemory memory finalMemory sourceWords words trace bodyGuard bodyPrefix
  obtain ⟨exit, values, newMeaning, executed, read, actual, trace⟩ :=
    Effects.Candidate.finish_block calls block observed source state frame frame' meaning bodyMeaning old
      initialMemory memory memory' finalMemory sourceWords bodyWords guarded bodyExecuted bodyResult bodyTrace
  exact ⟨exit, frame', memory', values, newMeaning, bodyWords, executed, read, actual, trace⟩

theorem seeded_block_success (calls : OpenCalls) (block : Mir.Block)
    (admitted : Floating.Admitted block.instrs.toList) (observed : List Nat)
    (source : State) (frame sourceFrame : Lir.Frame Nat)
    (initialMemory finalMemory : Lir.Memory) (sourceWords : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : Effects.Source.Invariant frame initialMemory source sourceFrame finalMemory sourceWords meaning)
    (guarded : ((evalBlock block observed).run { nodes := source.nodes }).2.nodes.any Expr.isPartialLeaf source.nodes.size = false)
    (sameEffects : ((evalBlock block observed).run { nodes := source.nodes }).2.effects = source.effects) :
    ∃ exit frame' values newMeaning,
      BlockExec calls block frame initialMemory exit frame' finalMemory ∧
      observed.mapM frame'.get = some values ∧
      BlockResult { nodes := source.nodes } ((evalBlock block observed).run { nodes := source.nodes }).2 frame'
        ((evalBlock block observed).run { nodes := source.nodes }).1.1
        ((evalBlock block observed).run { nodes := source.nodes }).1.2 exit values meaning newMeaning := by
  have finalPrefix : EffectPrefix ((evalBlock block observed).run { nodes := source.nodes }).2.effects source.effects := by
    rw [sameEffects]
    exact .refl _
  obtain ⟨exit, frame', memory', values, newMeaning, nextWords, executed, read, actual, trace⟩ :=
    block_success calls block admitted observed source { nodes := source.nodes } frame meaning
      (seed_rooted source frame sourceFrame initialMemory finalMemory sourceWords meaning invariant)
      invariant.total (Nat.le_refl _) initialMemory initialMemory finalMemory sourceWords []
      (seed_trace source frame sourceFrame initialMemory finalMemory sourceWords meaning invariant)
      (Validation.Candidate.guarded_of_any _ _ guarded) finalPrefix
  have sameMemory : memory' = finalMemory := (trace.complete sameEffects).2
  exact ⟨exit, frame', values, newMeaning, sameMemory ▸ executed, read, actual⟩

/-- Actual checker acceptance derives the candidate's real execution, exact
source final memory, whole slot map and observed source outputs. The source
execution and independent primitive/floating syntax are the only semantic inputs. -/
theorem accepted_block_success (calls : OpenCalls) (base : Nat) (source candidate : Mir.Block)
    (frame sourceFrame : Lir.Frame Nat) (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceAdmitted : Floating.Admitted source.instrs.toList)
    (candidateAdmitted : Floating.Admitted candidate.instrs.toList)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory)
    (accepted : check base source candidate = true) :
    ∃ candidateFrame values, BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (Acceptance.observedRegs source).mapM sourceFrame.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  have facts : Acceptance.Accepted base source candidate :=
    (Acceptance.check_eq_true_iff base source candidate).mp accepted
  obtain ⟨meaning, sourceWords, values, sourceRead, sourceResult⟩ :=
    Source.source_block calls source frame sourceFrame memory sourceMemory exit sourceAdmitted sourceExecuted
  obtain ⟨candidateExit, candidateFrame, candidateValues, newMeaning, candidateExecuted, candidateRead, candidateResult⟩ :=
    seeded_block_success calls candidate candidateAdmitted (Acceptance.observedRegs source)
      (Acceptance.sourceRun source).2 frame sourceFrame memory sourceMemory sourceWords meaning sourceResult.invariant
      facts.partialLeaves facts.effects.symm
  obtain ⟨sameExit, sameValues, slotsSame⟩ := Effects.Candidate.accepted_results_match sourceResult candidateResult facts
  exact ⟨candidateFrame, values, sameExit ▸ candidateExecuted, slotsSame, sourceRead, sameValues ▸ candidateRead⟩

end Silmaril.Compiler.Native.Optimize.Validation.Floating.Candidate
