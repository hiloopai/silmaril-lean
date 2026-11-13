module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Candidate.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Candidate
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract
open Validation.Effects Validation.Effects.Candidate

/-- Existing candidate results keep the independently fixed address resolver. -/
theorem invariant_of_result (units : Array Mir.Unit) (placement : MirSem.Placement)
    (before after : State) (frame final : Lir.Frame Nat) (meaning newMeaning : Interpretation)
    (invariant : Address.Invariant units placement before frame meaning)
    (actual : Result before after final meaning newMeaning) :
    Address.Invariant units placement after final newMeaning :=
  ⟨actual.rooted, actual.total, actual.extension.address.trans invariant.address⟩

/-- Mixed address interning adds no event; primitive and floating effect-growth
facts are reused through their public interface. -/
theorem growing_evalInstr (instruction : Mir.Instr) (admitted : AdmittedInstr instruction) :
    EffectGrowing (evalInstr instruction) := by
  cases instruction with
  | op operation => exact Floating.Candidate.growing_evalInstr (.op operation) trivial
  | fop op dest left right => exact Floating.Candidate.growing_evalInstr (.fop op dest left right) trivial
  | addr dest symbol offset =>
    exact growing_bind _ _ (growing_intern (.addr symbol offset)) (fun output => growing_writeReg dest output)
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem growing_forM (instructions : List Mir.Instr) (admitted : Admitted instructions) :
    EffectGrowing (instructions.forM evalInstr) := by
  induction instructions with
  | nil => exact growing_pure ()
  | cons instruction rest ih =>
    intro state
    rw [Lists.forM_cons_run]
    exact (growing_evalInstr instruction (admitted instruction (by simp)) state).trans
      (ih (fun i member => admitted i (by simp [member])) ((evalInstr instruction).run state).2)

namespace Nodes

theorem evalInstr (instruction : Mir.Instr) (admitted : AdmittedInstr instruction) :
    Validation.Candidate.Growing (Validation.evalInstr instruction) := by
  cases instruction with
  | op operation => exact Floating.Candidate.Nodes.evalInstr (.op operation) trivial
  | fop op dest left right => exact Floating.Candidate.Nodes.evalInstr (.fop op dest left right) trivial
  | addr dest symbol offset =>
    exact Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_intern (.addr symbol offset))
      (fun output => Validation.Candidate.growing_writeReg dest output)
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem forM (instructions : List Mir.Instr) (admitted : Admitted instructions) :
    Validation.Candidate.Growing (instructions.forM Validation.evalInstr) := by
  induction instructions with
  | nil => exact Validation.Candidate.growing_pure ()
  | cons instruction rest ih =>
    intro state
    rw [Lists.forM_cons_run]
    exact (evalInstr instruction (admitted instruction (by simp)) state).trans
      (ih (fun i member => admitted i (by simp [member])) ((Validation.evalInstr instruction).run state).2)

end Nodes

/-- Actual primitive/floating/address candidate execution is derived from the
real retained-node guard and ordered effect prefix. Target reads, resolution and
execution are conclusions, including when the incoming frame is partial. -/
theorem instruction_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (instruction : Mir.Instr) (admitted : AdmittedInstr instruction)
    (source state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (invariant : Address.Invariant units placement state frame meaning)
    (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((evalInstr instruction).run state).2.nodes)
    (afterPrefix : EffectPrefix ((evalInstr instruction).run state).2.effects source.effects) :
    ∃ frame' memory' newMeaning nextWords,
      InstructionExec (calls units placement) instruction frame memory frame' memory' ∧
      Result state ((evalInstr instruction).run state).2 frame' meaning newMeaning ∧
      Trace source ((evalInstr instruction).run state).2 newMeaning initialMemory memory' finalMemory sourceWords nextWords ∧
      Address.Invariant units placement ((evalInstr instruction).run state).2 frame' newMeaning := by
  cases instruction with
  | op operation =>
    obtain ⟨frame', memory', newMeaning, nextWords, executed, actual, afterTrace⟩ :=
      Validation.Effects.Candidate.evalOp_success source state frame meaning invariant.rooted invariant.total old
        initialMemory memory finalMemory sourceWords words trace operation guarded afterPrefix
    exact ⟨frame', memory', newMeaning, nextWords, .op executed, actual, afterTrace,
      invariant_of_result units placement state _ frame frame' meaning newMeaning invariant actual⟩
  | fop op dest left right =>
    obtain ⟨frame', newMeaning, executed, actual, afterTrace⟩ :=
      Floating.Candidate.fop_success source state frame meaning invariant.rooted invariant.total old
        initialMemory memory finalMemory sourceWords words trace op dest left right guarded
    exact ⟨frame', memory, newMeaning, words, .fop executed, actual, afterTrace,
      invariant_of_result units placement state _ frame frame' meaning newMeaning invariant actual⟩
  | addr dest symbol offset =>
    obtain ⟨word, newMeaning, _, executed, actual, afterTrace, after⟩ :=
      Address.Effects.candidate_addr_success units placement source state frame meaning invariant old
        initialMemory memory finalMemory sourceWords words trace dest symbol offset guarded
    exact ⟨frame.set dest word, memory, newMeaning, words, executed, actual, afterTrace, after⟩
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

/-- Every admitted mixed candidate list really executes, consuming the actual
source trace in order while retaining its fixed resolver and ghost load map. -/
theorem instructions_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (instructions : List Mir.Instr) (admitted : Admitted instructions)
    (source state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (invariant : Address.Invariant units placement state frame meaning)
    (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((instructions.forM evalInstr).run state).2.nodes)
    (afterPrefix : EffectPrefix ((instructions.forM evalInstr).run state).2.effects source.effects) :
    ∃ frame' memory' newMeaning nextWords,
      InstructionsExec (calls units placement) instructions frame memory frame' memory' ∧
      Result state ((instructions.forM evalInstr).run state).2 frame' meaning newMeaning ∧
      Trace source ((instructions.forM evalInstr).run state).2 newMeaning initialMemory memory' finalMemory sourceWords nextWords ∧
      Address.Invariant units placement ((instructions.forM evalInstr).run state).2 frame' newMeaning := by
  induction instructions generalizing state frame meaning memory words with
  | nil => exact ⟨frame, memory, meaning, words, .nil,
      ⟨invariant.rooted, invariant.total, .refl _ _, Nat.le_refl _⟩, trace, invariant⟩
  | cons instruction rest ih =>
    show ∃ frame' memory' newMeaning nextWords,
      InstructionsExec (calls units placement) (instruction :: rest) frame memory frame' memory' ∧
      Result state (((instruction :: rest).forM evalInstr).run state).2 frame' meaning newMeaning ∧
      Trace source (((instruction :: rest).forM evalInstr).run state).2 newMeaning initialMemory memory' finalMemory sourceWords nextWords ∧
      Address.Invariant units placement (((instruction :: rest).forM evalInstr).run state).2 frame' newMeaning
    have headAdmitted : AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Admitted rest := fun i member => admitted i (by simp [member])
    have tailGuard : Validation.Candidate.Guarded source.nodes.size
        ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.nodes := by
      simpa only [Lists.forM_cons_run] using guarded
    have headGuard : Validation.Candidate.Guarded source.nodes.size ((evalInstr instruction).run state).2.nodes :=
      tailGuard.prefix (Nodes.forM rest tailAdmitted ((evalInstr instruction).run state).2)
    have tailPrefix : EffectPrefix ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.effects source.effects := by
      simpa only [Lists.forM_cons_run] using afterPrefix
    have headPrefix : EffectPrefix ((evalInstr instruction).run state).2.effects source.effects :=
      (growing_forM rest tailAdmitted ((evalInstr instruction).run state).2).trans tailPrefix
    obtain ⟨middle, middleMemory, middleMeaning, middleWords, headExecuted, headResult, headTrace, headInvariant⟩ :=
      instruction_success units placement instruction headAdmitted source state frame meaning invariant old
        initialMemory memory finalMemory sourceWords words trace headGuard headPrefix
    obtain ⟨frame', memory', newMeaning, nextWords, tailExecuted, tailResult, tailTrace, tailInvariant⟩ :=
      ih tailAdmitted ((evalInstr instruction).run state).2 middle middleMeaning headInvariant
        (old.trans headResult.grows) middleMemory middleWords headTrace tailGuard tailPrefix
    rw [Lists.forM_cons_run]
    exact ⟨frame', memory', newMeaning, nextWords, .cons headExecuted tailExecuted,
      headResult.trans tailResult, tailTrace, tailInvariant⟩

/-- The completed real source independently supplies the full retained DAG and
load interpretation. Equality with its effects forces exact final memory. -/
theorem seeded_instructions_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (instructions : List Mir.Instr) (admitted : Admitted instructions)
    (source : State) (frame sourceFrame : Lir.Frame Nat)
    (initialMemory finalMemory : Lir.Memory) (sourceWords : List (Option Lir.Word)) (meaning : Interpretation)
    (sourceInvariant : Validation.Effects.Source.InvariantWith (resolve units placement)
      frame initialMemory source sourceFrame finalMemory sourceWords meaning)
    (guarded : Validation.Candidate.Guarded source.nodes.size
      ((instructions.forM evalInstr).run { nodes := source.nodes }).2.nodes)
    (sameEffects : ((instructions.forM evalInstr).run { nodes := source.nodes }).2.effects = source.effects) :
    ∃ frame' newMeaning,
      InstructionsExec (calls units placement) instructions frame initialMemory frame' finalMemory ∧
      Result { nodes := source.nodes } ((instructions.forM evalInstr).run { nodes := source.nodes }).2 frame' meaning newMeaning ∧
      Trace source ((instructions.forM evalInstr).run { nodes := source.nodes }).2 newMeaning
        initialMemory finalMemory finalMemory sourceWords sourceWords ∧
      Address.Invariant units placement ((instructions.forM evalInstr).run { nodes := source.nodes }).2 frame' newMeaning := by
  obtain ⟨seeded, initialTrace⟩ := Address.Effects.source_seed units placement source frame sourceFrame
    initialMemory finalMemory sourceWords meaning sourceInvariant
  have finalPrefix : EffectPrefix ((instructions.forM evalInstr).run { nodes := source.nodes }).2.effects source.effects := by
    rw [sameEffects]
    exact .refl _
  obtain ⟨frame', memory', newMeaning, nextWords, executed, actual, trace, invariant⟩ :=
    instructions_success units placement instructions admitted source { nodes := source.nodes } frame meaning seeded
      (Nat.le_refl _) initialMemory initialMemory finalMemory sourceWords [] initialTrace guarded finalPrefix
  obtain ⟨sameWords, sameMemory⟩ := trace.complete sameEffects
  subst nextWords
  subst memory'
  exact ⟨frame', newMeaning, executed, actual, trace, invariant⟩

/-- Mixed body replay delegates terminator and observed-register execution to
the common fragment-independent finishing theorem. -/
theorem block_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (block : Mir.Block) (admitted : Admitted block.instrs.toList) (observed : List Nat)
    (source state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (invariant : Address.Invariant units placement state frame meaning)
    (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((evalBlock block observed).run state).2.nodes)
    (afterPrefix : EffectPrefix ((evalBlock block observed).run state).2.effects source.effects) :
    ∃ exit frame' memory' values newMeaning nextWords,
      BlockExec (calls units placement) block frame memory exit frame' memory' ∧
      observed.mapM frame'.get = some values ∧
      BlockResult state ((evalBlock block observed).run state).2 frame'
        ((evalBlock block observed).run state).1.1 ((evalBlock block observed).run state).1.2 exit values meaning newMeaning ∧
      Trace source ((evalBlock block observed).run state).2 newMeaning initialMemory memory' finalMemory sourceWords nextWords ∧
      Address.Invariant units placement ((evalBlock block observed).run state).2 frame' newMeaning := by
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
  obtain ⟨frame', memory', bodyMeaning, bodyWords, bodyExecuted, bodyResult, bodyTrace, _⟩ :=
    instructions_success units placement block.instrs.toList admitted source state frame meaning invariant old
      initialMemory memory finalMemory sourceWords words trace bodyGuard bodyPrefix
  obtain ⟨exit, values, newMeaning, executed, read, actual, finalTrace⟩ :=
    Validation.Effects.Candidate.finish_block (calls units placement) block observed source state frame frame' meaning bodyMeaning old
      initialMemory memory memory' finalMemory sourceWords bodyWords guarded bodyExecuted bodyResult bodyTrace
  exact ⟨exit, frame', memory', values, newMeaning, bodyWords, executed, read, actual, finalTrace,
    invariant_of_result units placement state _ frame frame' meaning newMeaning invariant actual.result⟩

/-- Real source completion and the candidate's actual full-block guard/effect
equality derive its complete successful execution and exact source memory. -/
theorem seeded_block_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (block : Mir.Block) (admitted : Admitted block.instrs.toList) (observed : List Nat)
    (source : State) (frame sourceFrame : Lir.Frame Nat)
    (initialMemory finalMemory : Lir.Memory) (sourceWords : List (Option Lir.Word)) (meaning : Interpretation)
    (sourceInvariant : Validation.Effects.Source.InvariantWith (resolve units placement)
      frame initialMemory source sourceFrame finalMemory sourceWords meaning)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((evalBlock block observed).run { nodes := source.nodes }).2.nodes)
    (sameEffects : ((evalBlock block observed).run { nodes := source.nodes }).2.effects = source.effects) :
    ∃ exit frame' values newMeaning,
      BlockExec (calls units placement) block frame initialMemory exit frame' finalMemory ∧
      observed.mapM frame'.get = some values ∧
      BlockResult { nodes := source.nodes } ((evalBlock block observed).run { nodes := source.nodes }).2 frame'
        ((evalBlock block observed).run { nodes := source.nodes }).1.1
        ((evalBlock block observed).run { nodes := source.nodes }).1.2 exit values meaning newMeaning ∧
      Trace source ((evalBlock block observed).run { nodes := source.nodes }).2 newMeaning
        initialMemory finalMemory finalMemory sourceWords sourceWords ∧
      Address.Invariant units placement ((evalBlock block observed).run { nodes := source.nodes }).2 frame' newMeaning := by
  obtain ⟨seeded, initialTrace⟩ := Address.Effects.source_seed units placement source frame sourceFrame
    initialMemory finalMemory sourceWords meaning sourceInvariant
  have finalPrefix : EffectPrefix ((evalBlock block observed).run { nodes := source.nodes }).2.effects source.effects := by
    rw [sameEffects]
    exact .refl _
  obtain ⟨exit, frame', memory', values, newMeaning, nextWords, executed, read, actual, trace, invariant⟩ :=
    block_success units placement block admitted observed source { nodes := source.nodes } frame meaning seeded
      (Nat.le_refl _) initialMemory initialMemory finalMemory sourceWords [] initialTrace guarded finalPrefix
  obtain ⟨sameWords, sameMemory⟩ := trace.complete sameEffects
  subst nextWords
  subst memory'
  exact ⟨exit, frame', values, newMeaning, executed, read, actual, trace, invariant⟩

/-- The actual boolean checker supplies retained-leaf guard and exact effect
equality. The completed independent source invariant is the semantic input;
no candidate resolution, reads, memory run or terminator run is supplied. -/
theorem accepted_block_result (units : Array Mir.Unit) (placement : MirSem.Placement)
    (base : Nat) (source candidate : Mir.Block) (admitted : Admitted candidate.instrs.toList)
    (frame sourceFrame : Lir.Frame Nat) (initialMemory finalMemory : Lir.Memory)
    (sourceWords : List (Option Lir.Word)) (meaning : Interpretation)
    (sourceInvariant : Validation.Effects.Source.InvariantWith (resolve units placement)
      frame initialMemory (Acceptance.sourceRun source).2 sourceFrame finalMemory sourceWords meaning)
    (accepted : check base source candidate = true) :
    ∃ exit frame' values newMeaning,
      BlockExec (calls units placement) candidate frame initialMemory exit frame' finalMemory ∧
      (Acceptance.observedRegs source).mapM frame'.get = some values ∧
      BlockResult { nodes := (Acceptance.sourceRun source).2.nodes } (Acceptance.candidateRun source candidate).2 frame'
        (Acceptance.candidateRun source candidate).1.1 (Acceptance.candidateRun source candidate).1.2 exit values meaning newMeaning ∧
      Trace (Acceptance.sourceRun source).2 (Acceptance.candidateRun source candidate).2 newMeaning
        initialMemory finalMemory finalMemory sourceWords sourceWords ∧
      Address.Invariant units placement (Acceptance.candidateRun source candidate).2 frame' newMeaning := by
  have facts : Acceptance.Accepted base source candidate := (Acceptance.check_eq_true_iff base source candidate).mp accepted
  exact seeded_block_success units placement candidate admitted (Acceptance.observedRegs source) (Acceptance.sourceRun source).2
    frame sourceFrame initialMemory finalMemory sourceWords meaning sourceInvariant
    (Validation.Candidate.guarded_of_any _ _ facts.partialLeaves) facts.effects.symm

/-- The complete retained result yields real target execution and available
actual observations without any candidate-run premise. -/
theorem accepted_block_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (base : Nat) (source candidate : Mir.Block) (admitted : Admitted candidate.instrs.toList)
    (frame sourceFrame : Lir.Frame Nat) (initialMemory finalMemory : Lir.Memory)
    (sourceWords : List (Option Lir.Word)) (meaning : Interpretation)
    (sourceInvariant : Validation.Effects.Source.InvariantWith (resolve units placement)
      frame initialMemory (Acceptance.sourceRun source).2 sourceFrame finalMemory sourceWords meaning)
    (accepted : check base source candidate = true) :
    ∃ exit frame' values,
      BlockExec (calls units placement) candidate frame initialMemory exit frame' finalMemory ∧
      (Acceptance.observedRegs source).mapM frame'.get = some values := by
  obtain ⟨exit, frame', values, _, executed, read, _, _, _⟩ :=
    accepted_block_result units placement base source candidate admitted frame sourceFrame initialMemory finalMemory
      sourceWords meaning sourceInvariant accepted
  exact ⟨exit, frame', values, executed, read⟩

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Candidate
