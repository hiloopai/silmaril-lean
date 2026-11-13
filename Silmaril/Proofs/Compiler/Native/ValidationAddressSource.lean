module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Source.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Source
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract
open Validation.Effects

/-- Every real mixed instruction supplies its declared output. Other register
availability is retained, including for a genuinely partial incoming frame. -/
theorem instruction_written (units : Array Mir.Unit) (placement : MirSem.Placement)
    (instruction : Mir.Instr) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : AdmittedInstr instruction)
    (executed : InstructionExec (calls units placement) instruction frame memory final finalMemory) :
    SourceReads.Written frame final (Validation.defs instruction) := by
  cases instruction with
  | op operation => exact Floating.Source.instruction_written _ (.op operation) frame final memory finalMemory trivial executed
  | fop operation dest left right =>
    exact Floating.Source.instruction_written _ (.fop operation dest left right) frame final memory finalMemory trivial executed
  | addr dest symbol offset =>
    cases executed with
    | addr resolved => exact SourceReads.set_written frame dest _
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem instructions_written (units : Array Mir.Unit) (placement : MirSem.Placement)
    (instructions : List Mir.Instr) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Admitted instructions)
    (executed : InstructionsExec (calls units placement) instructions frame memory final finalMemory) :
    SourceReads.Written frame final (instructions.flatMap Validation.defs) := by
  induction executed with
  | nil => exact ⟨fun _ prior => prior, fun _ member => nomatch member⟩
  | @cons instruction rest frame memory middle middleMemory final finalMemory first later ih =>
    have firstWrite := instruction_written units placement instruction frame middle memory middleMemory
      (admitted instruction (by simp)) first
    have laterWrite := ih (fun i member => admitted i (by simp [member]))
    exact SourceReads.written_trans firstWrite laterWrite

/-- The actual source's observed register list contains only outputs of real
successful writes, so no separate successful observed-read premise is needed. -/
theorem observed_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (block : Mir.Block) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Admitted block.instrs.toList)
    (executed : InstructionsExec (calls units placement) block.instrs.toList frame memory final finalMemory) :
    ∃ values, (Acceptance.observedRegs block).mapM final.get = some values := by
  have written := instructions_written units placement block.instrs.toList frame final memory finalMemory admitted executed
  apply SourceReads.defined_mapM
  intro reg member
  apply written.defined reg
  simpa only [Acceptance.observedRegs, List.mem_dedup] using member

/-- Real source execution builds its complete fixed-resolver invariant. The
shared terminator/observation proof adds no events or invented load results. -/
theorem block_with_reads (units : Array Mir.Unit) (placement : MirSem.Placement)
    (block : Mir.Block) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (admitted : Admitted block.instrs.toList)
    (executed : BlockExec (calls units placement) block frame memory exit final finalMemory)
    (observed : List Nat) (values : List Lir.Word) (read : observed.mapM final.get = some values) :
    ∃ meaning words, Validation.Effects.Source.BlockResultWith (resolve units placement) frame memory
      ((evalBlock block observed).run {}).2 final finalMemory words
      ((evalBlock block observed).run {}).1.1 ((evalBlock block observed).run {}).1.2 exit values meaning := by
  obtain ⟨bodyMeaning, bodyWords, bodyInvariant⟩ := source_instructions_invariant units placement block.instrs.toList
    frame final memory finalMemory admitted executed.1
  obtain ⟨meaning, result⟩ := Validation.Effects.Source.finish_block (resolve units placement) block frame final
    memory finalMemory exit bodyMeaning bodyWords bodyInvariant executed.2 observed values read
  exact ⟨meaning, bodyWords, result⟩

/-- Actual successful mixed source execution derives the complete checker
sourceRun invariant, selected exit and observed values, with exact real memory. -/
theorem source_block (units : Array Mir.Unit) (placement : MirSem.Placement)
    (block : Mir.Block) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (admitted : Admitted block.instrs.toList)
    (executed : BlockExec (calls units placement) block frame memory exit final finalMemory) :
    ∃ meaning words values,
      (Acceptance.observedRegs block).mapM final.get = some values ∧
      Validation.Effects.Source.BlockResultWith (resolve units placement) frame memory
        (Acceptance.sourceRun block).2 final finalMemory words
        (Acceptance.sourceRun block).1.1 (Acceptance.sourceRun block).1.2 exit values meaning := by
  obtain ⟨values, read⟩ := observed_success units placement block frame final memory finalMemory admitted executed.1
  obtain ⟨meaning, words, result⟩ := block_with_reads units placement block frame final memory finalMemory exit admitted executed
    (Acceptance.observedRegs block) values read
  exact ⟨meaning, words, values, read, result⟩

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Source
