module

public import Silmaril.Compiler.Native.Optimize.Validation.SourceReads.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.SourceReads
open Silmaril.Machine
open Silmaril.Compile
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem set_written (frame : Lir.Frame Nat) (dest : Nat) (value : Lir.Word) :
    Written frame (frame.set dest value) [dest] := by
  constructor
  · intro reg prior
    by_cases same : reg = dest
    · exact ⟨value, by simp [same]⟩
    · obtain ⟨old, read⟩ := prior
      exact ⟨old, by simpa [same] using read⟩
  · intro reg member
    have same : reg = dest := by simpa using member
    subst reg
    exact ⟨value, by simp⟩

/-- Actual successful admitted operations write a defined destination and
cannot turn another previously defined register into a missing one. -/
theorem op_written (op : Lir.Op Nat) (frame frame' : Lir.Frame Nat)
    (memory memory' : Lir.Memory) (admitted : Roots.Admitted op)
    (executed : op.exec frame memory = some (frame', memory')) :
    Written frame frame' (Validation.defs (.op op)) := by
  cases op with
  | const dest value =>
    have result : frame.set dest value = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] using executed
    rw [← result.1]
    exact set_written frame dest value
  | move dest source =>
    have result : ∃ value, frame.get source = some value ∧
        frame.set dest value = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨value, read, equal, sameMemory⟩ := result
    rw [← equal]
    exact set_written frame dest value
  | unary op dest source =>
    have result : ∃ value, frame.get source = some value ∧
        frame.set dest (op.eval value) = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨value, read, equal, sameMemory⟩ := result
    rw [← equal]
    exact set_written frame dest (op.eval value)
  | binary op dest left right =>
    have result : ∃ x, frame.get left = some x ∧ ∃ y, frame.get right = some y ∧
        ∃ value, op.eval x y = some value ∧ frame.set dest value = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.mk.injEq] using executed
    obtain ⟨leftValue, leftRead, rightValue, rightRead, value, computed, equal, sameMemory⟩ := result
    rw [← equal]
    exact set_written frame dest value
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot => cases admitted
  | slotSet slot source => cases admitted

theorem instruction_written (calls : OpenCalls) (instruction : Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : Lists.AdmittedInstr instruction)
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

theorem written_trans {first middle last : Lir.Frame Nat} {head tail : List Nat}
    (firstWrite : Written first middle head) (laterWrite : Written middle last tail) :
    Written first last (head ++ tail) := by
  constructor
  · intro reg defined
    exact laterWrite.domain reg (firstWrite.domain reg defined)
  · intro reg member
    rcases List.mem_append.mp member with early | late
    · exact laterWrite.domain reg (firstWrite.defined reg early)
    · exact laterWrite.defined reg late

/-- Every actual source definition remains defined after the entire successful
admitted list, including definitions overwritten by later successful writes. -/
theorem instructions_written (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : Lists.Admitted instructions)
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

theorem defined_mapM (frame : Lir.Frame Nat) (registers : List Nat) (defined : Defined frame registers) :
    ∃ values, registers.mapM frame.get = some values := by
  induction registers with
  | nil => exact ⟨[], rfl⟩
  | cons reg rest ih =>
    obtain ⟨word, read⟩ := defined reg (by simp)
    obtain ⟨values, reads⟩ := ih (fun r member => defined r (by simp [member]))
    exact ⟨word :: values, by simp only [List.mapM_cons, Option.bind_eq_bind,
      Option.pure_def, read, Option.bind_some, reads]⟩

/-- Successful source instructions supply the actual checker-selected output
read list. Its dedup order is retained, and no incoming total frame is needed. -/
theorem observed_success (calls : OpenCalls) (block : Mir.Block)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : Lists.Admitted block.instrs.toList)
    (executed : InstructionsExec calls block.instrs.toList frame memory frame' memory') :
    ∃ values, (Acceptance.observedRegs block).mapM frame'.get = some values := by
  have written := instructions_written calls block.instrs.toList frame frame' memory memory' admitted executed
  apply defined_mapM
  intro reg member
  apply written.defined reg
  simpa only [Acceptance.observedRegs, List.mem_dedup] using member

/-- The complete actual source symbolic block result now follows from actual
source execution alone, with observed-read success derived above. -/
theorem source_block_sound (calls : OpenCalls) (block : Mir.Block)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory) (exit : BlockExit)
    (admitted : Lists.Admitted block.instrs.toList)
    (executed : BlockExec calls block frame memory exit frame' memory') :
    ∃ values newMeaning, memory' = memory ∧
      (Acceptance.observedRegs block).mapM frame'.get = some values ∧
      Observation.BlockResult {} (Acceptance.sourceRun block).2 frame'
        (Acceptance.sourceRun block).1.1 (Acceptance.sourceRun block).1.2
        exit values (Total.initialMeaning frame) newMeaning := by
  obtain ⟨values, read⟩ := observed_success calls block frame frame' memory memory' admitted executed.1
  obtain ⟨sameMemory, newMeaning, actual⟩ := Observation.source_block_sound calls block frame frame'
    memory memory' exit executed admitted (Acceptance.observedRegs block) values read
  exact ⟨values, newMeaning, sameMemory, read, actual⟩

end Silmaril.Compiler.Native.Optimize.Validation.SourceReads
