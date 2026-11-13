module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.InstructionSemantics.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.InstructionSemantics
open Silmaril.Compile Silmaril.Machine

theorem frame_get (source : Lir.Frame Nat) (register : Nat) :
    (frame source).get register = source.get register := rfl

theorem frame_set (source : Lir.Frame Nat) (register : Nat) (value : Lir.Word) :
    frame (source.set register value) = (frame source).set register value := rfl

/-- Admission preserves the actual partial primitive executor, including
unwritten-register failure. No successful source execution is assumed. -/
theorem oldOp_execute (instruction : Mir.Instr) (old : Old.Op)
    (admitted : oldOp instruction = some old) (source : Lir.Frame Nat)
    (memory : Lir.Memory) (oldMemory : Silmaril.Machine.Lir.Memory) :
    old.exec (frame source) oldMemory =
      (execute instruction source memory).map (fun result => (frame result.1, oldMemory)) := by
  cases instruction with
  | op operation =>
    show old.exec (frame source) oldMemory =
      (execute (.op operation) source memory).map (fun result => (frame result.1, oldMemory))
    cases operation with
    | const destination value =>
      cases admitted
      rfl
    | move destination operand =>
      cases admitted
      simp only [execute, Lir.Op.exec, Silmaril.Machine.RTL.SSA.Op.exec, frame_get]
      cases source.get operand <;> rfl
    | unary operation destination operand =>
      cases admitted
      simp only [execute, Lir.Op.exec, Silmaril.Machine.RTL.SSA.Op.exec, frame_get, oldUnary_eval]
      cases source.get operand <;> rfl
    | binary operation destination left right =>
      show old.exec (frame source) oldMemory =
        (execute (.op (.binary operation destination left right)) source memory).map
          (fun result => (frame result.1, oldMemory))
      have selected : (oldBinary operation).map (Silmaril.Machine.RTL.SSA.Op.binary · destination left right) = some old :=
        admitted
      obtain ⟨converted, binaryAccepted, same⟩ := Option.map_eq_some_iff.mp selected
      cases same
      simp only [execute, Lir.Op.exec, Silmaril.Machine.RTL.SSA.Op.exec, frame_get,
        oldBinary_eval operation converted binaryAccepted, Option.map_bind, Option.map_map,
        Function.comp_def, frame_set]
    | _ => cases admitted
  | _ => cases admitted

/-- Flattening's identity register map round trips every admitted old
primitive. Calls, memory and unsupported binary operators remain rejected. -/
theorem newOp_oldOp (old : Old.Op) (instruction : Mir.Instr)
    (converted : newOp id old = some instruction) : oldOp instruction = some old := by
  cases old with
  | const destination value => cases converted; rfl
  | move destination operand => cases converted; rfl
  | unary operation destination operand =>
      cases converted
      cases operation <;> rfl
  | binary operation destination left right =>
      cases operation <;> simp only [newOp, newBinary, Option.map_some,
        Option.map_none, reduceCtorEq, Option.some.injEq] at converted
      all_goals cases converted; rfl
  | _ => cases converted

/-- The reverse adapter with identity register names has the same exact
partial-executor correspondence. Register remapping is a separate obligation. -/
theorem newOp_execute (old : Old.Op) (instruction : Mir.Instr)
    (converted : newOp id old = some instruction) (source : Lir.Frame Nat)
    (memory : Lir.Memory) (oldMemory : Silmaril.Machine.Lir.Memory) :
    old.exec (frame source) oldMemory =
      (execute instruction source memory).map (fun result => (frame result.1, oldMemory)) :=
  oldOp_execute instruction old (newOp_oldOp old instruction converted) source memory oldMemory

/-- The admitted native primitive leaves the actual native memory and slot
map unchanged. Slot preservation is stated before projecting to older RTL. -/
theorem execute_preserves {instruction : Mir.Instr} {old : Old.Op}
    (admitted : oldOp instruction = some old) (source final : Lir.Frame Nat)
    (memory finalMemory : Lir.Memory)
    (executed : execute instruction source memory = some (final, finalMemory)) :
    final.slots = source.slots ∧ finalMemory = memory := by
  cases instruction with
  | op operation =>
    show final.slots = source.slots ∧ finalMemory = memory
    cases operation with
    | const destination value =>
      cases executed
      exact ⟨rfl, rfl⟩
    | move destination operand =>
      obtain ⟨value, _, equal⟩ : ∃ value, source.get operand = some value ∧
          (source.set destination value, memory) = (final, finalMemory) := by
        simpa only [execute, Lir.Op.exec, Option.map_eq_some_iff] using executed
      cases equal
      exact ⟨rfl, rfl⟩
    | unary operation destination operand =>
      obtain ⟨value, _, equal⟩ : ∃ value, source.get operand = some value ∧
          (source.set destination (operation.eval value), memory) = (final, finalMemory) := by
        simpa only [execute, Lir.Op.exec, Option.map_eq_some_iff] using executed
      cases equal
      exact ⟨rfl, rfl⟩
    | binary operation destination left right =>
      show final.slots = source.slots ∧ finalMemory = memory
      obtain ⟨leftValue, _, rightValue, _, value, _, equal⟩ :
          ∃ leftValue, source.get left = some leftValue ∧
          ∃ rightValue, source.get right = some rightValue ∧
          ∃ value, operation.eval leftValue rightValue = some value ∧
            (source.set destination value, memory) = (final, finalMemory) := by
        simpa only [execute, Lir.Op.exec, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] using executed
      cases equal
      exact ⟨rfl, rfl⟩
    | _ => cases admitted
  | _ => cases admitted

/-- For an admitted primitive, the wrapper is exactly the existing open MIR
instruction relation, for arbitrary address and call summaries. -/
theorem instructionExec_iff {instruction : Mir.Instr} {old : Old.Op}
    (admitted : oldOp instruction = some old) (calls : OpenCalls)
    (source final : Lir.Frame Nat) (memory finalMemory : Lir.Memory) :
    InstructionExec calls instruction source memory final finalMemory ↔
      execute instruction source memory = some (final, finalMemory) := by
  cases instruction with
  | op operation =>
      constructor
      · intro executed
        cases executed with | op executed => exact executed
      · exact InstructionExec.op
  | _ => cases admitted

end Silmaril.Compiler.Native.Optimize.LambdaSSA.InstructionSemantics
