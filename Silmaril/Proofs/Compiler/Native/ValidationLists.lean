module

public import Silmaril.Compiler.Native.Optimize.Validation.Lists.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Lists
open Silmaril.Machine
open Roots
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem result_trans {before middle after : State} {frame frame' : Lir.Frame Nat}
    {first middleMeaning last : Interpretation}
    (earlier : OpResult before middle frame first middleMeaning)
    (later : OpResult middle after frame' middleMeaning last) :
    OpResult before after frame' first last :=
  ⟨later.rooted, earlier.extension.trans later.extension earlier.grows,
    earlier.grows.trans later.grows, later.effects.trans earlier.effects⟩

theorem forM_nil_run (state : State) :
    (([] : List Silmaril.Compile.Mir.Instr).forM evalInstr).run state = ((), state) := rfl

theorem forM_cons_run (instruction : Silmaril.Compile.Mir.Instr)
    (rest : List Silmaril.Compile.Mir.Instr) (state : State) :
    ((instruction :: rest).forM evalInstr).run state =
      (rest.forM evalInstr).run ((evalInstr instruction).run state).2 := rfl

/-- Lift actual admitted primitive execution through the actual List.forM
StateM traversal from actual source execution, without checker acceptance. -/
theorem instructions_sound (calls : OpenCalls) (instructions : List Silmaril.Compile.Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (executed : InstructionsExec calls instructions frame memory frame' memory')
    (admitted : Admitted instructions) (state : State) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((instructions.forM evalInstr).run state).2 frame' meaning newMeaning := by
  induction executed generalizing state meaning with
  | nil => exact ⟨rfl, meaning, rooted, .refl _ _, Nat.le_refl _, rfl⟩
  | @cons instruction rest frame memory middle middleMem frame' memory' first tail ih =>
    show memory' = memory ∧ ∃ newMeaning,
      OpResult state (((instruction :: rest).forM evalInstr).run state).2 frame' meaning newMeaning
    have headAdmitted : AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Admitted rest := fun i member => admitted i (by simp [member])
    have step : middleMem = memory ∧ ∃ middleMeaning,
        OpResult state ((evalInstr instruction).run state).2 middle meaning middleMeaning := by
      cases instruction with
      | op op => exact evalInstr_op_sound calls state frame middle memory middleMem meaning rooted op headAdmitted first
      | fop op dest left right => cases headAdmitted
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect target args results => cases headAdmitted
    obtain ⟨stepMemory, middleMeaning, stepResult⟩ := step
    obtain ⟨tailMemory, newMeaning, tailResult⟩ := ih tailAdmitted
      ((evalInstr instruction).run state).2 middleMeaning stepResult.rooted
    rw [forM_cons_run]
    exact ⟨tailMemory.trans stepMemory, newMeaning, result_trans stepResult tailResult⟩

theorem list_loop_eq_forM (instructions : List Silmaril.Compile.Mir.Instr) :
    forIn instructions () (fun instruction _ => do evalInstr instruction; pure (.yield ())) =
      instructions.forM evalInstr := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih => simp only [List.forIn_cons, List.forM, bind_assoc, pure_bind, ih]

theorem array_loop_eq_forM (instructions : Array Silmaril.Compile.Mir.Instr) :
    forIn instructions () (fun instruction _ => do evalInstr instruction; pure (.yield ())) =
      instructions.toList.forM evalInstr := by
  change forIn instructions () (fun instruction _ => do evalInstr instruction; pure (.yield ())) = _
  rw [← Array.forIn_toList]
  exact list_loop_eq_forM instructions.toList

theorem array_instructions_sound (calls : OpenCalls) (instructions : Array Silmaril.Compile.Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (executed : InstructionsExec calls instructions.toList frame memory frame' memory')
    (admitted : Admitted instructions.toList) (state : State) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((forIn instructions () (fun instruction _ =>
        do evalInstr instruction; pure (.yield ()))).run state).2 frame' meaning newMeaning := by
  rw [array_loop_eq_forM]
  exact instructions_sound calls instructions.toList frame frame' memory memory' executed admitted state meaning rooted

theorem instructions_empty_effects (calls : OpenCalls) (instructions : List Silmaril.Compile.Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (executed : InstructionsExec calls instructions frame memory frame' memory')
    (admitted : Admitted instructions) (state : State) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (empty : state.effects = #[]) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((instructions.forM evalInstr).run state).2 frame' meaning newMeaning ∧
      ((instructions.forM evalInstr).run state).2.effects = #[] := by
  obtain ⟨memorySame, newMeaning, actual⟩ :=
    instructions_sound calls instructions frame frame' memory memory' executed admitted state meaning rooted
  exact ⟨memorySame, newMeaning, actual, actual.effects.trans empty⟩

/-- Expose the exact instruction prefix, then actual terminator evaluation and
observed-register reads used by the existing evalBlock implementation. -/
theorem evalBlock_run (block : Silmaril.Compile.Mir.Block) (observed : List Nat) (state : State) :
    (evalBlock block observed).run state =
      let body := (block.instrs.toList.forM evalInstr).run state
      let term := (evalTerm block.term).run body.2
      let regs := (observed.mapM readReg).run term.2
      ((term.1, regs.1), regs.2) := by
  unfold evalBlock
  rw [array_loop_eq_forM]
  rfl

end Silmaril.Compiler.Native.Optimize.Validation.Lists
