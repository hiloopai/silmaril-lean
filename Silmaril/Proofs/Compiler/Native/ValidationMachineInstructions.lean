module

public import Silmaril.Compiler.Native.Optimize.Validation.Machine.Instructions.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Machine.Instructions
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract
open Relation Validation.Finite

theorem instructions_steps {calls : OpenCalls} {units : Array Mir.Unit} {placement : MirSem.Placement}
    {admittedInstr : Mir.Instr → Prop} (bridge : Bridge units placement calls admittedInstr)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (preceding instructions : List Mir.Instr)
    (layout : block.instrs.toList = preceding ++ instructions)
    (admitted : ∀ instruction ∈ instructions, admittedInstr instruction)
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : InstructionsExec calls instructions frame memory finalFrame finalMemory) :
    ReflTransGen (MirSem.Step units placement) ⟨function, label, preceding.length, frame, stack, memory⟩
      ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩ := by
  induction executed generalizing preceding with
  | nil =>
    have size : block.instrs.size = preceding.length := by simpa only [List.append_nil, Array.length_toList] using congrArg List.length layout
    rw [size]
  | @cons instruction rest frame memory middle middleMemory finalFrame finalMemory first later ih =>
    show ReflTransGen (MirSem.Step units placement) ⟨function, label, preceding.length, frame, stack, memory⟩
      ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩
    have headAdmitted : admittedInstr instruction := admitted instruction (by simp)
    have atIndex : block.instrs[preceding.length]? = some instruction := by
      rw [← Array.getElem?_toList, layout, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have firstStep : MirSem.Step units placement ⟨function, label, preceding.length, frame, stack, memory⟩
        ⟨function, label, preceding.length + 1, middle, stack, middleMemory⟩ := by
      exact bridge.sound function label preceding.length block instruction found atIndex headAdmitted
        frame middle stack memory middleMemory first
    have restLayout : block.instrs.toList = (preceding ++ [instruction]) ++ rest := by
      simpa only [List.append_assoc, List.singleton_append] using layout
    have tailSteps : ReflTransGen (MirSem.Step units placement)
        ⟨function, label, (preceding ++ [instruction]).length, middle, stack, middleMemory⟩
        ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩ :=
      ih (preceding ++ [instruction]) restLayout (fun i h => admitted i (by simp [h]))
    exact ReflTransGen.head firstStep (by simpa only [List.length_append, List.length_singleton] using tailSteps)

theorem block_steps {calls : OpenCalls} {units : Array Mir.Unit} {placement : MirSem.Placement}
    {admittedInstr : Mir.Instr → Prop} (bridge : Bridge units placement calls admittedInstr)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : ∀ instruction ∈ block.instrs.toList, admittedInstr instruction)
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block frame memory exit finalFrame finalMemory) :
    ReflTransGen (MirSem.Step units placement) ⟨function, label, 0, frame, stack, memory⟩
      ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩ ∧
    MirSem.step units placement ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩ =
      finish ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩ exit := by
  have body := instructions_steps bridge function label block found [] block.instrs.toList rfl
    admitted frame finalFrame stack memory finalMemory executed.1
  refine ⟨body, ?_⟩
  rw [Mir.FuncPass.step_term units placement _ block found rfl, termOut_of_exec block.term finalFrame exit executed.2]
  cases exit with
  | jump label => rfl
  | returned words => rfl
  | trapped => rfl

theorem jump_steps {calls : OpenCalls} {units : Array Mir.Unit} {placement : MirSem.Placement}
    {admittedInstr : Mir.Instr → Prop} (bridge : Bridge units placement calls admittedInstr)
    (function : Mir.Func) (label next : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : ∀ instruction ∈ block.instrs.toList, admittedInstr instruction)
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : BlockExec calls block frame memory (.jump next) finalFrame finalMemory) :
    ReflTransGen (MirSem.Step units placement) ⟨function, label, 0, frame, stack, memory⟩
      ⟨function, next, 0, finalFrame, stack, finalMemory⟩ := by
  obtain ⟨body, terminal⟩ := block_steps bridge function label block found admitted
    frame finalFrame stack memory finalMemory (.jump next) executed
  exact body.tail terminal

theorem returned_behaves {calls : OpenCalls} {units : Array Mir.Unit} {placement : MirSem.Placement}
    {admittedInstr : Mir.Instr → Prop} (bridge : Bridge units placement calls admittedInstr)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : ∀ instruction ∈ block.instrs.toList, admittedInstr instruction)
    (frame finalFrame : Lir.Frame Nat) (memory finalMemory : Lir.Memory) (words : List Lir.Word)
    (executed : BlockExec calls block frame memory (.returned words) finalFrame finalMemory) :
    MirSem.Behaves units placement ⟨function, label, 0, frame, [], memory⟩ (.returned words finalMemory) := by
  obtain ⟨body, terminal⟩ := block_steps bridge function label block found admitted
    frame finalFrame [] memory finalMemory (.returned words) executed
  exact ⟨_, body, terminal⟩

theorem trapped_behaves {calls : OpenCalls} {units : Array Mir.Unit} {placement : MirSem.Placement}
    {admittedInstr : Mir.Instr → Prop} (bridge : Bridge units placement calls admittedInstr)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : ∀ instruction ∈ block.instrs.toList, admittedInstr instruction)
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : BlockExec calls block frame memory .trapped finalFrame finalMemory) :
    MirSem.Behaves units placement ⟨function, label, 0, frame, stack, memory⟩ (.trapped finalMemory) := by
  obtain ⟨body, terminal⟩ := block_steps bridge function label block found admitted
    frame finalFrame stack memory finalMemory .trapped executed
  exact ⟨_, body, terminal⟩

/-- Extract a genuine independent instruction execution from a successful
actual finite run, using the proved entire next-state shape of the bridge. -/
theorem instruction_run {calls : OpenCalls} {units : Array Mir.Unit} {placement : MirSem.Placement}
    {admittedInstr : Mir.Instr → Prop} (bridge : Bridge units placement calls admittedInstr)
    (outcome : Outcome) (function : Mir.Func) (label index : Nat) (block : Mir.Block)
    (instruction : Mir.Instr) (found : function.blocks[label]? = some block)
    (selected : block.instrs[index]? = some instruction) (admitted : admittedInstr instruction)
    (frame : Lir.Frame Nat) (memory : Lir.Memory) (count : Nat)
    (run : Run units placement outcome count ⟨function, label, index, frame, [], memory⟩) :
    ∃ finalFrame finalMemory remaining, count = remaining + 1 ∧
      InstructionExec calls instruction frame memory finalFrame finalMemory ∧
      Run units placement outcome remaining ⟨function, label, index + 1, finalFrame, [], finalMemory⟩ := by
  obtain ⟨finalFrame, finalMemory, executed, step⟩ :=
    bridge.complete function label index block instruction found selected admitted frame [] memory (run_not_stuck run)
  obtain ⟨remaining, size, rest⟩ := run_running run step
  exact ⟨finalFrame, finalMemory, remaining, size, executed, rest⟩

theorem instructions_run {calls : OpenCalls} {units : Array Mir.Unit} {placement : MirSem.Placement}
    {admittedInstr : Mir.Instr → Prop} (bridge : Bridge units placement calls admittedInstr) (outcome : Outcome)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (preceding instructions : List Mir.Instr)
    (layout : block.instrs.toList = preceding ++ instructions)
    (admitted : ∀ instruction ∈ instructions, admittedInstr instruction)
    (frame : Lir.Frame Nat) (memory : Lir.Memory) (count : Nat)
    (run : Run units placement outcome count ⟨function, label, preceding.length, frame, [], memory⟩) :
    ∃ finalFrame finalMemory remaining, remaining ≤ count ∧
      InstructionsExec calls instructions frame memory finalFrame finalMemory ∧
      Run units placement outcome remaining ⟨function, label, block.instrs.size, finalFrame, [], finalMemory⟩ := by
  induction instructions generalizing preceding frame memory count with
  | nil =>
    have size : block.instrs.size = preceding.length := by
      simpa only [List.append_nil, Array.length_toList] using congrArg List.length layout
    exact ⟨frame, memory, count, Nat.le_refl _, .nil, size ▸ run⟩
  | cons instruction rest ih =>
    show ∃ finalFrame finalMemory remaining, remaining ≤ count ∧
      InstructionsExec calls (instruction :: rest) frame memory finalFrame finalMemory ∧
      Run units placement outcome remaining ⟨function, label, block.instrs.size, finalFrame, [], finalMemory⟩
    have headAdmitted : admittedInstr instruction := admitted instruction (by simp)
    have atIndex : block.instrs[preceding.length]? = some instruction := by
      rw [← Array.getElem?_toList, layout, List.getElem?_append_right (Nat.le_refl _)]
      simp
    obtain ⟨middle, middleMemory, afterFirst, size, first, later⟩ :=
      instruction_run bridge outcome function label preceding.length block instruction found atIndex headAdmitted frame memory count run
    have restLayout : block.instrs.toList = (preceding ++ [instruction]) ++ rest := by
      simpa only [List.append_assoc, List.singleton_append] using layout
    have laterRun : Run units placement outcome afterFirst
        ⟨function, label, (preceding ++ [instruction]).length, middle, [], middleMemory⟩ := by
      simpa only [List.length_append, List.length_singleton] using later
    obtain ⟨finalFrame, finalMemory, remaining, bounded, executed, terminal⟩ :=
      ih (preceding ++ [instruction]) restLayout (fun i h => admitted i (by simp [h])) middle middleMemory afterFirst laterRun
    exact ⟨finalFrame, finalMemory, remaining, by omega, .cons first executed, terminal⟩

end Silmaril.Compiler.Native.Optimize.Validation.Machine.Instructions
