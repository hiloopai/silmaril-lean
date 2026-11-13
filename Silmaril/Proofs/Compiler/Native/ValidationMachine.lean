module

public import Silmaril.Compiler.Native.Optimize.Validation.Machine.Defs
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Machine
open Silmaril.Machine Silmaril.Compile
open Relation
open Silmaril.Compile.Contract

theorem op_step (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label index : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (op : Lir.Op Nat)
    (selected : block.instrs[index]? = some (.op op))
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : op.exec frame memory = some (finalFrame, finalMemory)) :
    MirSem.Step units placement ⟨function, label, index, frame, stack, memory⟩
      ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩ := by
  simp only [MirSem.Step, MirSem.step, found, selected, executed]

/-- Actual pure list execution gives actual Mir instruction steps from any
list preceding position, preserving the real function, label and call stack. -/
theorem instructions_steps (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (preceding instructions : List Mir.Instr)
    (layout : block.instrs.toList = preceding ++ instructions)
    (admitted : Lists.Admitted instructions)
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
    have headAdmitted : Lists.AdmittedInstr instruction := admitted instruction (by simp)
    have atIndex : block.instrs[preceding.length]? = some instruction := by
      rw [← Array.getElem?_toList, layout, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have firstStep : MirSem.Step units placement ⟨function, label, preceding.length, frame, stack, memory⟩
        ⟨function, label, preceding.length + 1, middle, stack, middleMemory⟩ := by
      cases instruction with
      | op op =>
        cases first with
        | op actual => exact op_step units placement function label preceding.length block found op atIndex frame middle stack memory middleMemory actual
      | fop op dest left right => cases headAdmitted
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect reg args results => cases headAdmitted
    have restLayout : block.instrs.toList = (preceding ++ [instruction]) ++ rest := by
      simpa only [List.append_assoc, List.singleton_append] using layout
    have tailSteps : ReflTransGen (MirSem.Step units placement)
        ⟨function, label, (preceding ++ [instruction]).length, middle, stack, middleMemory⟩
        ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩ :=
      ih (preceding ++ [instruction]) restLayout (fun i h => admitted i (by simp [h]))
    exact ReflTransGen.head firstStep (by simpa only [List.length_append, List.length_singleton] using tailSteps)

theorem termOut_of_exec (term : Lir.Term Nat) (frame : Lir.Frame Nat) (exit : BlockExit)
    (executed : TermExec term frame exit) : Mir.FuncPass.termOut frame term = termOut exit := by
  cases executed with
  | jump => rfl
  | zero read => simp only [Mir.FuncPass.termOut, read, termOut, ↓reduceIte]
  | nonzero read nonzero => simp only [Mir.FuncPass.termOut, read, termOut, ite_eq_right nonzero]
  | ret read => simp only [Mir.FuncPass.termOut, read, termOut]
  | trap => rfl

/-- Connect real local block execution to the independent actual Mir machine.
The instruction path is finite; its final terminator result retains the exact
caller continuation, including a possible failed caller result write. -/
theorem block_steps (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : Lists.Admitted block.instrs.toList)
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block frame memory exit finalFrame finalMemory) :
    ReflTransGen (MirSem.Step units placement) ⟨function, label, 0, frame, stack, memory⟩
      ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩ ∧
    MirSem.step units placement ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩ =
      finish ⟨function, label, block.instrs.size, finalFrame, stack, finalMemory⟩ exit := by
  have body := instructions_steps calls units placement function label block found [] block.instrs.toList rfl
    admitted frame finalFrame stack memory finalMemory executed.1
  refine ⟨body, ?_⟩
  rw [Mir.FuncPass.step_term units placement _ block found rfl, termOut_of_exec block.term finalFrame exit executed.2]
  cases exit with
  | jump label => rfl
  | returned words => rfl
  | trapped => rfl

theorem jump_steps (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label next : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : Lists.Admitted block.instrs.toList)
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : BlockExec calls block frame memory (.jump next) finalFrame finalMemory) :
    ReflTransGen (MirSem.Step units placement) ⟨function, label, 0, frame, stack, memory⟩
      ⟨function, next, 0, finalFrame, stack, finalMemory⟩ := by
  obtain ⟨body, terminal⟩ := block_steps calls units placement function label block found admitted
    frame finalFrame stack memory finalMemory (.jump next) executed
  exact body.tail terminal

theorem returned_behaves (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : Lists.Admitted block.instrs.toList)
    (frame finalFrame : Lir.Frame Nat) (memory finalMemory : Lir.Memory) (words : List Lir.Word)
    (executed : BlockExec calls block frame memory (.returned words) finalFrame finalMemory) :
    MirSem.Behaves units placement ⟨function, label, 0, frame, [], memory⟩ (.returned words finalMemory) := by
  obtain ⟨body, terminal⟩ := block_steps calls units placement function label block found admitted
    frame finalFrame [] memory finalMemory (.returned words) executed
  exact ⟨_, body, terminal⟩

theorem trapped_behaves (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : Lists.Admitted block.instrs.toList)
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : BlockExec calls block frame memory .trapped finalFrame finalMemory) :
    MirSem.Behaves units placement ⟨function, label, 0, frame, stack, memory⟩ (.trapped finalMemory) := by
  obtain ⟨body, terminal⟩ := block_steps calls units placement function label block found admitted
    frame finalFrame stack memory finalMemory .trapped executed
  exact ⟨_, body, terminal⟩


theorem source_member_of_lookup {function : Mir.Func} {label : Nat} {block : Mir.Block}
    (found : function.blocks[label]? = some block) : block ∈ function.blocks.toList := by
  obtain ⟨bounded, equal⟩ := Array.getElem?_eq_some_iff.mp found
  exact equal ▸ Array.getElem_mem_toList bounded

/-- Checked contextual execution gives a real finite path in the actual
candidate function, with no candidate concrete execution premise. -/
theorem checked_block_steps (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (sourceFunction candidateFunction : Mir.Func) (label : Nat) (source candidate : Mir.Block)
    (sourceFound : sourceFunction.blocks[label]? = some source)
    (candidateFound : candidateFunction.blocks[label]? = some candidate)
    (sourceAdmitted : Lists.Admitted source.instrs.toList)
    (candidateAdmitted : Lists.Admitted candidate.instrs.toList)
    (accepted : check (freshBase sourceFunction) source candidate = true)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : PureSoundness.FrameAgrees (freshBase sourceFunction) sourceInput candidateInput)
    (stack : List MirSem.Act) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal,
      PureSoundness.FrameAgrees (freshBase sourceFunction) sourceFinal candidateFinal ∧
      ReflTransGen (MirSem.Step units placement) ⟨candidateFunction, label, 0, candidateInput, stack, memory⟩
        ⟨candidateFunction, label, candidate.instrs.size, candidateFinal, stack, finalMemory⟩ ∧
      MirSem.step units placement ⟨candidateFunction, label, candidate.instrs.size, candidateFinal, stack, finalMemory⟩ =
        finish ⟨candidateFunction, label, candidate.instrs.size, candidateFinal, stack, finalMemory⟩ exit := by
  obtain ⟨candidateFinal, candidateExecuted, finalAgree⟩ := Context.function_checked_contextual
    (source_member_of_lookup sourceFound) sourceAdmitted candidateAdmitted accepted calls sourceInput candidateInput
      sourceFinal agrees memory finalMemory exit executed
  obtain ⟨body, terminal⟩ := block_steps calls units placement candidateFunction label candidate candidateFound
    candidateAdmitted candidateInput candidateFinal stack memory finalMemory exit candidateExecuted
  exact ⟨candidateFinal, finalAgree, body, terminal⟩

theorem checked_jump_steps (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (sourceFunction candidateFunction : Mir.Func) (label next : Nat) (source candidate : Mir.Block)
    (sourceFound : sourceFunction.blocks[label]? = some source)
    (candidateFound : candidateFunction.blocks[label]? = some candidate)
    (sourceAdmitted : Lists.Admitted source.instrs.toList)
    (candidateAdmitted : Lists.Admitted candidate.instrs.toList)
    (accepted : check (freshBase sourceFunction) source candidate = true)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : PureSoundness.FrameAgrees (freshBase sourceFunction) sourceInput candidateInput)
    (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : BlockExec calls source sourceInput memory (.jump next) sourceFinal finalMemory) :
    ∃ candidateFinal, PureSoundness.FrameAgrees (freshBase sourceFunction) sourceFinal candidateFinal ∧
      ReflTransGen (MirSem.Step units placement) ⟨candidateFunction, label, 0, candidateInput, stack, memory⟩
        ⟨candidateFunction, next, 0, candidateFinal, stack, finalMemory⟩ := by
  obtain ⟨candidateFinal, finalAgree, body, terminal⟩ := checked_block_steps calls units placement sourceFunction candidateFunction
    label source candidate sourceFound candidateFound sourceAdmitted candidateAdmitted accepted sourceInput candidateInput sourceFinal
    agrees stack memory finalMemory (.jump next) executed
  exact ⟨candidateFinal, finalAgree, body.tail terminal⟩

theorem checked_returned_behaves (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (sourceFunction candidateFunction : Mir.Func) (label : Nat) (source candidate : Mir.Block)
    (sourceFound : sourceFunction.blocks[label]? = some source)
    (candidateFound : candidateFunction.blocks[label]? = some candidate)
    (sourceAdmitted : Lists.Admitted source.instrs.toList)
    (candidateAdmitted : Lists.Admitted candidate.instrs.toList)
    (accepted : check (freshBase sourceFunction) source candidate = true)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : PureSoundness.FrameAgrees (freshBase sourceFunction) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (words : List Lir.Word)
    (executed : BlockExec calls source sourceInput memory (.returned words) sourceFinal finalMemory) :
    MirSem.Behaves units placement ⟨candidateFunction, label, 0, candidateInput, [], memory⟩ (.returned words finalMemory) := by
  obtain ⟨candidateFinal, finalAgree, body, terminal⟩ := checked_block_steps calls units placement sourceFunction candidateFunction
    label source candidate sourceFound candidateFound sourceAdmitted candidateAdmitted accepted sourceInput candidateInput sourceFinal
    agrees [] memory finalMemory (.returned words) executed
  exact ⟨_, body, terminal⟩

end Silmaril.Compiler.Native.Optimize.Validation.Machine
