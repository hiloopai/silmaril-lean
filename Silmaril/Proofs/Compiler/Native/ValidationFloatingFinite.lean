module

public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Finite.Defs
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.Validation.Floating.Finite
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract
open Relation
open Validation.Finite Validation.Machine

theorem fop_step (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label index : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (op : Lir.FOp) (dest left right : Nat)
    (selected : block.instrs[index]? = some (.fop op dest left right))
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory : Lir.Memory)
    (executed : Lir.FOp.exec op dest left right frame = some finalFrame) :
    MirSem.Step units placement ⟨function, label, index, frame, stack, memory⟩
      ⟨function, label, index + 1, finalFrame, stack, memory⟩ := by
  simp only [MirSem.Step, MirSem.step, found, selected, executed]

/-- Actual finite successful raw execution requires both floating operands.
It yields the genuine next state with unchanged concrete memory. -/
theorem fop_run (units : Array Mir.Unit) (placement : MirSem.Placement) (outcome : Outcome)
    (function : Mir.Func) (label index : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (op : Lir.FOp) (dest left right : Nat)
    (selected : block.instrs[index]? = some (.fop op dest left right))
    (frame : Lir.Frame Nat) (memory : Lir.Memory) (count : Nat)
    (run : Run units placement outcome count ⟨function, label, index, frame, [], memory⟩) :
    ∃ finalFrame remaining, count = remaining + 1 ∧
      Lir.FOp.exec op dest left right frame = some finalFrame ∧
      Run units placement outcome remaining ⟨function, label, index + 1, finalFrame, [], memory⟩ := by
  cases actual : Lir.FOp.exec op dest left right frame with
  | none =>
    have stuck := run_not_stuck run
    simp only [MirSem.step, found, selected, actual] at stuck
    exact False.elim (stuck rfl)
  | some finalFrame =>
    have step : MirSem.step units placement ⟨function, label, index, frame, [], memory⟩ =
        .running ⟨function, label, index + 1, finalFrame, [], memory⟩ := by
      simp only [MirSem.step, found, selected, actual]
    obtain ⟨remaining, size, rest⟩ := run_running run step
    exact ⟨finalFrame, remaining, size, rfl, rest⟩

theorem instructions_steps (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (preceding instructions : List Mir.Instr)
    (layout : block.instrs.toList = preceding ++ instructions)
    (admitted : Floating.Admitted instructions)
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
    have headAdmitted : Floating.AdmittedInstr instruction := admitted instruction (by simp)
    have atIndex : block.instrs[preceding.length]? = some instruction := by
      rw [← Array.getElem?_toList, layout, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have firstStep : MirSem.Step units placement ⟨function, label, preceding.length, frame, stack, memory⟩
        ⟨function, label, preceding.length + 1, middle, stack, middleMemory⟩ := by
      cases instruction with
      | op op =>
        cases first with
        | op actual => exact op_step units placement function label preceding.length block found op atIndex frame middle stack memory middleMemory actual
      | fop op dest left right =>
        cases first with
        | fop actual =>
          exact fop_step units placement function label preceding.length block found op dest left right atIndex
            frame middle stack memory actual
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

theorem block_steps (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : Floating.Admitted block.instrs.toList)
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
    (found : function.blocks[label]? = some block) (admitted : Floating.Admitted block.instrs.toList)
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : BlockExec calls block frame memory (.jump next) finalFrame finalMemory) :
    ReflTransGen (MirSem.Step units placement) ⟨function, label, 0, frame, stack, memory⟩
      ⟨function, next, 0, finalFrame, stack, finalMemory⟩ := by
  obtain ⟨body, terminal⟩ := block_steps calls units placement function label block found admitted
    frame finalFrame stack memory finalMemory (.jump next) executed
  exact body.tail terminal

theorem returned_behaves (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : Floating.Admitted block.instrs.toList)
    (frame finalFrame : Lir.Frame Nat) (memory finalMemory : Lir.Memory) (words : List Lir.Word)
    (executed : BlockExec calls block frame memory (.returned words) finalFrame finalMemory) :
    MirSem.Behaves units placement ⟨function, label, 0, frame, [], memory⟩ (.returned words finalMemory) := by
  obtain ⟨body, terminal⟩ := block_steps calls units placement function label block found admitted
    frame finalFrame [] memory finalMemory (.returned words) executed
  exact ⟨_, body, terminal⟩

theorem trapped_behaves (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (admitted : Floating.Admitted block.instrs.toList)
    (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : BlockExec calls block frame memory .trapped finalFrame finalMemory) :
    MirSem.Behaves units placement ⟨function, label, 0, frame, stack, memory⟩ (.trapped finalMemory) := by
  obtain ⟨body, terminal⟩ := block_steps calls units placement function label block found admitted
    frame finalFrame stack memory finalMemory .trapped executed
  exact ⟨_, body, terminal⟩

theorem instructions_run (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement) (outcome : Outcome)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (preceding instructions : List Mir.Instr)
    (layout : block.instrs.toList = preceding ++ instructions)
    (admitted : Floating.Admitted instructions) (frame : Lir.Frame Nat) (memory : Lir.Memory) (count : Nat)
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
    have headAdmitted : Floating.AdmittedInstr instruction := admitted instruction (by simp)
    have atIndex : block.instrs[preceding.length]? = some instruction := by
      rw [← Array.getElem?_toList, layout, List.getElem?_append_right (Nat.le_refl _)]
      simp
    cases instruction with
    | op op =>
      show ∃ finalFrame finalMemory remaining, remaining ≤ count ∧
        InstructionsExec calls (Mir.Instr.op op :: rest) frame memory finalFrame finalMemory ∧
        Run units placement outcome remaining ⟨function, label, block.instrs.size, finalFrame, [], finalMemory⟩
      obtain ⟨middle, middleMemory, afterFirst, size, first, later⟩ :=
        op_run units placement outcome function label preceding.length block found op atIndex frame memory count run
      have restLayout : block.instrs.toList = (preceding ++ [Mir.Instr.op op]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append] using layout
      have laterRun : Run units placement outcome afterFirst
          ⟨function, label, (preceding ++ [Mir.Instr.op op]).length, middle, [], middleMemory⟩ := by
        simpa only [List.length_append, List.length_singleton] using later
      obtain ⟨finalFrame, finalMemory, remaining, bounded, executed, terminal⟩ :=
        ih (preceding ++ [Mir.Instr.op op]) restLayout (fun i h => admitted i (by simp [h])) middle middleMemory afterFirst laterRun
      exact ⟨finalFrame, finalMemory, remaining, by omega, .cons (.op first) executed, terminal⟩
    | fop op dest left right =>
      show ∃ finalFrame finalMemory remaining, remaining ≤ count ∧
        InstructionsExec calls (Mir.Instr.fop op dest left right :: rest) frame memory finalFrame finalMemory ∧
        Run units placement outcome remaining ⟨function, label, block.instrs.size, finalFrame, [], finalMemory⟩
      obtain ⟨middle, afterFirst, size, first, later⟩ := fop_run units placement outcome function label preceding.length
        block found op dest left right atIndex frame memory count run
      have restLayout : block.instrs.toList = (preceding ++ [Mir.Instr.fop op dest left right]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append] using layout
      have laterRun : Run units placement outcome afterFirst
          ⟨function, label, (preceding ++ [Mir.Instr.fop op dest left right]).length, middle, [], memory⟩ := by
        simpa only [List.length_append, List.length_singleton] using later
      obtain ⟨finalFrame, finalMemory, remaining, bounded, executed, terminal⟩ :=
        ih (preceding ++ [Mir.Instr.fop op dest left right]) restLayout (fun i h => admitted i (by simp [h])) middle memory afterFirst laterRun
      exact ⟨finalFrame, finalMemory, remaining, by omega, .cons (.fop first) executed, terminal⟩
    | addr dest symbol offset => cases headAdmitted
    | call symbol args results => cases headAdmitted
    | callIndirect reg args results => cases headAdmitted

theorem versionFunc_run (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (function : Mir.Func) (admitted : AdmittedFunction function) (outcome : Outcome)
    (count label : Nat) (sourceInput candidateInput : Lir.Frame Nat) (memory : Lir.Memory)
    (agrees : PureSoundness.FrameAgrees (freshBase function) sourceInput candidateInput)
    (run : Run units placement outcome count ⟨function, label, 0, sourceInput, [], memory⟩) :
    MirSem.Behaves (versionUnits cfg units) placement
      ⟨versionFunc cfg function, label, 0, candidateInput, [], memory⟩ outcome.behavior := by
  induction count using Nat.strong_induction_on generalizing label sourceInput candidateInput memory with
  | ind count ih =>
    show MirSem.Behaves (versionUnits cfg units) placement
      ⟨versionFunc cfg function, label, 0, candidateInput, [], memory⟩ outcome.behavior
    cases sourceFound : function.blocks[label]? with
    | none =>
      have stuck := run_not_stuck run
      simp only [MirSem.step, sourceFound] at stuck
      exact False.elim (stuck rfl)
    | some source =>
      show MirSem.Behaves (versionUnits cfg units) placement
        ⟨versionFunc cfg function, label, 0, candidateInput, [], memory⟩ outcome.behavior
      have sourceAdmitted : Floating.Admitted source.instrs.toList :=
        admitted source (Machine.source_member_of_lookup sourceFound)
      obtain ⟨sourceFinal, finalMemory, remaining, bounded, body, atTerm⟩ :=
        instructions_run calls units placement outcome function label source sourceFound [] source.instrs.toList rfl
          sourceAdmitted sourceInput memory count run
      obtain ⟨exit, term, continuation⟩ :=
        term_run units placement outcome function label source sourceFound sourceFinal finalMemory remaining atTerm
      have sourceExecuted : BlockExec calls source sourceInput memory exit sourceFinal finalMemory := ⟨body, term⟩
      obtain ⟨candidate, candidateFinal, candidateFound, candidateExecuted, finalAgree⟩ :=
        Floating.Caller.versionFunc_block_contextual sourceFound sourceAdmitted cfg calls sourceInput candidateInput
          sourceFinal agrees memory finalMemory exit sourceExecuted
      have candidateEqual : candidate = roundTripBlock cfg (freshBase function) source :=
        Option.some.inj (candidateFound.symm.trans (LambdaSSA.ContextualSoundness.versionFunc_block sourceFound cfg))
      have candidateAdmitted : Floating.Admitted candidate.instrs.toList := by
        rw [candidateEqual]
        exact Floating.Caller.roundTripBlock_admitted cfg (freshBase function) source sourceAdmitted
      cases exit with
      | jump next =>
        obtain ⟨afterJump, decreased, rest⟩ := continuation
        have later := ih afterJump (by omega) next sourceFinal candidateFinal finalMemory finalAgree rest
        have steps := jump_steps calls (versionUnits cfg units) placement (versionFunc cfg function) label next candidate
          candidateFound candidateAdmitted candidateInput candidateFinal [] memory finalMemory candidateExecuted
        exact behaves_prepend steps later
      | returned words =>
        rw [continuation]
        exact returned_behaves calls (versionUnits cfg units) placement (versionFunc cfg function) label candidate
          candidateFound candidateAdmitted candidateInput candidateFinal memory finalMemory words candidateExecuted
      | trapped =>
        rw [continuation]
        exact trapped_behaves calls (versionUnits cfg units) placement (versionFunc cfg function) label candidate
          candidateFound candidateAdmitted candidateInput candidateFinal [] memory finalMemory candidateExecuted

theorem versionFunc_behaves (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (function : Mir.Func) (admitted : AdmittedFunction function) (outcome : Outcome)
    (label : Nat) (sourceInput candidateInput : Lir.Frame Nat) (memory : Lir.Memory)
    (agrees : PureSoundness.FrameAgrees (freshBase function) sourceInput candidateInput)
    (source : MirSem.Behaves units placement ⟨function, label, 0, sourceInput, [], memory⟩ outcome.behavior) :
    MirSem.Behaves (versionUnits cfg units) placement
      ⟨versionFunc cfg function, label, 0, candidateInput, [], memory⟩ outcome.behavior := by
  have actual : ∃ count, Run units placement outcome count ⟨function, label, 0, sourceInput, [], memory⟩ := by
    cases outcome with
    | returned words finalMemory =>
      obtain ⟨terminal, steps, done⟩ := source
      exact run_of_steps steps done
    | trapped finalMemory =>
      obtain ⟨terminal, steps, done⟩ := source
      exact run_of_steps steps done
  obtain ⟨count, run⟩ := actual
  exact versionFunc_run calls units placement cfg function admitted outcome count label sourceInput candidateInput memory agrees run

theorem related_behaves (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (function : Mir.Func) (admitted : AdmittedFunction function) (outcome : Outcome)
    (sourceState candidateState : MirSem.State) (related : BoundaryRelated cfg function sourceState candidateState)
    (source : MirSem.Behaves units placement sourceState outcome.behavior) :
    MirSem.Behaves (versionUnits cfg units) placement candidateState outcome.behavior := by
  obtain ⟨label, sourceFrame, candidateFrame, memory, rfl, rfl, agrees⟩ := related
  exact versionFunc_behaves calls units placement cfg function admitted outcome label sourceFrame candidateFrame memory agrees source

theorem program_behaves (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (size : Nat) (function : Mir.Func) (frame : Lir.Frame Nat)
    (admitted : AdmittedFunction function) (outcome : Outcome)
    (started : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩)
    (source : MirSem.Behaves units placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩ outcome.behavior) :
    ∃ candidateState, MirSem.start (versionUnits cfg units) placement size = some candidateState ∧
      MirSem.Behaves (versionUnits cfg units) placement candidateState outcome.behavior := by
  exact ⟨_, start_versionUnits cfg units placement size function frame started,
    versionFunc_behaves calls units placement cfg function admitted outcome 0 frame frame
      (MirSem.initMem units placement size) (Context.agrees_refl _ _) source⟩

/-- The exact existing compiler with cleanup disabled retains its localSSA
flag; no candidate trace or block/check premise is supplied. -/
theorem optimizeWith_program_behaves (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (constantPropagation : cfg.constantPropagation = false)
    (commonSubexpressions : cfg.commonSubexpressions = false) (deadCode : cfg.deadCode = false)
    (jumpThreading : cfg.jumpThreading = false) (size : Nat) (function : Mir.Func) (frame : Lir.Frame Nat)
    (admitted : AdmittedFunction function) (outcome : Outcome)
    (started : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩)
    (source : MirSem.Behaves units placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩ outcome.behavior) :
    ∃ candidateState, MirSem.start (optimizeWith cfg units) placement size = some candidateState ∧
      MirSem.Behaves (optimizeWith cfg units) placement candidateState outcome.behavior := by
  cases enabled : cfg.localSSA with
  | false =>
    rw [optimizeWith_identity cfg units enabled constantPropagation commonSubexpressions deadCode jumpThreading]
    exact ⟨_, started, source⟩
  | true =>
    rw [optimizeWith_versionUnits cfg units enabled constantPropagation commonSubexpressions deadCode jumpThreading]
    exact program_behaves calls units placement cfg size function frame admitted outcome started source

theorem optimizeWith_program (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (size : Nat) (function : Mir.Func) (frame : Lir.Frame Nat)
    (admitted : AdmittedFunction function) (outcome : Outcome)
    (started : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩)
    (source : MirSem.Behaves units placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩ outcome.behavior) :
    Cleanup.ProgramBehaves (optimizeWith cfg units) placement size outcome.behavior := by
  have before : Cleanup.ProgramBehaves
      (if cfg.localSSA then versionUnits cfg units else units) placement size outcome.behavior := by
    cases enabled : cfg.localSSA with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, started, source⟩
    | true =>
      simp only [↓reduceIte]
      exact program_behaves calls units placement cfg size function frame admitted outcome started source
  have nonstuck : outcome.behavior ≠ .stuck := by
    cases outcome <;> simp [Outcome.behavior]
  exact Cleanup.cleanup_preserves cfg _ placement size outcome.behavior nonstuck before

/-- The actual default optimizer uses all four cleanup passes and both local
SSA stages; no disabled-pass premise is required. -/
theorem optimize_program (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (size : Nat) (function : Mir.Func) (frame : Lir.Frame Nat)
    (admitted : AdmittedFunction function) (outcome : Outcome)
    (started : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩)
    (source : MirSem.Behaves units placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩ outcome.behavior) :
    Cleanup.ProgramBehaves (optimize units) placement size outcome.behavior :=
  optimizeWith_program calls units placement {} size function frame admitted outcome started source

end Silmaril.Compiler.Native.Optimize.Validation.Floating.Finite
