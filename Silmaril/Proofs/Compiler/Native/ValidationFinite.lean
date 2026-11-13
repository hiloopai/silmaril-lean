module

public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Machine.Thms
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ContextualSoundness.Thms
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Finite
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract
open Relation

private theorem result_ne_running (outcome : Outcome) (state : MirSem.State) :
    outcome.result ≠ .running state := by cases outcome <;> simp [Outcome.result]

private theorem result_ne_stuck (outcome : Outcome) : outcome.result ≠ .stuck := by
  cases outcome <;> simp [Outcome.result]

private theorem result_injective {first second : Outcome} (equal : first.result = second.result) : first = second := by
  cases first <;> cases second <;> simp_all [Outcome.result]

theorem run_not_stuck {units : Array Mir.Unit} {placement : MirSem.Placement} {outcome : Outcome}
    {count : Nat} {state : MirSem.State} (run : Run units placement outcome count state) :
    MirSem.step units placement state ≠ .stuck := by
  cases run with
  | done terminal => rw [terminal]; exact result_ne_stuck _
  | next step rest => rw [step]; simp

theorem run_running {units : Array Mir.Unit} {placement : MirSem.Placement} {outcome : Outcome}
    {count : Nat} {state later : MirSem.State} (run : Run units placement outcome count state)
    (actual : MirSem.step units placement state = .running later) :
    ∃ remaining, count = remaining + 1 ∧ Run units placement outcome remaining later := by
  cases run with
  | done terminal => exact False.elim (result_ne_running _ _ (terminal.symm.trans actual))
  | @next remaining state nextState step rest =>
    have equal : nextState = later := MirSem.Result.running.inj (step.symm.trans actual)
    exact ⟨remaining, rfl, equal ▸ rest⟩

theorem run_terminal {units : Array Mir.Unit} {placement : MirSem.Placement} {outcome terminal : Outcome}
    {count : Nat} {state : MirSem.State} (run : Run units placement outcome count state)
    (actual : MirSem.step units placement state = terminal.result) : outcome = terminal := by
  cases run with
  | done equal => exact result_injective (equal.symm.trans actual)
  | next step rest => exact False.elim (result_ne_running _ _ (actual.symm.trans step))

theorem run_of_steps {units : Array Mir.Unit} {placement : MirSem.Placement} {outcome : Outcome}
    {state finalState : MirSem.State} (steps : ReflTransGen (MirSem.Step units placement) state finalState)
    (terminal : MirSem.step units placement finalState = outcome.result) :
    ∃ count, Run units placement outcome count state := by
  induction steps using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .done terminal⟩
  | @head middle later step rest ih =>
    obtain ⟨count, run⟩ := ih
    exact ⟨count + 1, .next step run⟩

theorem op_run (units : Array Mir.Unit) (placement : MirSem.Placement) (outcome : Outcome)
    (function : Mir.Func) (label index : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (op : Lir.Op Nat)
    (selected : block.instrs[index]? = some (.op op))
    (frame : Lir.Frame Nat) (memory : Lir.Memory) (count : Nat)
    (run : Run units placement outcome count ⟨function, label, index, frame, [], memory⟩) :
    ∃ finalFrame finalMemory remaining, count = remaining + 1 ∧
      op.exec frame memory = some (finalFrame, finalMemory) ∧
      Run units placement outcome remaining ⟨function, label, index + 1, finalFrame, [], finalMemory⟩ := by
  cases actual : op.exec frame memory with
  | none =>
    have stuck := run_not_stuck run
    simp only [MirSem.step, found, selected, actual] at stuck
    exact False.elim (stuck rfl)
  | some pair =>
    obtain ⟨finalFrame, finalMemory⟩ := pair
    have step : MirSem.step units placement ⟨function, label, index, frame, [], memory⟩ =
        .running ⟨function, label, index + 1, finalFrame, [], finalMemory⟩ := by
      simp only [MirSem.step, found, selected, actual]
    obtain ⟨remaining, size, rest⟩ := run_running run step
    exact ⟨finalFrame, finalMemory, remaining, size, rfl, rest⟩

theorem instructions_run (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement) (outcome : Outcome)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (preceding instructions : List Mir.Instr)
    (layout : block.instrs.toList = preceding ++ instructions)
    (admitted : Lists.Admitted instructions) (frame : Lir.Frame Nat) (memory : Lir.Memory) (count : Nat)
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
    have headAdmitted : Lists.AdmittedInstr instruction := admitted instruction (by simp)
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
    | fop op dest left right => cases headAdmitted
    | addr dest symbol offset => cases headAdmitted
    | call symbol args results => cases headAdmitted
    | callIndirect reg args results => cases headAdmitted


theorem term_run (units : Array Mir.Unit) (placement : MirSem.Placement) (outcome : Outcome)
    (function : Mir.Func) (label : Nat) (block : Mir.Block)
    (found : function.blocks[label]? = some block) (frame : Lir.Frame Nat) (memory : Lir.Memory) (count : Nat)
    (run : Run units placement outcome count ⟨function, label, block.instrs.size, frame, [], memory⟩) :
    ∃ exit, TermExec block.term frame exit ∧
      match exit with
      | .jump next => ∃ remaining, remaining < count ∧
          Run units placement outcome remaining ⟨function, next, 0, frame, [], memory⟩
      | .returned words => outcome = .returned words memory
      | .trapped => outcome = .trapped memory := by
  have terminalStep : MirSem.step units placement ⟨function, label, block.instrs.size, frame, [], memory⟩ =
      match Mir.FuncPass.termOut frame block.term with
      | .goto next => .running ⟨function, next, 0, frame, [], memory⟩
      | .ret words => .returned words memory
      | .trap => .trapped memory
      | .stuck => .stuck := Mir.FuncPass.step_term units placement _ block found rfl
  have executed : ∃ exit, TermExec block.term frame exit := by
    cases term : block.term with
    | jump next => exact ⟨.jump next, term ▸ TermExec.jump⟩
    | branch reg yes no =>
      show ∃ exit, TermExec (.branch reg yes no) frame exit
      cases read : frame.get reg with
      | none =>
        have actualStuck : MirSem.step units placement ⟨function, label, block.instrs.size, frame, [], memory⟩ = .stuck := by
          rw [terminalStep]
          simp only [Mir.FuncPass.termOut, term, read]
        exact False.elim (run_not_stuck run actualStuck)
      | some value =>
        by_cases zero : value = 0
        · exact ⟨.jump no, term ▸ TermExec.zero (zero ▸ read)⟩
        · exact ⟨.jump yes, term ▸ TermExec.nonzero read zero⟩
    | ret locations =>
      cases read : frame.readAll locations with
      | none =>
        have actualStuck : MirSem.step units placement ⟨function, label, block.instrs.size, frame, [], memory⟩ = .stuck := by
          rw [terminalStep]
          simp only [Mir.FuncPass.termOut, term, read]
        exact False.elim (run_not_stuck run actualStuck)
      | some words => exact ⟨.returned words, term ▸ TermExec.ret read⟩
    | trap => exact ⟨.trapped, term ▸ TermExec.trap⟩
  obtain ⟨exit, localTerm⟩ := executed
  refine ⟨exit, localTerm, ?_⟩
  have exactTerminal : MirSem.step units placement ⟨function, label, block.instrs.size, frame, [], memory⟩ =
      Machine.finish ⟨function, label, block.instrs.size, frame, [], memory⟩ exit := by
    rw [terminalStep, Machine.termOut_of_exec block.term frame exit localTerm]
    cases exit <;> rfl
  cases exit with
  | jump next =>
    obtain ⟨remaining, size, rest⟩ := run_running run exactTerminal
    exact ⟨remaining, by omega, rest⟩
  | returned words => exact run_terminal run exactTerminal
  | trapped => exact run_terminal run exactTerminal


theorem roundTripBlock_admitted (cfg : Config) (base : Nat) (source : Mir.Block)
    (admitted : Lists.Admitted source.instrs.toList) :
    Lists.Admitted (roundTripBlock cfg base source).instrs.toList := by
  have fallback : Lists.Admitted
      (if (enter base source).isSSA && check base source (leave (enter base source))
        then leave (enter base source) else source).instrs.toList := by
    split
    · exact LambdaSSA.SelectedSoundness.leave_enter_admitted base source admitted
    · exact admitted
  cases enabled : cfg.lambdaSSA with
  | false => simpa only [roundTripBlock, enabled, Bool.false_eq_true, ↓reduceIte] using fallback
  | true =>
    cases selected : LambdaSSA.optimize? base source with
    | none => simpa only [roundTripBlock, enabled, ↓reduceIte, selected, Option.map_none, Option.getD_none] using fallback
    | some result =>
      obtain ⟨candidate, count⟩ := result
      rw [LambdaSSA.SelectedSoundness.roundTripBlock_selected cfg base source candidate count enabled selected]
      exact (LambdaSSA.OptimizerAdmission.optimize_admitted selected).2.1

theorem behaves_prepend {units : Array Mir.Unit} {placement : MirSem.Placement} {outcome : Outcome}
    {state later : MirSem.State} (steps : ReflTransGen (MirSem.Step units placement) state later)
    (rest : MirSem.Behaves units placement later outcome.behavior) :
    MirSem.Behaves units placement state outcome.behavior := by
  cases outcome with
  | returned words memory =>
    obtain ⟨terminal, tailSteps, done⟩ := rest
    exact ⟨terminal, steps.trans tailSteps, done⟩
  | trapped memory =>
    obtain ⟨terminal, tailSteps, done⟩ := rest
    exact ⟨terminal, steps.trans tailSteps, done⟩

/-- Every finite successful actual source machine trace through admitted
blocks gives actual behavior of the real indexed versionFunc, from its own
related partial input frame. Candidate machine execution is derived. -/
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
      have sourceAdmitted : Lists.Admitted source.instrs.toList :=
        admitted source (Machine.source_member_of_lookup sourceFound)
      obtain ⟨sourceFinal, finalMemory, remaining, bounded, body, atTerm⟩ :=
        instructions_run calls units placement outcome function label source sourceFound [] source.instrs.toList rfl
          sourceAdmitted sourceInput memory count run
      obtain ⟨exit, term, continuation⟩ :=
        term_run units placement outcome function label source sourceFound sourceFinal finalMemory remaining atTerm
      have sourceExecuted : BlockExec calls source sourceInput memory exit sourceFinal finalMemory := ⟨body, term⟩
      obtain ⟨candidate, candidateFinal, candidateFound, candidateExecuted, finalAgree⟩ :=
        LambdaSSA.ContextualSoundness.versionFunc_block_contextual sourceFound sourceAdmitted cfg calls sourceInput candidateInput
          sourceFinal agrees memory finalMemory exit sourceExecuted
      have candidateEqual : candidate = roundTripBlock cfg (freshBase function) source :=
        Option.some.inj (candidateFound.symm.trans (LambdaSSA.ContextualSoundness.versionFunc_block sourceFound cfg))
      have candidateAdmitted : Lists.Admitted candidate.instrs.toList := by
        rw [candidateEqual]
        exact roundTripBlock_admitted cfg (freshBase function) source sourceAdmitted
      cases exit with
      | jump next =>
        obtain ⟨afterJump, decreased, rest⟩ := continuation
        have later := ih afterJump (by omega) next sourceFinal candidateFinal finalMemory finalAgree rest
        have steps := Machine.jump_steps calls (versionUnits cfg units) placement (versionFunc cfg function) label next candidate
          candidateFound candidateAdmitted candidateInput candidateFinal [] memory finalMemory candidateExecuted
        exact behaves_prepend steps later
      | returned words =>
        rw [continuation]
        exact Machine.returned_behaves calls (versionUnits cfg units) placement (versionFunc cfg function) label candidate
          candidateFound candidateAdmitted candidateInput candidateFinal memory finalMemory words candidateExecuted
      | trapped =>
        rw [continuation]
        exact Machine.trapped_behaves calls (versionUnits cfg units) placement (versionFunc cfg function) label candidate
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


theorem strongNames_versionUnits (cfg : Config) (units : Array Mir.Unit) :
    MirSem.strongNames (versionUnits cfg units) = MirSem.strongNames units := by
  simp [MirSem.strongNames, versionUnits, versionFunc, List.flatMap_map, List.filter_map, List.map_map, Function.comp_def]

theorem funcDefs_versionUnits (cfg : Config) (units : Array Mir.Unit) :
    MirSem.funcDefs (versionUnits cfg units) = (MirSem.funcDefs units).map (versionFunc cfg) := by
  simp only [MirSem.funcDefs, strongNames_versionUnits]
  simp only [versionUnits, Array.toList_map, List.flatMap_map]
  rw [← List.map_flatMap, List.filter_map]
  rfl

theorem dataDefs_versionUnits (cfg : Config) (units : Array Mir.Unit) :
    MirSem.dataDefs (versionUnits cfg units) = MirSem.dataDefs units := by
  simp only [MirSem.dataDefs, strongNames_versionUnits]
  simp only [versionUnits, Array.toList_map, List.flatMap_map]

theorem funcOf_versionUnits (cfg : Config) (units : Array Mir.Unit) (name : String) :
    MirSem.funcOf (versionUnits cfg units) name = (MirSem.funcOf units name).map (versionFunc cfg) := by
  simp [MirSem.funcOf, funcDefs_versionUnits, List.find?_map, versionFunc, Function.comp_def]

theorem dataOf_versionUnits (cfg : Config) (units : Array Mir.Unit) (name : String) :
    MirSem.dataOf (versionUnits cfg units) name = MirSem.dataOf units name := by
  simp only [MirSem.dataOf, dataDefs_versionUnits]

theorem symValue_versionUnits (cfg : Config) (units : Array Mir.Unit) (placement : MirSem.Placement) (name : String) :
    MirSem.symValue (versionUnits cfg units) placement name = MirSem.symValue units placement name := by
  simp only [MirSem.symValue, dataOf_versionUnits, funcOf_versionUnits, Option.isSome_map]

theorem objectByte_versionUnits (cfg : Config) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (data : Mir.Data) (offset : Nat) :
    MirSem.objectByte (versionUnits cfg units) placement data offset = MirSem.objectByte units placement data offset := by
  simp only [MirSem.objectByte, symValue_versionUnits]

theorem initMem_versionUnits (cfg : Config) (units : Array Mir.Unit) (placement : MirSem.Placement) (size : Nat) :
    MirSem.initMem (versionUnits cfg units) placement size = MirSem.initMem units placement size := by
  simp only [MirSem.initMem, dataDefs_versionUnits, objectByte_versionUnits]

theorem enter_versionFunc (cfg : Config) (function : Mir.Func) (words : List Lir.Word) :
    MirSem.enter (versionFunc cfg function) words = MirSem.enter function words := rfl

/-- Actual source startup determines the exact actual transformed startup,
including weak/strong symbol selection, argument writes and relocation memory. -/
theorem start_versionUnits (cfg : Config) (units : Array Mir.Unit) (placement : MirSem.Placement) (size : Nat)
    (function : Mir.Func) (frame : Lir.Frame Nat)
    (source : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩) :
    MirSem.start (versionUnits cfg units) placement size = some
      ⟨versionFunc cfg function, 0, 0, frame, [], MirSem.initMem units placement size⟩ := by
  unfold MirSem.start at source ⊢
  rw [funcDefs_versionUnits, List.head?_map]
  cases found : (MirSem.funcDefs units).head? with
  | none => simp [found] at source
  | some actual =>
    simp only [found, Option.bind_some] at source
    cases entered : MirSem.enter actual [] with
    | none => simp [entered] at source
    | some actualFrame =>
      simp only [entered, Option.map_some, Option.some.injEq, MirSem.State.mk.injEq] at source
      obtain ⟨rfl, _, _, rfl, _, _⟩ := source
      simp only [Option.map_some, Option.bind_some, enter_versionFunc, entered, Option.map_some, initMem_versionUnits]

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


theorem optimizeWith_versionUnits (cfg : Config) (units : Array Mir.Unit)
    (localSSA : cfg.localSSA = true) (constantPropagation : cfg.constantPropagation = false)
    (commonSubexpressions : cfg.commonSubexpressions = false) (deadCode : cfg.deadCode = false)
    (jumpThreading : cfg.jumpThreading = false) :
    optimizeWith cfg units = versionUnits cfg units := by
  simp only [optimizeWith, localSSA, ↓reduceIte, cleanupPasses, constantPropagation,
    commonSubexpressions, deadCode, jumpThreading, Bool.false_eq_true, List.nil_append]
  rfl

theorem optimizeWith_identity (cfg : Config) (units : Array Mir.Unit)
    (localSSA : cfg.localSSA = false) (constantPropagation : cfg.constantPropagation = false)
    (commonSubexpressions : cfg.commonSubexpressions = false) (deadCode : cfg.deadCode = false)
    (jumpThreading : cfg.jumpThreading = false) : optimizeWith cfg units = units := by
  simp only [optimizeWith, localSSA, Bool.false_eq_true, ↓reduceIte, cleanupPasses, constantPropagation,
    commonSubexpressions, deadCode, jumpThreading, List.nil_append]
  rfl

end Silmaril.Compiler.Native.Optimize.Validation.Finite
