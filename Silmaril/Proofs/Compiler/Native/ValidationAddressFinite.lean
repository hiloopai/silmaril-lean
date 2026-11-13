module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Finite.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Finite
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract
open Relation Validation.Finite Validation.Machine

/-- New source-domain admission implies the existing address block interface.
The stronger pseudo-symbol boundary is independent of compiler acceptance. -/
theorem admitted_address (instructions : List Mir.Instr) (admitted : Admitted instructions) :
    Effects.Admitted instructions := by
  intro instruction member
  have accepted := admitted instruction member
  cases instruction with
  | op | fop => trivial
  | addr dest symbol offset => exact accepted.1
  | call | callIndirect => cases accepted

/-- The actual fixed-placement resolver is unchanged by local SSA. -/
theorem resolve_versionUnits (cfg : Config) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (symbol : String) (offset : Nat) :
    resolve (versionUnits cfg units) placement symbol offset = resolve units placement symbol offset := by
  simp only [resolve, symValue_versionUnits]

theorem calls_versionUnits (cfg : Config) (units : Array Mir.Unit) (placement : MirSem.Placement) :
    calls (versionUnits cfg units) placement = calls units placement := by
  have addresses : resolve (versionUnits cfg units) placement = resolve units placement := by
    funext symbol offset
    exact resolve_versionUnits cfg units placement symbol offset
  simp only [calls, addresses]

/-- An actual ordinary-address instruction execution reconstructs the real
next machine state, at arbitrary function, block and caller stack. -/
theorem instruction_step (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label index : Nat) (block : Mir.Block) (instruction : Mir.Instr)
    (found : function.blocks[label]? = some block) (selected : block.instrs[index]? = some instruction)
    (admitted : Effects.AdmittedInstr instruction) (frame finalFrame : Lir.Frame Nat)
    (stack : List MirSem.Act) (memory finalMemory : Lir.Memory)
    (executed : InstructionExec (calls units placement) instruction frame memory finalFrame finalMemory) :
    MirSem.Step units placement ⟨function, label, index, frame, stack, memory⟩
      ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩ := by
  show MirSem.Step units placement ⟨function, label, index, frame, stack, memory⟩
    ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩
  cases instruction with
  | op operation =>
    cases executed with
    | op actual => simp only [MirSem.Step, MirSem.step, found, selected, actual]
  | fop operation dest left right =>
    cases executed with
    | fop actual => simp only [MirSem.Step, MirSem.step, found, selected, actual]
  | addr dest symbol offset =>
    show MirSem.Step units placement ⟨function, label, index, frame, stack, memory⟩
      ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩
    have ordinary : symbol ≠ reservedFrame := admitted
    cases executed with
    | @addr _ _ _ _ _ value actual =>
      cases resolved : MirSem.symValue units placement symbol with
      | none => simp only [calls, resolve, ordinary, ↓reduceIte, resolved, Option.map_none] at actual; cases actual
      | some address =>
        have equal : BitVec.ofNat 64 (address + offset) = value := by
          simpa only [calls, resolve, ordinary, ↓reduceIte, resolved, Option.map_some, Option.some.injEq] using actual
        cases equal
        simp only [MirSem.Step, MirSem.step, found, selected, resolved]
  | call | callIndirect => cases admitted

/-- A nonstuck actual admitted instruction determines both its independent
execution and its entire straight-line next machine state. -/
theorem instruction_of_nonstuck (units : Array Mir.Unit) (placement : MirSem.Placement)
    (function : Mir.Func) (label index : Nat) (block : Mir.Block) (instruction : Mir.Instr)
    (found : function.blocks[label]? = some block) (selected : block.instrs[index]? = some instruction)
    (admitted : Effects.AdmittedInstr instruction) (frame : Lir.Frame Nat)
    (stack : List MirSem.Act) (memory : Lir.Memory)
    (nonstuck : MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ ≠ .stuck) :
    ∃ finalFrame finalMemory,
      InstructionExec (calls units placement) instruction frame memory finalFrame finalMemory ∧
      MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ =
        .running ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩ := by
  show ∃ finalFrame finalMemory,
    InstructionExec (calls units placement) instruction frame memory finalFrame finalMemory ∧
    MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ =
      .running ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩
  cases instruction with
  | op operation =>
    show ∃ finalFrame finalMemory,
      InstructionExec (calls units placement) (.op operation) frame memory finalFrame finalMemory ∧
      MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ =
        .running ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩
    cases actual : operation.exec frame memory with
    | none =>
      have impossible : MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ = .stuck := by
        simp only [MirSem.step, found, selected, actual]
      exact False.elim (nonstuck impossible)
    | some pair =>
      obtain ⟨finalFrame, finalMemory⟩ := pair
      exact ⟨finalFrame, finalMemory, .op actual, by simp only [MirSem.step, found, selected, actual]⟩
  | fop operation dest left right =>
    cases actual : Lir.FOp.exec operation dest left right frame with
    | none =>
      have impossible : MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ = .stuck := by
        simp only [MirSem.step, found, selected, actual]
      exact False.elim (nonstuck impossible)
    | some finalFrame =>
      exact ⟨finalFrame, memory, .fop actual, by simp only [MirSem.step, found, selected, actual]⟩
  | addr dest symbol offset =>
    show ∃ finalFrame finalMemory,
      InstructionExec (calls units placement) (.addr dest symbol offset) frame memory finalFrame finalMemory ∧
      MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ =
        .running ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩
    have ordinary : symbol ≠ reservedFrame := admitted
    cases actual : MirSem.symValue units placement symbol with
    | none =>
      have impossible : MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ = .stuck := by
        simp only [MirSem.step, found, selected, actual]
      exact False.elim (nonstuck impossible)
    | some address =>
      refine ⟨frame.set dest (BitVec.ofNat 64 (address + offset)), memory, .addr ?_, ?_⟩
      · simp only [calls, resolve, ordinary, ↓reduceIte, actual, Option.map_some]
      · simp only [MirSem.step, found, selected, actual]
  | call | callIndirect => cases admitted

/-- Concrete proved bridge for the actual unit/placement-based address resolver.
No arbitrary open-call interpretation appears in the CFG/compiler result. -/
theorem instructionBridge (units : Array Mir.Unit) (placement : MirSem.Placement) :
    Instructions.Bridge units placement (calls units placement) Effects.AdmittedInstr :=
  ⟨instruction_step units placement, instruction_of_nonstuck units placement⟩

theorem versionFunc_run (units : Array Mir.Unit) (placement : MirSem.Placement)
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
      have sourceAdmitted : Effects.Admitted source.instrs.toList :=
        admitted_address _ (admitted source (Machine.source_member_of_lookup sourceFound))
      obtain ⟨sourceFinal, finalMemory, remaining, bounded, body, atTerm⟩ :=
        Instructions.instructions_run (instructionBridge units placement) outcome function label source sourceFound [] source.instrs.toList rfl
          sourceAdmitted sourceInput memory count run
      obtain ⟨exit, term, continuation⟩ :=
        term_run units placement outcome function label source sourceFound sourceFinal finalMemory remaining atTerm
      have sourceExecuted : BlockExec (calls units placement) source sourceInput memory exit sourceFinal finalMemory := ⟨body, term⟩
      obtain ⟨candidate, candidateFinal, values, candidateFound, candidateExecuted, finalAgree, sourceRead, candidateRead⟩ :=
        Caller.versionFunc_block_contextual units placement sourceFound sourceAdmitted cfg sourceInput candidateInput
          sourceFinal agrees memory finalMemory exit sourceExecuted
      have candidateEqual : candidate = roundTripBlock cfg (freshBase function) source :=
        Option.some.inj (candidateFound.symm.trans (LambdaSSA.ContextualSoundness.versionFunc_block sourceFound cfg))
      have candidateAdmitted : Effects.Admitted candidate.instrs.toList := by
        rw [candidateEqual]
        exact Caller.roundTripBlock_admitted cfg (freshBase function) source sourceAdmitted
      have targetExecuted : BlockExec (calls (versionUnits cfg units) placement) candidate candidateInput memory
          exit candidateFinal finalMemory := by
        rw [calls_versionUnits]
        exact candidateExecuted
      cases exit with
      | jump next =>
        obtain ⟨afterJump, decreased, rest⟩ := continuation
        have later := ih afterJump (by omega) next sourceFinal candidateFinal finalMemory finalAgree rest
        have steps := Instructions.jump_steps (instructionBridge (versionUnits cfg units) placement) (versionFunc cfg function) label next candidate
          candidateFound candidateAdmitted candidateInput candidateFinal [] memory finalMemory targetExecuted
        exact behaves_prepend steps later
      | returned words =>
        rw [continuation]
        exact Instructions.returned_behaves (instructionBridge (versionUnits cfg units) placement) (versionFunc cfg function) label candidate
          candidateFound candidateAdmitted candidateInput candidateFinal memory finalMemory words targetExecuted
      | trapped =>
        rw [continuation]
        exact Instructions.trapped_behaves (instructionBridge (versionUnits cfg units) placement) (versionFunc cfg function) label candidate
          candidateFound candidateAdmitted candidateInput candidateFinal [] memory finalMemory targetExecuted

theorem versionFunc_behaves (units : Array Mir.Unit) (placement : MirSem.Placement)
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
  exact versionFunc_run units placement cfg function admitted outcome count label sourceInput candidateInput memory agrees run

theorem related_behaves (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (function : Mir.Func) (admitted : AdmittedFunction function) (outcome : Outcome)
    (sourceState candidateState : MirSem.State) (related : BoundaryRelated cfg function sourceState candidateState)
    (source : MirSem.Behaves units placement sourceState outcome.behavior) :
    MirSem.Behaves (versionUnits cfg units) placement candidateState outcome.behavior := by
  obtain ⟨label, sourceFrame, candidateFrame, memory, rfl, rfl, agrees⟩ := related
  exact versionFunc_behaves units placement cfg function admitted outcome label sourceFrame candidateFrame memory agrees source

theorem program_behaves (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (size : Nat) (function : Mir.Func) (frame : Lir.Frame Nat)
    (admitted : AdmittedFunction function) (outcome : Outcome)
    (started : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩)
    (source : MirSem.Behaves units placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩ outcome.behavior) :
    ∃ candidateState, MirSem.start (versionUnits cfg units) placement size = some candidateState ∧
      MirSem.Behaves (versionUnits cfg units) placement candidateState outcome.behavior := by
  exact ⟨_, start_versionUnits cfg units placement size function frame started,
    versionFunc_behaves units placement cfg function admitted outcome 0 frame frame
      (MirSem.initMem units placement size) (Context.agrees_refl _ _) source⟩

/-- The exact existing compiler with cleanup disabled retains its localSSA
flag; no candidate trace or block/check premise is supplied. -/
theorem optimizeWith_program_behaves (units : Array Mir.Unit) (placement : MirSem.Placement)
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
    exact program_behaves units placement cfg size function frame admitted outcome started source

theorem optimizeWith_program (units : Array Mir.Unit) (placement : MirSem.Placement)
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
      exact program_behaves units placement cfg size function frame admitted outcome started source
  have nonstuck : outcome.behavior ≠ .stuck := by
    cases outcome <;> simp [Outcome.behavior]
  exact Cleanup.cleanup_preserves cfg _ placement size outcome.behavior nonstuck before

/-- The actual default optimizer uses all four cleanup passes and both local
SSA stages; no disabled-pass premise is required. -/
theorem optimize_program (units : Array Mir.Unit) (placement : MirSem.Placement)
    (size : Nat) (function : Mir.Func) (frame : Lir.Frame Nat)
    (admitted : AdmittedFunction function) (outcome : Outcome)
    (started : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩)
    (source : MirSem.Behaves units placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩ outcome.behavior) :
    Cleanup.ProgramBehaves (optimize units) placement size outcome.behavior :=
  optimizeWith_program units placement {} size function frame admitted outcome started source

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Finite
