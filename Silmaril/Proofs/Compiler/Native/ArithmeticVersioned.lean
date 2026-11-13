module

public import Silmaril.Compiler.Native.Correctness.ArithmeticVersioned.Defs
public import Silmaril.Compiler.Native.Correctness.ArithmeticInstitution.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Caller.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.ArithmeticVersioned
open Silmaril.Compile Silmaril.Machine CategoryTheory
open Silmaril.Compiler.Core.SignedArithmetic
open Silmaril.Compiler.Native.Semantics Silmaril.Compiler.Native.Optimize
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

/-- The unsupported address is retained by the actual LambdaSSA fallback. -/
theorem prologue_lambda (base : Nat) : LambdaSSA.optimize? base AdditionLower.prologue = none := by
  cbv

theorem prologue_renamed (base : Nat) : leave (enter base AdditionLower.prologue) = versionedPrologue base := by
  cbv

/-- The exact caller retains the real validation/isSSA branch. -/
theorem prologue_round_trip (cfg : Config) (base : Nat) :
    roundTripBlock cfg base AdditionLower.prologue =
      if (enter base AdditionLower.prologue).isSSA &&
          Validation.check base AdditionLower.prologue (leave (enter base AdditionLower.prologue))
      then versionedPrologue base else AdditionLower.prologue := by
  simp only [roundTripBlock, prologue_lambda, Option.map_none, Option.getD_none, ite_self,
    prologue_renamed]

/-- Both real fallback outcomes derive execution and low-register/whole-slot
agreement, including arbitrary incoming partial frames. -/
theorem prologue_contextual (cfg : Config) (base : Nat) (summaries : OpenCalls)
    (source candidate : Lir.Frame Nat) (memory : Lir.Memory) (address : Lir.Word)
    (resolved : summaries.address "__ccomp_frame" 0 = some address)
    (agrees : Validation.PureSoundness.FrameAgrees base source candidate) :
    ∃ final, BlockExec summaries (roundTripBlock cfg base AdditionLower.prologue)
      candidate memory (.jump 1) final memory ∧
      Validation.PureSoundness.FrameAgrees base (source.set 0 address) final := by
  rw [prologue_round_trip]
  split
  · show ∃ final, BlockExec summaries (versionedPrologue base) candidate memory (.jump 1) final memory ∧
      Validation.PureSoundness.FrameAgrees base (source.set 0 address) final
    have fresh : Validation.PureSoundness.FrameAgrees base source (candidate.set base address) := by
      refine ⟨agrees.slots, ?_⟩
      intro register below
      have distinct : register ≠ base := by omega
      simpa only [Lir.Frame.get_set, distinct, ite_false] using agrees.registers register below
    exact ⟨(candidate.set base address).set 0 address,
      ⟨.cons (.addr resolved) (.cons (.op (by simp only [Lir.Op.exec, Lir.Frame.get_set, ite_true, Option.map_some])) .nil), .jump⟩,
      Validation.Context.agrees_set fresh 0 address⟩
  · exact ⟨candidate.set 0 address, AdditionLower.prologue_executed summaries candidate memory address resolved,
      Validation.Context.agrees_set agrees 0 address⟩

theorem prologue_call_free (cfg : Config) (base : Nat) :
    OpenFrame.BlockCallFree (roundTripBlock cfg base AdditionLower.prologue) := by
  rw [prologue_round_trip]
  split <;> simp [OpenFrame.BlockCallFree, OpenFrame.CallFree, versionedPrologue, AdditionLower.prologue]

/-- Every selected operation is admitted independently of its value bounds. -/
theorem plan_admitted (expression : Expression) (next : Nat) :
    Validation.Slots.Admitted (ArithmeticLower.plan expression next).instructions := by
  induction expression generalizing next with
  | literal number =>
    simp [ArithmeticLower.plan, Validation.Slots.Admitted, Validation.Slots.AdmittedInstr,
      Validation.Slots.AdmittedOp, Validation.Roots.Admitted]
  | binary operator left right first last =>
    show Validation.Slots.Admitted (ArithmeticLower.plan (.binary operator left right) next).instructions
    intro instruction member
    simp only [ArithmeticLower.plan, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (member | member) | rfl | rfl | rfl | rfl
    · exact first next instruction member
    · exact last (ArithmeticLower.plan left next).nextReg instruction member
    · trivial
    · trivial
    · cases operator <;> rfl
    · trivial

theorem body_admitted (expression : Expression) :
    Validation.Slots.Admitted (ArithmeticLower.body expression).instrs.toList := by
  intro instruction member
  simp only [ArithmeticLower.body, Array.toList_push, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | rfl
  · exact plan_admitted expression 2 instruction member
  · trivial

theorem metadata_retained (cfg : Config) (input : Artifact) :
    (versionArtifact cfg input).functions = input.functions ∧
      (versionArtifact cfg input).calls = input.calls ∧
      (versionArtifact cfg input).mir.data = input.mir.data := ⟨rfl, rfl, rfl⟩

theorem calls_retained (cfg : Config) (input : Artifact) (environment : OpenFrame.Environment) :
    OpenFrame.calls (versionArtifact cfg input) environment = OpenFrame.calls input environment := rfl

theorem actual_start (cfg : Config) (expression : Expression) (memory : Lir.Memory) :
    OpenFrame.start (artifact cfg expression) "main" [] memory = some (invocation cfg expression memory) := by
  have functions : (artifact cfg expression).mir.funcs = #[versionFunc cfg (ArithmeticLower.function expression)] := by
    simp only [artifact, versionArtifact, ArithmeticLower.artifact, ArithmeticLower.unit, Array.map_singleton]
  unfold OpenFrame.start
  rw [functions]
  rfl

theorem prologue_found (cfg : Config) (expression : Expression) :
    (versionFunc cfg (ArithmeticLower.function expression)).blocks[0]? = some
      (roundTripBlock cfg (freshBase (ArithmeticLower.function expression)) AdditionLower.prologue) :=
  LambdaSSA.ContextualSoundness.versionFunc_block (function := ArithmeticLower.function expression)
    (source := AdditionLower.prologue) (index := 0) rfl cfg

theorem body_found (cfg : Config) (expression : Expression) :
    (versionFunc cfg (ArithmeticLower.function expression)).blocks[1]? = some
      (roundTripBlock cfg (freshBase (ArithmeticLower.function expression)) (ArithmeticLower.body expression)) :=
  LambdaSSA.ContextualSoundness.versionFunc_block (function := ArithmeticLower.function expression)
    (source := ArithmeticLower.body expression) (index := 1) rfl cfg

theorem fallback_found (cfg : Config) (expression : Expression) :
    (versionFunc cfg (ArithmeticLower.function expression)).blocks[2]? = some
      (roundTripBlock cfg (freshBase (ArithmeticLower.function expression)) AdditionLower.fallback) :=
  LambdaSSA.ContextualSoundness.versionFunc_block (function := ArithmeticLower.function expression)
    (source := AdditionLower.fallback) (index := 2) rfl cfg

/-- Actual source execution is derived from bounds; actual contextual admission
transports it through either real LambdaSSA/fallback branch at the source's own
freshBase. Neither selected syntax nor a candidate trace is supplied. -/
theorem versioned_run (cfg : Config) (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory)
    (sourceInput candidateInput : Lir.Frame Nat)
    (agrees : Validation.PureSoundness.FrameAgrees (freshBase (ArithmeticLower.function expression))
      sourceInput candidateInput) :
    OpenFrame.Run (OpenFrame.calls (artifact cfg expression) environment)
      (versionFunc cfg (ArithmeticLower.function expression)) ⟨0, candidateInput, memory⟩
      (.returned [BitVec.ofInt 64 expression.value] memory) := by
  let summaries := OpenFrame.calls (artifact cfg expression) environment
  obtain ⟨middle, prologueRun, prologueAgree⟩ := prologue_contextual cfg
    (freshBase (ArithmeticLower.function expression)) summaries sourceInput candidateInput memory environment.frameAddress
    (OpenFrame.reserved_address _ _ _) agrees
  have sourceRun : BlockExec summaries (ArithmeticLower.body expression)
      (sourceInput.set 0 environment.frameAddress) memory (.returned [BitVec.ofInt 64 expression.value])
      (ArithmeticLower.bodyFrame expression (sourceInput.set 0 environment.frameAddress)) memory :=
    ArithmeticLower.body_executed expression bounded summaries _ memory
  obtain ⟨candidate, final, found, bodyRun, _⟩ := Validation.Slots.Caller.versionFunc_block_contextual
    (function := ArithmeticLower.function expression) (source := ArithmeticLower.body expression) (index := 1)
    rfl (body_admitted expression) cfg summaries (sourceInput.set 0 environment.frameAddress) middle
    _ prologueAgree memory memory (.returned [BitVec.ofInt 64 expression.value]) sourceRun
  exact .next (.jump (prologue_found cfg expression) prologueRun) (.stop ⟨candidate, final, found, bodyRun⟩)

theorem slots_call_free {block : Mir.Block} (admitted : Validation.Slots.Admitted block.instrs.toList) :
    OpenFrame.BlockCallFree block := by
  intro instruction member
  have allowed := admitted instruction member
  cases instruction <;> simp_all [Validation.Slots.AdmittedInstr, OpenFrame.CallFree]

theorem actual_call_free (cfg : Config) (expression : Expression) :
    OpenFrame.FunctionCallFree (versionFunc cfg (ArithmeticLower.function expression)) := by
  intro label block found
  have labelBound : label < 3 := by
    have bounded := (Array.getElem?_eq_some_iff).mp found
    simpa [versionFunc, ArithmeticLower.function] using bounded.1
  interval_cases label
  · have same : block = roundTripBlock cfg (freshBase (ArithmeticLower.function expression)) AdditionLower.prologue :=
      Option.some.inj (found.symm.trans (prologue_found cfg expression))
    exact same.symm ▸ prologue_call_free cfg _
  · have same : block = roundTripBlock cfg (freshBase (ArithmeticLower.function expression)) (ArithmeticLower.body expression) :=
      Option.some.inj (found.symm.trans (body_found cfg expression))
    exact same.symm ▸ slots_call_free
      (Validation.Slots.Caller.roundTripBlock_admitted cfg _ _ (body_admitted expression))
  · have same : block = roundTripBlock cfg (freshBase (ArithmeticLower.function expression)) AdditionLower.fallback :=
      Option.some.inj (found.symm.trans (fallback_found cfg expression))
    have admitted : Validation.Slots.Admitted AdditionLower.fallback.instrs.toList := by
      simp [AdditionLower.fallback, Validation.Slots.Admitted, Validation.Slots.AdmittedInstr,
        Validation.Slots.AdmittedOp, Validation.Roots.Admitted]
    exact same.symm ▸ slots_call_free (Validation.Slots.Caller.roundTripBlock_admitted cfg _ _ admitted)

theorem function_observations_exact (cfg : Config) (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Behaves (OpenFrame.calls (artifact cfg expression) environment)
      (versionFunc cfg (ArithmeticLower.function expression)) (ArithmeticOpenFrame.initial memory) behavior ↔
      behavior = .returned [BitVec.ofInt 64 expression.value] memory := by
  apply OpenFrame.run_observations_exact (actual_call_free cfg expression)
  exact versioned_run cfg expression bounded environment memory .empty .empty ⟨rfl, fun _ _ => rfl⟩

theorem artifact_observations_exact (cfg : Config) (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Observes (artifact cfg expression) environment "main" [] memory behavior ↔
      behavior = .returned [BitVec.ofInt 64 expression.value] memory := by
  constructor
  · rintro ⟨candidate, started, executed⟩
    have same := Option.some.inj ((actual_start cfg expression memory).symm.trans started)
    subst candidate
    exact (function_observations_exact cfg expression bounded environment memory behavior).1 executed
  · intro expected
    exact ⟨invocation cfg expression memory, actual_start cfg expression memory,
      (function_observations_exact cfg expression bounded environment memory behavior).2 expected⟩

theorem run_value (context : ArithmeticInstitution.Context) (cfg : Config) (program : ArithmeticInstitution.Program) :
    run context cfg program = some (target cfg program) := by
  rw [run, ArithmeticInstitution.run_value]
  rfl

theorem target_behaviors_exact (context : ArithmeticInstitution.Context) (cfg : Config)
    (program : ArithmeticInstitution.Program) (observation : ArithmeticInstitution.Observation) :
    observation ∈ ArithmeticInstitution.targetBehaviors context (target cfg program) ↔
      observation = Main.expectedExit program.expression := by
  constructor
  · rintro ⟨behavior, observed, projected⟩
    have actual : behavior = .returned [BitVec.ofInt 64 program.expression.value] context.memory :=
      (artifact_observations_exact cfg program.expression program.bounds context.environment context.memory behavior).1 observed
    subst behavior
    exact projected.symm.trans (ArithmeticInstitution.returned_process program.expression context.memory)
  · intro expectedObservation
    refine ⟨.returned [BitVec.ofInt 64 program.expression.value] context.memory,
      (artifact_observations_exact cfg program.expression program.bounds context.environment context.memory _).2 rfl, ?_⟩
    exact (ArithmeticInstitution.returned_process program.expression context.memory).trans expectedObservation.symm

theorem expected_behaviors (context : ArithmeticInstitution.Context) (cfg : Config) (program : ArithmeticInstitution.Program) :
    ArithmeticInstitution.sourceLanguage.beh program = (ArithmeticInstitution.targetLanguage context).beh (target cfg program) := by
  ext observation
  exact (ArithmeticInstitution.source_behaviors_exact program observation).trans
    (target_behaviors_exact context cfg program observation).symm

def pass (context : ArithmeticInstitution.Context) (cfg : Config) : Category.Pass (ArithmeticInstitution.convention context) where
  run := run context cfg
  sound program output compiled := by
    have same : target cfg program = output := Option.some.inj ((run_value context cfg program).symm.trans compiled)
    subst output
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro observation member
    exact ⟨observation, (expected_behaviors context cfg program).symm ▸ member, rfl⟩

def compiler (context : ArithmeticInstitution.Context) (cfg : Config) := (pass context cfg).toCompiler

theorem pass_run_pipeline (context : ArithmeticInstitution.Context) (cfg : Config)
    (program : ArithmeticInstitution.Program) :
    (pass context cfg).run program = ((ArithmeticInstitution.pass context).run program).map
      (fun output => { output with artifact := versionArtifact cfg output.artifact }) := rfl

theorem accepted_program (context : ArithmeticInstitution.Context) (cfg : Config) :
    ∃ program output, (pass context cfg).run program = some output :=
  ⟨ArithmeticInstitution.exampleProgram, target cfg ArithmeticInstitution.exampleProgram,
    run_value context cfg ArithmeticInstitution.exampleProgram⟩

theorem target_nonempty (context : ArithmeticInstitution.Context) (cfg : Config)
    (program : ArithmeticInstitution.Program) :
    ∃ observation, observation ∈ (ArithmeticInstitution.targetLanguage context).beh (target cfg program) :=
  ⟨Main.expectedExit program.expression, (target_behaviors_exact context cfg program _).2 rfl⟩

theorem run_sat (context : ArithmeticInstitution.Context) (cfg : Config)
    (program : ArithmeticInstitution.Program) (specification : Set ArithmeticInstitution.Observation) :
    ArithmeticInstitution.sourceLanguage.Sat program specification ↔
      (ArithmeticInstitution.targetLanguage context).Sat (target cfg program) specification := by
  change ArithmeticInstitution.sourceLanguage.beh program ⊆ specification ↔
    (ArithmeticInstitution.targetLanguage context).beh (target cfg program) ⊆ specification
  rw [expected_behaviors context cfg program]
  exact Iff.rfl

namespace Hets
open Silmaril.Logic.Institution

theorem run_readback_models (context : ArithmeticInstitution.Context) (cfg : Config)
    (program : ArithmeticInstitution.Program) :
    (((ArithmeticInstitution.Hets.graph context).comor ArithmeticInstitution.Hets.Translation.lower).ρ.app
          (Discrete.mk ())).mod.obj ((ArithmeticInstitution.targetLanguage context).beh (target cfg program)) =
      ArithmeticInstitution.sourceLanguage.beh program := by
  change _root_.id '' (ArithmeticInstitution.targetLanguage context).beh (target cfg program) =
    ArithmeticInstitution.sourceLanguage.beh program
  rw [Set.image_id]
  exact (expected_behaviors context cfg program).symm

theorem run_graph_sat (context : ArithmeticInstitution.Context) (cfg : Config)
    (program : ArithmeticInstitution.Program) (specification : Set ArithmeticInstitution.Observation) :
    (((ArithmeticInstitution.Hets.graph context).inst ArithmeticInstitution.Hets.Node.cerberus).I.obj
        (Discrete.mk ())).Sat (ArithmeticInstitution.sourceLanguage.beh program) specification ↔
      (((ArithmeticInstitution.Hets.graph context).inst ArithmeticInstitution.Hets.Node.openNative).I.obj
        (Discrete.mk ())).Sat ((ArithmeticInstitution.targetLanguage context).beh (target cfg program))
        ((((ArithmeticInstitution.Hets.graph context).comor ArithmeticInstitution.Hets.Translation.lower).ρ.app
          (Discrete.mk ())).sen specification) := by
  have condition := (((ArithmeticInstitution.Hets.graph context).comor ArithmeticInstitution.Hets.Translation.lower).ρ.app
    (Discrete.mk ())).sat ((ArithmeticInstitution.targetLanguage context).beh (target cfg program)) specification
  rw [run_readback_models context cfg program] at condition
  exact condition.symm

theorem versionedPath_comorphism (context : ArithmeticInstitution.Context) :
    IndexedCoInst.coHom (ArithmeticInstitution.Hets.graph context).indexed
        ((ArithmeticInstitution.Hets.graph context).pathHom (versionedPath context)) =
      (ArithmeticInstitution.Hets.graph context).comor ArithmeticInstitution.Hets.Translation.lower :=
  ArithmeticInstitution.Hets.loweringPath_comorphism context

end Hets
end Silmaril.Compiler.Native.Correctness.ArithmeticVersioned
