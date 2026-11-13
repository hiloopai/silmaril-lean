module

public import Silmaril.Compiler.Native.Correctness.ArithmeticOptimized.Defs
public import Silmaril.Compiler.Native.Optimize.Open.Cleanup.Thms
public import Silmaril.Compiler.Native.Correctness.ArithmeticVersioned.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.ArithmeticOptimized
open Silmaril.Compile Silmaril.Machine CategoryTheory
open Silmaril.Compiler.Native.Semantics Silmaril.Compiler.Native.Optimize
open Silmaril.Compiler.Core.SignedArithmetic

theorem artifact_mir (cfg : Config) (input : Artifact) :
    (optimizeArtifact cfg input).mir = { input.mir with funcs := input.mir.funcs.map (Open.Cleanup.optimizeFunc cfg) } := by
  unfold optimizeArtifact
  rw [Open.Cleanup.optimizeWith_eq_mapFuncs]
  simp [Mir.FuncPass.mapFuncs]

theorem metadata_retained (cfg : Config) (input : Artifact) :
    (optimizeArtifact cfg input).functions = input.functions ∧
      (optimizeArtifact cfg input).calls = input.calls ∧
      (optimizeArtifact cfg input).mir.data = input.mir.data := by
  exact ⟨rfl, rfl, congrArg (·.data) (artifact_mir cfg input)⟩

theorem calls_retained (cfg : Config) (input : Artifact) (environment : OpenFrame.Environment) :
    OpenFrame.calls (optimizeArtifact cfg input) environment = OpenFrame.calls input environment := rfl

theorem actual_units (cfg : Config) (input : Artifact) :
    optimizeWith cfg #[input.mir] = #[(optimizeArtifact cfg input).mir] := by
  rw [Open.Cleanup.optimizeWith_eq_mapFuncs, artifact_mir]
  simp [Mir.FuncPass.mapFuncs]

theorem default_units (input : Artifact) :
    optimize #[input.mir] = #[(optimizeArtifact {} input).mir] := actual_units {} input

theorem actual_start (cfg : Config) (expression : Expression) (memory : Lir.Memory) :
    OpenFrame.start (artifact cfg expression) "main" [] memory = some (invocation cfg expression memory) := by
  have functions : (artifact cfg expression).mir.funcs =
      #[Open.Cleanup.optimizeFunc cfg (ArithmeticLower.function expression)] := by
    rw [artifact, artifact_mir]
    simp only [ArithmeticLower.artifact, ArithmeticLower.unit, Array.map_singleton]
  unfold OpenFrame.start
  rw [functions]
  simp [Open.Cleanup.optimize_name, Open.Cleanup.optimize_params,
    Contract.MirSem.enter, Lir.Frame.writeAll, invocation, ArithmeticOpenFrame.invocation, ArithmeticOpenFrame.initial,
    artifact, optimizeArtifact, ArithmeticLower.artifact, ArithmeticLower.function]

/-- The real localSSA gate uses either the independently proved unversioned
source run or actual versionFunc, with its real LambdaSSA/checker/fallback. -/
theorem actual_run (cfg : Config) (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) :
    OpenFrame.Run
      (OpenFrame.calls (artifact cfg expression) environment)
      (Open.Cleanup.optimizeFunc cfg (ArithmeticLower.function expression))
      (ArithmeticOpenFrame.initial memory) (.returned [BitVec.ofInt 64 expression.value] memory) := by
  simp only [artifact, calls_retained]
  let summaries := OpenFrame.calls (ArithmeticLower.artifact expression) environment
  have selected : OpenFrame.Run summaries
      (if cfg.localSSA then versionFunc cfg (ArithmeticLower.function expression)
        else ArithmeticLower.function expression)
      (ArithmeticOpenFrame.initial memory) (.returned [BitVec.ofInt 64 expression.value] memory) := by
    cases enabled : cfg.localSSA with
    | false =>
      simpa only [enabled, Bool.false_eq_true, ↓reduceIte] using ArithmeticOpenFrame.actual_run expression bounded environment memory
    | true =>
      simpa only [enabled, ↓reduceIte, ArithmeticVersioned.artifact, ArithmeticVersioned.calls_retained,
        summaries, ArithmeticOpenFrame.initial] using
        ArithmeticVersioned.versioned_run cfg expression bounded environment memory .empty .empty ⟨rfl, fun _ _ => rfl⟩
  exact Open.Cleanup.run_entry_zero cfg summaries selected (by
    intro impossible
    cases impossible)

theorem actual_call_free (cfg : Config) (expression : Expression) :
    OpenFrame.FunctionCallFree (Open.Cleanup.optimizeFunc cfg (ArithmeticLower.function expression)) := by
  unfold Open.Cleanup.optimizeFunc
  apply Open.Cleanup.function_call_free
  cases enabled : cfg.localSSA with
  | false => simpa only [enabled, Bool.false_eq_true, ↓reduceIte] using ArithmeticOpenFrame.actual_call_free expression
  | true => simpa only [enabled, ↓reduceIte] using ArithmeticVersioned.actual_call_free cfg expression

theorem function_observations_exact (cfg : Config) (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Behaves
      (OpenFrame.calls (artifact cfg expression) environment)
      (Open.Cleanup.optimizeFunc cfg (ArithmeticLower.function expression))
      (ArithmeticOpenFrame.initial memory) behavior ↔
      behavior = .returned [BitVec.ofInt 64 expression.value] memory :=
  OpenFrame.run_observations_exact (actual_call_free cfg _) (actual_run cfg expression bounded environment memory) behavior

theorem artifact_observations_exact (cfg : Config) (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Observes (artifact cfg expression)
      environment "main" [] memory behavior ↔
      behavior = .returned [BitVec.ofInt 64 expression.value] memory := by
  constructor
  · rintro ⟨candidate, started, executed⟩
    have same := Option.some.inj ((actual_start cfg _ memory).symm.trans started)
    subst candidate
    exact (function_observations_exact cfg expression bounded environment memory behavior).1 executed
  · intro expected
    exact ⟨invocation cfg _ memory, actual_start cfg _ memory,
      (function_observations_exact cfg expression bounded environment memory behavior).2 expected⟩

theorem default_observations_exact (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Observes (optimizeArtifact {} (ArithmeticLower.artifact expression))
      environment "main" [] memory behavior ↔
      behavior = .returned [BitVec.ofInt 64 expression.value] memory :=
  artifact_observations_exact {} expression bounded environment memory behavior

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
      (fun output => { output with artifact := optimizeArtifact cfg output.artifact }) := rfl

/-- The real unchanged default optimizer in the actual lower/optimize pipeline,
with every Config default retained and the original lowering errors preserved. -/
theorem default_pass_run_pipeline (context : ArithmeticInstitution.Context) (program : ArithmeticInstitution.Program) :
    (pass context {}).run program =
      match Lower.compile context.tag (Main.program program.expression) with
      | .ok input => some ⟨{ input with mir := (optimize #[input.mir])[0]! }, "main", []⟩
      | .error _ => none := by
  change run context {} program = _
  unfold run ArithmeticInstitution.run
  cases Lower.compile context.tag (Main.program program.expression) <;> rfl

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

theorem optimizedPath_comorphism (context : ArithmeticInstitution.Context) :
    IndexedCoInst.coHom (ArithmeticInstitution.Hets.graph context).indexed
        ((ArithmeticInstitution.Hets.graph context).pathHom (optimizedPath context)) =
      (ArithmeticInstitution.Hets.graph context).comor ArithmeticInstitution.Hets.Translation.lower :=
  ArithmeticInstitution.Hets.loweringPath_comorphism context

end Hets
end Silmaril.Compiler.Native.Correctness.ArithmeticOptimized
