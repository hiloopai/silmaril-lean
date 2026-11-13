module

public import Silmaril.Compiler.Native.Correctness.AdditionOptimized.Defs
public import Silmaril.Compiler.Native.Optimize.Open.Cleanup.Thms
public import Silmaril.Compiler.Native.Correctness.AdditionVersioned.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionOptimized
open Silmaril.Compile Silmaril.Machine CategoryTheory
open Silmaril.Compiler.Native.Semantics Silmaril.Compiler.Native.Optimize

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

theorem actual_start (cfg : Config) (left right : Lir.Word) (memory : Lir.Memory) :
    OpenFrame.start (artifact cfg left right) "main" [] memory = some (invocation cfg left right memory) := by
  have functions : (artifact cfg left right).mir.funcs =
      #[Open.Cleanup.optimizeFunc cfg (AdditionLower.function left right)] := by
    rw [artifact, artifact_mir]
    simp only [AdditionLower.artifact, AdditionLower.unit, Array.map_singleton]
  unfold OpenFrame.start
  rw [functions]
  simp [Open.Cleanup.optimize_name, Open.Cleanup.optimize_params,
    Contract.MirSem.enter, Lir.Frame.writeAll, invocation, AdditionOpenFrame.invocation, AdditionOpenFrame.initial,
    artifact, optimizeArtifact, AdditionLower.artifact, AdditionLower.function]

/-- The real localSSA gate uses either the independently proved unversioned
source run or actual versionFunc, with its real LambdaSSA/checker/fallback. -/
theorem actual_run (cfg : Config) (left right : Int) (bounds : AdditionSource.Bounds left right)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) :
    OpenFrame.Run
      (OpenFrame.calls (artifact cfg (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) environment)
      (Open.Cleanup.optimizeFunc cfg (AdditionLower.function (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)))
      (AdditionOpenFrame.initial memory) (.returned [BitVec.ofInt 64 (left + right)] memory) := by
  simp only [artifact, calls_retained]
  let summaries := OpenFrame.calls (AdditionLower.artifact (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) environment
  have selected : OpenFrame.Run summaries
      (if cfg.localSSA then versionFunc cfg (AdditionLower.function (BitVec.ofInt 64 left) (BitVec.ofInt 64 right))
        else AdditionLower.function (BitVec.ofInt 64 left) (BitVec.ofInt 64 right))
      (AdditionOpenFrame.initial memory) (.returned [BitVec.ofInt 64 (left + right)] memory) := by
    cases enabled : cfg.localSSA with
    | false =>
      simpa only [enabled, Bool.false_eq_true, ↓reduceIte] using AdditionOpenFrame.actual_run left right bounds environment memory
    | true =>
      simpa only [enabled, ↓reduceIte, AdditionVersioned.artifact, AdditionVersioned.calls_retained,
        summaries, AdditionOpenFrame.initial] using
        AdditionVersioned.versioned_run cfg left right bounds environment memory .empty .empty ⟨rfl, fun _ _ => rfl⟩
  exact Open.Cleanup.run_entry_zero cfg summaries selected (by
    intro impossible
    cases impossible)

theorem actual_call_free (cfg : Config) (left right : Lir.Word) :
    OpenFrame.FunctionCallFree (Open.Cleanup.optimizeFunc cfg (AdditionLower.function left right)) := by
  unfold Open.Cleanup.optimizeFunc
  apply Open.Cleanup.function_call_free
  cases enabled : cfg.localSSA with
  | false => simpa only [enabled, Bool.false_eq_true, ↓reduceIte] using AdditionOpenFrame.actual_call_free left right
  | true => simpa only [enabled, ↓reduceIte] using AdditionVersioned.actual_call_free cfg left right

theorem function_observations_exact (cfg : Config) (left right : Int) (bounds : AdditionSource.Bounds left right)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Behaves
      (OpenFrame.calls (artifact cfg (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) environment)
      (Open.Cleanup.optimizeFunc cfg (AdditionLower.function (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)))
      (AdditionOpenFrame.initial memory) behavior ↔
      behavior = .returned [BitVec.ofInt 64 (left + right)] memory :=
  OpenFrame.run_observations_exact (actual_call_free cfg _ _) (actual_run cfg left right bounds environment memory) behavior

theorem artifact_observations_exact (cfg : Config) (left right : Int) (bounds : AdditionSource.Bounds left right)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Observes (artifact cfg (BitVec.ofInt 64 left) (BitVec.ofInt 64 right))
      environment "main" [] memory behavior ↔
      behavior = .returned [BitVec.ofInt 64 (left + right)] memory := by
  constructor
  · rintro ⟨candidate, started, executed⟩
    have same := Option.some.inj ((actual_start cfg _ _ memory).symm.trans started)
    subst candidate
    exact (function_observations_exact cfg left right bounds environment memory behavior).1 executed
  · intro expected
    exact ⟨invocation cfg _ _ memory, actual_start cfg _ _ memory,
      (function_observations_exact cfg left right bounds environment memory behavior).2 expected⟩

theorem default_observations_exact (left right : Int) (bounds : AdditionSource.Bounds left right)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Observes (optimizeArtifact {} (AdditionLower.artifact (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)))
      environment "main" [] memory behavior ↔
      behavior = .returned [BitVec.ofInt 64 (left + right)] memory :=
  artifact_observations_exact {} left right bounds environment memory behavior

theorem run_value (context : AdditionInstitution.Context) (cfg : Config) (program : AdditionInstitution.Program) :
    run context cfg program = some (target cfg program) := by
  rw [run, AdditionInstitution.run_value]
  rfl

theorem target_behaviors_exact (context : AdditionInstitution.Context) (cfg : Config)
    (program : AdditionInstitution.Program) (observation : AdditionInstitution.Observation) :
    observation ∈ AdditionInstitution.targetBehaviors context (target cfg program) ↔
      observation = AdditionMain.expectedExit program.left program.right := by
  constructor
  · rintro ⟨behavior, observed, projected⟩
    have actual : behavior = .returned [BitVec.ofInt 64 (program.left + program.right)] context.memory :=
      (artifact_observations_exact cfg program.left program.right program.bounds context.environment context.memory behavior).1 observed
    subst behavior
    exact projected.symm.trans (AdditionInstitution.returned_process program.left program.right context.memory)
  · intro expectedObservation
    refine ⟨.returned [BitVec.ofInt 64 (program.left + program.right)] context.memory,
      (artifact_observations_exact cfg program.left program.right program.bounds context.environment context.memory _).2 rfl, ?_⟩
    exact (AdditionInstitution.returned_process program.left program.right context.memory).trans expectedObservation.symm

theorem expected_behaviors (context : AdditionInstitution.Context) (cfg : Config) (program : AdditionInstitution.Program) :
    AdditionInstitution.sourceLanguage.beh program = (AdditionInstitution.targetLanguage context).beh (target cfg program) := by
  ext observation
  exact (AdditionInstitution.source_behaviors_exact program observation).trans
    (target_behaviors_exact context cfg program observation).symm

def pass (context : AdditionInstitution.Context) (cfg : Config) : Category.Pass (AdditionInstitution.convention context) where
  run := run context cfg
  sound program output compiled := by
    have same : target cfg program = output := Option.some.inj ((run_value context cfg program).symm.trans compiled)
    subst output
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro observation member
    exact ⟨observation, (expected_behaviors context cfg program).symm ▸ member, rfl⟩

def compiler (context : AdditionInstitution.Context) (cfg : Config) := (pass context cfg).toCompiler

theorem pass_run_pipeline (context : AdditionInstitution.Context) (cfg : Config)
    (program : AdditionInstitution.Program) :
    (pass context cfg).run program = ((AdditionInstitution.pass context).run program).map
      (fun output => { output with artifact := optimizeArtifact cfg output.artifact }) := rfl

/-- The real unchanged default optimizer in the actual lower/optimize pipeline,
with every Config default retained and the original lowering errors preserved. -/
theorem default_pass_run_pipeline (context : AdditionInstitution.Context) (program : AdditionInstitution.Program) :
    (pass context {}).run program =
      match Lower.compile context.tag (AdditionSource.program program.left program.right) with
      | .ok input => some ⟨{ input with mir := (optimize #[input.mir])[0]! }, "main", []⟩
      | .error _ => none := by
  change run context {} program = _
  unfold run AdditionInstitution.run
  cases Lower.compile context.tag (AdditionSource.program program.left program.right) <;> rfl

theorem accepted_program (context : AdditionInstitution.Context) (cfg : Config) :
    ∃ program output, (pass context cfg).run program = some output :=
  ⟨AdditionInstitution.exampleProgram, target cfg AdditionInstitution.exampleProgram,
    run_value context cfg AdditionInstitution.exampleProgram⟩

theorem target_nonempty (context : AdditionInstitution.Context) (cfg : Config)
    (program : AdditionInstitution.Program) :
    ∃ observation, observation ∈ (AdditionInstitution.targetLanguage context).beh (target cfg program) :=
  ⟨AdditionMain.expectedExit program.left program.right, (target_behaviors_exact context cfg program _).2 rfl⟩

theorem run_sat (context : AdditionInstitution.Context) (cfg : Config)
    (program : AdditionInstitution.Program) (specification : Set AdditionInstitution.Observation) :
    AdditionInstitution.sourceLanguage.Sat program specification ↔
      (AdditionInstitution.targetLanguage context).Sat (target cfg program) specification := by
  change AdditionInstitution.sourceLanguage.beh program ⊆ specification ↔
    (AdditionInstitution.targetLanguage context).beh (target cfg program) ⊆ specification
  rw [expected_behaviors context cfg program]
  exact Iff.rfl

namespace Hets
open Silmaril.Logic.Institution

theorem run_readback_models (context : AdditionInstitution.Context) (cfg : Config)
    (program : AdditionInstitution.Program) :
    (((AdditionInstitution.Hets.graph context).comor AdditionInstitution.Hets.Translation.lower).ρ.app
          (Discrete.mk ())).mod.obj ((AdditionInstitution.targetLanguage context).beh (target cfg program)) =
      AdditionInstitution.sourceLanguage.beh program := by
  change _root_.id '' (AdditionInstitution.targetLanguage context).beh (target cfg program) =
    AdditionInstitution.sourceLanguage.beh program
  rw [Set.image_id]
  exact (expected_behaviors context cfg program).symm

theorem run_graph_sat (context : AdditionInstitution.Context) (cfg : Config)
    (program : AdditionInstitution.Program) (specification : Set AdditionInstitution.Observation) :
    (((AdditionInstitution.Hets.graph context).inst AdditionInstitution.Hets.Node.cerberus).I.obj
        (Discrete.mk ())).Sat (AdditionInstitution.sourceLanguage.beh program) specification ↔
      (((AdditionInstitution.Hets.graph context).inst AdditionInstitution.Hets.Node.openNative).I.obj
        (Discrete.mk ())).Sat ((AdditionInstitution.targetLanguage context).beh (target cfg program))
        ((((AdditionInstitution.Hets.graph context).comor AdditionInstitution.Hets.Translation.lower).ρ.app
          (Discrete.mk ())).sen specification) := by
  have condition := (((AdditionInstitution.Hets.graph context).comor AdditionInstitution.Hets.Translation.lower).ρ.app
    (Discrete.mk ())).sat ((AdditionInstitution.targetLanguage context).beh (target cfg program)) specification
  rw [run_readback_models context cfg program] at condition
  exact condition.symm

theorem optimizedPath_comorphism (context : AdditionInstitution.Context) :
    IndexedCoInst.coHom (AdditionInstitution.Hets.graph context).indexed
        ((AdditionInstitution.Hets.graph context).pathHom (optimizedPath context)) =
      (AdditionInstitution.Hets.graph context).comor AdditionInstitution.Hets.Translation.lower :=
  AdditionInstitution.Hets.loweringPath_comorphism context

end Hets
end Silmaril.Compiler.Native.Correctness.AdditionOptimized
