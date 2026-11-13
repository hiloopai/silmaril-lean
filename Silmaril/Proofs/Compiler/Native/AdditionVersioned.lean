module

public import Silmaril.Compiler.Native.Correctness.AdditionVersioned.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionInstitution.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Caller.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionVersioned

open Silmaril.Compile Silmaril.Machine CategoryTheory
open Silmaril.Compiler.Native.Semantics Silmaril.Compiler.Native.Optimize

theorem metadata_retained (cfg : Config) (input : Artifact) :
    (versionArtifact cfg input).functions = input.functions ∧
      (versionArtifact cfg input).calls = input.calls ∧
      (versionArtifact cfg input).mir.data = input.mir.data := ⟨rfl, rfl, rfl⟩

theorem calls_retained (cfg : Config) (input : Artifact) (environment : OpenFrame.Environment) :
    OpenFrame.calls (versionArtifact cfg input) environment = OpenFrame.calls input environment := rfl

theorem actual_start (cfg : Config) (left right : Lir.Word) (memory : Lir.Memory) :
    OpenFrame.start (artifact cfg left right) "main" [] memory =
      some (invocation cfg left right memory) := by
  have functions : (artifact cfg left right).mir.funcs =
      #[versionFunc cfg (AdditionLower.function left right)] := by
    simp only [artifact, versionArtifact, AdditionLower.artifact, AdditionLower.unit, Array.map_singleton]
  unfold OpenFrame.start
  rw [functions]
  rfl

theorem prologue_found (cfg : Config) (left right : Lir.Word) :
    (versionFunc cfg (AdditionLower.function left right)).blocks[0]? =
      some (roundTripBlock cfg 11 AdditionLower.prologue) := by
  have found := LambdaSSA.ContextualSoundness.versionFunc_block
    (function := AdditionLower.function left right) (source := AdditionLower.prologue) (index := 0) rfl cfg
  simpa only [AdditionLower.actual_freshBase] using found

theorem body_found (cfg : Config) (left right : Lir.Word) :
    (versionFunc cfg (AdditionLower.function left right)).blocks[1]? =
      some (roundTripBlock cfg 11 (AdditionLower.body left right)) := by
  have found := LambdaSSA.ContextualSoundness.versionFunc_block
    (function := AdditionLower.function left right) (source := AdditionLower.body left right) (index := 1) rfl cfg
  simpa only [AdditionLower.actual_freshBase] using found

theorem fallback_found (cfg : Config) (left right : Lir.Word) :
    (versionFunc cfg (AdditionLower.function left right)).blocks[2]? =
      some (roundTripBlock cfg 11 AdditionLower.fallback) := by
  have found := LambdaSSA.ContextualSoundness.versionFunc_block
    (function := AdditionLower.function left right) (source := AdditionLower.fallback) (index := 2) rfl cfg
  simpa only [AdditionLower.actual_freshBase] using found

/-- Whole execution from independently supplied partial frames. The source
frame executes the actual source body; only actual low-register/whole-slot
agreement connects it to the candidate's incoming frame. -/
theorem versioned_run (cfg : Config) (left right : Int) (bounds : AdditionSource.Bounds left right)
    (environment : OpenFrame.Environment) (memory : Lir.Memory)
    (sourceInput candidateInput : Lir.Frame Nat)
    (agrees : Validation.PureSoundness.FrameAgrees 11 sourceInput candidateInput) :
    OpenFrame.Run (OpenFrame.calls (artifact cfg (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) environment)
      (versionFunc cfg (AdditionLower.function (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)))
      ⟨0, candidateInput, memory⟩ (.returned [BitVec.ofInt 64 (left + right)] memory) := by
  let summaries := OpenFrame.calls (artifact cfg (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) environment
  have sourceRun : BlockExec summaries
      (AdditionLower.body (BitVec.ofInt 64 left) (BitVec.ofInt 64 right))
      (sourceInput.set 0 environment.frameAddress) memory
      (.returned [BitVec.ofInt 64 (left + right)])
      (AdditionLower.bodyFrame (sourceInput.set 0 environment.frameAddress)
        (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) memory :=
    AdditionLower.body_executed summaries (sourceInput.set 0 environment.frameAddress) memory left right bounds
  have member : AdditionLower.body (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) ∈
      (AdditionLower.function (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)).blocks.toList := by
    simp [AdditionLower.function]
  have bodyAgrees : Validation.PureSoundness.FrameAgrees 11
      (sourceInput.set 0 environment.frameAddress)
      ((candidateInput.set 11 environment.frameAddress).set 0 environment.frameAddress) :=
    AdditionLower.prologue_agrees sourceInput candidateInput environment.frameAddress agrees
  obtain ⟨candidateFinal, candidateRun, _⟩ := Validation.Slots.Caller.roundTripBlock_contextual
    member (AdditionLower.body_admitted _ _) cfg summaries
    (sourceInput.set 0 environment.frameAddress)
    ((candidateInput.set 11 environment.frameAddress).set 0 environment.frameAddress)
    _ (by simpa only [AdditionLower.actual_freshBase] using bodyAgrees)
    memory memory (.returned [BitVec.ofInt 64 (left + right)]) sourceRun
  have candidateBody : BlockExec summaries
      (roundTripBlock cfg 11 (AdditionLower.body (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)))
      ((candidateInput.set 11 environment.frameAddress).set 0 environment.frameAddress) memory
      (.returned [BitVec.ofInt 64 (left + right)]) candidateFinal memory := by
    simpa only [AdditionLower.actual_freshBase] using candidateRun
  have prologueRun : BlockExec summaries (roundTripBlock cfg 11 AdditionLower.prologue)
      candidateInput memory (.jump 1)
      ((candidateInput.set 11 environment.frameAddress).set 0 environment.frameAddress) memory :=
    AdditionLower.versioned_prologue_executed summaries cfg candidateInput memory
      environment.frameAddress (OpenFrame.reserved_address _ _ _)
  refine .next (.jump (prologue_found cfg _ _) prologueRun) (.stop ?_)
  exact ⟨_, candidateFinal, body_found cfg _ _, candidateBody⟩

theorem slots_call_free {block : Mir.Block} (admitted : Validation.Slots.Admitted block.instrs.toList) :
    OpenFrame.BlockCallFree block := by
  intro instruction member
  have allowed := admitted instruction member
  cases instruction <;> simp_all [Validation.Slots.AdmittedInstr, OpenFrame.CallFree]

theorem actual_call_free (cfg : Config) (left right : Lir.Word) :
    OpenFrame.FunctionCallFree (versionFunc cfg (AdditionLower.function left right)) := by
  intro label block found
  have labelBound : label < 3 := by
    have bounded := (Array.getElem?_eq_some_iff).mp found
    simpa [versionFunc, AdditionLower.function] using bounded.1
  interval_cases label
  · have same : block = roundTripBlock cfg 11 AdditionLower.prologue :=
      Option.some.inj (found.symm.trans (prologue_found cfg left right))
    rw [same, AdditionLower.actual_prologue]
    simp [OpenFrame.BlockCallFree, AdditionLower.versionedPrologue, OpenFrame.CallFree]
  · have same : block = roundTripBlock cfg 11 (AdditionLower.body left right) :=
      Option.some.inj (found.symm.trans (body_found cfg left right))
    exact same.symm ▸ slots_call_free
      (Validation.Slots.Caller.roundTripBlock_admitted cfg 11 _ (AdditionLower.body_admitted left right))
  · have same : block = roundTripBlock cfg 11 AdditionLower.fallback :=
      Option.some.inj (found.symm.trans (fallback_found cfg left right))
    have admitted : Validation.Slots.Admitted AdditionLower.fallback.instrs.toList := by
      simp [AdditionLower.fallback, Validation.Slots.Admitted, Validation.Slots.AdmittedInstr,
        Validation.Slots.AdmittedOp, Validation.Roots.Admitted, Mir.DeadCode.faults]
    exact same.symm ▸ slots_call_free (Validation.Slots.Caller.roundTripBlock_admitted cfg 11 _ admitted)

theorem function_observations_exact (cfg : Config) (left right : Int) (bounds : AdditionSource.Bounds left right)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Behaves
        (OpenFrame.calls (artifact cfg (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) environment)
        (versionFunc cfg (AdditionLower.function (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)))
        (AdditionOpenFrame.initial memory) behavior ↔
      behavior = .returned [BitVec.ofInt 64 (left + right)] memory := by
  apply OpenFrame.run_observations_exact (actual_call_free cfg _ _)
  exact versioned_run cfg left right bounds environment memory .empty .empty ⟨rfl, fun _ _ => rfl⟩

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
      (fun output => { output with artifact := versionArtifact cfg output.artifact }) := rfl

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

theorem versionedPath_comorphism (context : AdditionInstitution.Context) :
    IndexedCoInst.coHom (AdditionInstitution.Hets.graph context).indexed
        ((AdditionInstitution.Hets.graph context).pathHom (versionedPath context)) =
      (AdditionInstitution.Hets.graph context).comor AdditionInstitution.Hets.Translation.lower :=
  AdditionInstitution.Hets.loweringPath_comorphism context

end Hets
end Silmaril.Compiler.Native.Correctness.AdditionVersioned
