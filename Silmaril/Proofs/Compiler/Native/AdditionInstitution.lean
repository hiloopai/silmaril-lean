module

public import Silmaril.Compiler.Native.Correctness.AdditionInstitution.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionMain.Thms
public import Silmaril.Compiler.Native.Correctness.AdditionOpenFrame.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionInstitution

open Silmaril.Compile Silmaril.Machine CategoryTheory
open Silmaril.Compiler.Native.Semantics

/-- Both actual source UB exclusion and exact process behavior are proved
from the same independently constructed source, with its actual startup. -/
theorem source_behaviors_exact (program : Program) (observation : Observation) :
    observation ∈ sourceBehaviors program ↔
      observation = AdditionMain.expectedExit program.left program.right := by
  simp only [sourceBehaviors, Set.mem_ofPred_eq]
  rw [AdditionMain.source_process_exact program.left program.right program.bounds]
  exact or_iff_right (AdditionMain.source_no_undefined_behaviour program.left program.right program.bounds)

theorem source_model (program : Program) :
    ∃ model : Silmaril.Cerberus.Institution.Model,
      Elaborates (AdditionSource.source program.left program.right) model ∧
        Silmaril.Cerberus.Institution.Satisfies model (Silmaril.Compiler.Core.ElaborationTotal.returnsInteger (program.left + program.right)) :=
  AdditionMain.source_model program.left program.right program.bounds

theorem run_value (context : Context) (program : Program) :
    run context program = some (expected program) := by
  simp only [run, AdditionLower.compile program.left program.right program.bounds context.tag]
  rfl

theorem returned_process (left right : Int) (memory : Lir.Memory) :
    observe (.returned [BitVec.ofInt 64 (left + right)] memory) =
      AdditionMain.expectedExit left right := by
  change Silmaril.Compile.Core.Spec.Obs.exit ((BitVec.ofInt 64 (left + right)).toNat % 256) [] =
    .exit ((left + right) % 256).toNat []
  rw [LiteralEmission.word_status]

/-- The complete target model is evaluated before process projection. -/
theorem target_behaviors_exact (context : Context) (program : Program) (observation : Observation) :
    observation ∈ targetBehaviors context (expected program) ↔
      observation = AdditionMain.expectedExit program.left program.right := by
  constructor
  · rintro ⟨behavior, observed, projected⟩
    have actual : behavior = .returned [BitVec.ofInt 64 (program.left + program.right)] context.memory :=
      (AdditionOpenFrame.artifact_observations_exact program.left program.right program.bounds
        context.environment context.memory behavior).1 observed
    subst behavior
    exact projected.symm.trans (returned_process program.left program.right context.memory)
  · intro expectedObservation
    refine ⟨.returned [BitVec.ofInt 64 (program.left + program.right)] context.memory,
      (AdditionOpenFrame.artifact_observations_exact program.left program.right program.bounds
        context.environment context.memory _).2 rfl, ?_⟩
    exact (returned_process program.left program.right context.memory).trans expectedObservation.symm

/-- Equality of actual source and actual target process models, with distinct
independent source and target program domains. -/
theorem expected_behaviors (context : Context) (program : Program) :
    sourceLanguage.beh program = (targetLanguage context).beh (expected program) := by
  ext observation
  exact (source_behaviors_exact program observation).trans (target_behaviors_exact context program observation).symm

theorem run_behaviors (context : Context) (program : Program) (target : Target)
    (compiled : run context program = some target) :
    sourceLanguage.beh program = (targetLanguage context).beh target := by
  have same : expected program = target := Option.some.inj ((run_value context program).symm.trans compiled)
  exact same ▸ expected_behaviors context program

/-- A genuine pass for the existing lowerer over a nonempty independent source
domain. Native machine code, optimization and ABI refinement remain separate. -/
def pass (context : Context) : Category.Pass (convention context) where
  run := run context
  sound program target compiled := by
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro observation member
    exact ⟨observation, (run_behaviors context program target compiled).symm ▸ member, rfl⟩

theorem pass_run (context : Context) (program : Program) :
    (pass context).run program = run context program := rfl

def compiler (context : Context) := (pass context).toCompiler

theorem run_room_sat (context : Context) (program : Program) (target : Target)
    (compiled : run context program = some target) (specification : Set Observation) :
    (sourceLanguage.room ()).Sat (sourceLanguage.beh program) specification ↔
      ((targetLanguage context).room ()).Sat ((targetLanguage context).beh target) specification := by
  change sourceLanguage.beh program ⊆ specification ↔ (targetLanguage context).beh target ⊆ specification
  rw [run_behaviors context program target compiled]
  exact Iff.rfl

theorem run_sat (context : Context) (program : Program) (target : Target)
    (compiled : run context program = some target) (specification : Set Observation) :
    sourceLanguage.Sat program specification ↔ (targetLanguage context).Sat target specification :=
  run_room_sat context program target compiled specification

/-- A concrete member selected solely by source syntax and arithmetic bounds. -/
def exampleProgram : Program := ⟨17, -29, by
  unfold AdditionSource.Bounds LiteralEmission.IsInt32
  omega⟩

theorem accepted_program (context : Context) : ∃ program target, (pass context).run program = some target :=
  ⟨exampleProgram, expected exampleProgram, run_value context exampleProgram⟩

theorem source_nonempty : ∃ observation, observation ∈ sourceLanguage.beh exampleProgram :=
  ⟨AdditionMain.expectedExit 17 (-29), (source_behaviors_exact exampleProgram _).2 rfl⟩

theorem target_nonempty (context : Context) :
    ∃ observation, observation ∈ (targetLanguage context).beh (expected exampleProgram) :=
  ⟨AdditionMain.expectedExit 17 (-29), (target_behaviors_exact context exampleProgram _).2 rfl⟩

namespace Hets
open Silmaril.Logic.Institution

theorem run_readback_models (context : Context) (program : Program) (target : Target)
    (compiled : run context program = some target) :
    (((graph context).comor Translation.lower).ρ.app (Discrete.mk ())).mod.obj
        ((targetLanguage context).beh target) = sourceLanguage.beh program := by
  change _root_.id '' (targetLanguage context).beh target = sourceLanguage.beh program
  rw [Set.image_id]
  exact (run_behaviors context program target compiled).symm

theorem run_graph_sat (context : Context) (program : Program) (target : Target)
    (compiled : run context program = some target) (specification : Set Observation) :
    (((graph context).inst Node.cerberus).I.obj (Discrete.mk ())).Sat (sourceLanguage.beh program) specification ↔
      (((graph context).inst Node.openNative).I.obj (Discrete.mk ())).Sat
        ((targetLanguage context).beh target)
        ((((graph context).comor Translation.lower).ρ.app (Discrete.mk ())).sen specification) := by
  have condition := (((graph context).comor Translation.lower).ρ.app (Discrete.mk ())).sat
    ((targetLanguage context).beh target) specification
  rw [run_readback_models context program target compiled] at condition
  exact condition.symm

theorem loweringPath_comorphism (context : Context) :
    IndexedCoInst.coHom (graph context).indexed ((graph context).pathHom (loweringPath context)) =
      (graph context).comor Translation.lower :=
  (graph context).coHom_toPath Translation.lower

end Hets
end Silmaril.Compiler.Native.Correctness.AdditionInstitution
