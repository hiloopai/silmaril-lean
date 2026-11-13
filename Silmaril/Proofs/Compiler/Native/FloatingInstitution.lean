module

public import Silmaril.Compiler.Native.Optimize.FloatingInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.FiniteInstitution.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.FloatingInstitution
open Silmaril.Machine Silmaril.Compile CategoryTheory
open Silmaril.Compile.Contract

/-- The target domain is an independently defined weakening of source
finite definedness; it does not need source syntax admission. -/
theorem source_target_defined (context : Context) {units : Array Mir.Unit}
    (defined : SourceDefined context units) : TargetDefined context units := by
  obtain ⟨function, frame, outcome, admitted, started, executed⟩ := defined
  exact ⟨outcome, _, started, executed⟩

/-- The complete actual machine model is determined by an actual behavior
witness, using real startup and raw-machine behavior uniqueness. -/
theorem behaviors_singleton (context : Context) {units : Array Mir.Unit} {behavior : Lir.Behavior}
    (executed : Validation.Cleanup.ProgramBehaves units context.placement context.size behavior) :
    behaviors context units = {behavior} := by
  obtain ⟨state, started, actual⟩ := executed
  exact FiniteInstitution.behaviors_singleton context started actual

/-- Stuck/divergent observations are retained in the raw model and excluded
by proved actual finite behavior, rather than by the model definition. -/
theorem behaviors_finite (context : Context) {units : Array Mir.Unit}
    (defined : TargetDefined context units) {behavior : Lir.Behavior}
    (member : behavior ∈ behaviors context units) :
    behavior ≠ .stuck ∧ behavior ≠ .diverges := by
  obtain ⟨outcome, executed⟩ := defined
  rw [behaviors_singleton context executed] at member
  have same : behavior = outcome.behavior := member
  subst behavior
  cases outcome <;> simp [Validation.Finite.Outcome.behavior]

/-- Actual source execution derives actual finite target startup/behavior
for all six compiler flags, including every concrete cleanup pass. -/
theorem optimizeWith_defined (context : Context) (cfg : Config) {units : Array Mir.Unit}
    (defined : SourceDefined context units) : TargetDefined context (optimizeWith cfg units) := by
  obtain ⟨function, frame, outcome, admitted, started, executed⟩ := defined
  exact ⟨outcome, Validation.Floating.Finite.optimizeWith_program context.calls units context.placement cfg context.size
    function frame admitted outcome started executed⟩

/-- Equality covers every raw actual behavior on each side. No candidate
execution or candidate syntax/checker/simulation premise is supplied. -/
theorem optimizeWith_behaviors (context : Context) (cfg : Config) {units : Array Mir.Unit}
    (defined : SourceDefined context units) :
    behaviors context units = behaviors context (optimizeWith cfg units) := by
  obtain ⟨function, frame, outcome, admitted, started, executed⟩ := defined
  have sourceExecuted : Validation.Cleanup.ProgramBehaves units context.placement context.size outcome.behavior :=
    ⟨_, started, executed⟩
  have targetExecuted : Validation.Cleanup.ProgramBehaves (optimizeWith cfg units) context.placement context.size outcome.behavior :=
    Validation.Floating.Finite.optimizeWith_program context.calls units context.placement cfg context.size
      function frame admitted outcome started executed
  exact (behaviors_singleton context sourceExecuted).trans (behaviors_singleton context targetExecuted).symm

/-- Add only a proof field to the exact existing configured compiler. -/
def run (context : Context) (cfg : Config) (source : SourceProgram context) : TargetProgram context :=
  ⟨optimizeWith cfg source.val, optimizeWith_defined context cfg source.property⟩

theorem run_value (context : Context) (cfg : Config) (source : SourceProgram context) :
    (run context cfg source).val = optimizeWith cfg source.val := rfl

/-- The existing default optimizer, with local SSA, LambdaSSA and all four
cleanup passes retaining their actual default values. -/
def runDefault (context : Context) (source : SourceProgram context) : TargetProgram context :=
  run context {} source

theorem runDefault_value (context : Context) (source : SourceProgram context) :
    (runDefault context source).val = optimize source.val := rfl

theorem run_behaviors (context : Context) (cfg : Config) (source : SourceProgram context) :
    (sourceLanguage context).beh source = (targetLanguage context).beh (run context cfg source) :=
  optimizeWith_behaviors context cfg source.property

/-- The actual total compiler as an always-successful existing Category.Pass
between the distinct source/target languages. No runtime guard or fallback. -/
def pass (context : Context) (cfg : Config) : Category.Pass (convention context) where
  run source := some (run context cfg source)
  sound source candidate selected := by
    have same : run context cfg source = candidate := Option.some.inj selected
    subst candidate
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro behavior member
    exact ⟨behavior, (run_behaviors context cfg source).symm ▸ member, rfl⟩

theorem pass_run_value (context : Context) (cfg : Config) (source : SourceProgram context) :
    ((pass context cfg).run source).map (fun program : TargetProgram context => program.val) =
      some (optimizeWith cfg source.val) := rfl

def defaultPass (context : Context) : Category.Pass (convention context) := pass context {}

theorem defaultPass_run_value (context : Context) (source : SourceProgram context) :
    ((defaultPass context).run source).map (fun program : TargetProgram context => program.val) =
      some (optimize source.val) := rfl

def compiler (context : Context) (cfg : Config) := (pass context cfg).toCompiler

/-- The existing compiler projection retains the exact configured optimizer. -/
theorem compiler_run_value (context : Context) (cfg : Config) (source : SourceProgram context) :
    ((compiler context cfg).run source).map (fun program : TargetProgram context => program.val) =
      some (optimizeWith cfg source.val) := rfl

/-- Satisfaction equivalence for arbitrary sets of complete actual behaviors. -/
theorem run_room_sat (context : Context) (cfg : Config) (source : SourceProgram context)
    (specification : Set Lir.Behavior) :
    ((sourceLanguage context).room ()).Sat ((sourceLanguage context).beh source) specification ↔
      ((targetLanguage context).room ()).Sat ((targetLanguage context).beh (run context cfg source)) specification := by
  change (sourceLanguage context).beh source ⊆ specification ↔
    (targetLanguage context).beh (run context cfg source) ⊆ specification
  rw [run_behaviors context cfg source]
  exact Iff.rfl

theorem run_sat (context : Context) (cfg : Config) (source : SourceProgram context)
    (specification : Set Lir.Behavior) :
    (sourceLanguage context).Sat source specification ↔
      (targetLanguage context).Sat (run context cfg source) specification :=
  run_room_sat context cfg source specification

namespace Hets
open Silmaril.Logic.Institution

theorem run_readback_models (context : Context) (cfg : Config) (source : SourceProgram context) :
    (((graph context).comor Translation.optimize).ρ.app (Discrete.mk ())).mod.obj
        ((targetLanguage context).beh (run context cfg source)) = (sourceLanguage context).beh source := by
  change _root_.id '' (targetLanguage context).beh (run context cfg source) = (sourceLanguage context).beh source
  rw [Set.image_id]
  exact (run_behaviors context cfg source).symm

theorem run_graph_sat (context : Context) (cfg : Config) (source : SourceProgram context)
    (specification : Set Lir.Behavior) :
    (((graph context).inst Node.source).I.obj (Discrete.mk ())).Sat ((sourceLanguage context).beh source) specification ↔
      (((graph context).inst Node.optimized).I.obj (Discrete.mk ())).Sat
        ((targetLanguage context).beh (run context cfg source))
        ((((graph context).comor Translation.optimize).ρ.app (Discrete.mk ())).sen specification) := by
  have condition := (((graph context).comor Translation.optimize).ρ.app (Discrete.mk ())).sat
    ((targetLanguage context).beh (run context cfg source)) specification
  rw [run_readback_models context cfg source] at condition
  exact condition.symm

theorem optimizerPath_comorphism (context : Context) :
    IndexedCoInst.coHom (graph context).indexed ((graph context).pathHom (optimizerPath context)) =
      (graph context).comor Translation.optimize :=
  (graph context).coHom_toPath Translation.optimize

end Hets
end Silmaril.Compiler.Native.Optimize.FloatingInstitution
