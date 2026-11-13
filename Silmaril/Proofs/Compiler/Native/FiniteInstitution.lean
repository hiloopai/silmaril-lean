module

public import Silmaril.Compiler.Native.Optimize.FiniteInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.FiniteInstitution
open Silmaril.Machine Silmaril.Compile CategoryTheory
open Silmaril.Compile.Contract

/-- Admission of every actual mapped block follows from original membership
and the existing selected/fallback admission theorem. -/
theorem versionFunc_admitted (cfg : Config) {function : Mir.Func}
    (admitted : Validation.Finite.AdmittedFunction function) :
    Validation.Finite.AdmittedFunction (versionFunc cfg function) := by
  intro candidate member
  change candidate ∈ (function.blocks.map (roundTripBlock cfg (freshBase function))).toList at member
  rw [Array.toList_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact Validation.Finite.roundTripBlock_admitted cfg (freshBase function) source (admitted source sourceMember)

/-- Real source startup and finite execution derive the real mapped program's
independent domain proof; no candidate execution is supplied. -/
theorem versionUnits_defined (context : Context) (cfg : Config) {units : Array Mir.Unit}
    (defined : Defined context units) : Defined context (Validation.Finite.versionUnits cfg units) := by
  obtain ⟨function, frame, outcome, admitted, started, executed⟩ := defined
  refine ⟨versionFunc cfg function, frame, outcome, versionFunc_admitted cfg admitted, ?_, ?_⟩
  · rw [Validation.Finite.initMem_versionUnits]
    exact Validation.Finite.start_versionUnits cfg units context.placement context.size function frame started
  · rw [Validation.Finite.initMem_versionUnits]
    exact Validation.Finite.versionFunc_behaves context.calls units context.placement cfg function admitted outcome
      0 frame frame (MirSem.initMem units context.placement context.size)
      (Validation.Context.agrees_refl _ _) executed

/-- Every actual behavior model with an actual behavior witness is determined
by that witness, using the real MirSem uniqueness theorem, including stuckness
and divergence. The model itself remains defined from all real executions. -/
theorem behaviors_singleton (context : Context) {units : Array Mir.Unit} {state : MirSem.State}
    {behavior : Lir.Behavior}
    (started : MirSem.start units context.placement context.size = some state)
    (executed : MirSem.Behaves units context.placement state behavior) :
    behaviors context units = {behavior} := by
  ext other
  constructor
  · intro member
    obtain ⟨otherState, otherStart, otherExec⟩ := member
    have same : otherState = state := Option.some.inj (otherStart.symm.trans started)
    subst otherState
    exact (MirSem.Behaves.unique executed otherExec).symm
  · intro member
    have same : other = behavior := member
    subst other
    exact ⟨state, started, executed⟩

/-- Actual finite forward preservation and actual universal machine uniqueness
imply equality of complete source/candidate behavior models. -/
theorem versionUnits_behaviors (context : Context) (cfg : Config) {units : Array Mir.Unit}
    (defined : Defined context units) :
    behaviors context units = behaviors context (Validation.Finite.versionUnits cfg units) := by
  obtain ⟨function, frame, outcome, admitted, started, executed⟩ := defined
  obtain ⟨candidateState, candidateStart, candidateExec⟩ :=
    Validation.Finite.program_behaves context.calls units context.placement cfg context.size function frame admitted
      outcome started executed
  exact (behaviors_singleton context started executed).trans
    (behaviors_singleton context candidateStart candidateExec).symm

/-- The independent finite-success domain rules out both actual stuck and
actual divergent behaviors, rather than removing them from the model. -/
theorem behaviors_finite (context : Context) {units : Array Mir.Unit}
    (defined : Defined context units) {behavior : Lir.Behavior}
    (member : behavior ∈ behaviors context units) :
    behavior ≠ .stuck ∧ behavior ≠ .diverges := by
  obtain ⟨function, frame, outcome, admitted, started, executed⟩ := defined
  rw [behaviors_singleton context started executed] at member
  have same : behavior = outcome.behavior := member
  subst behavior
  cases outcome <;> simp [Validation.Finite.Outcome.behavior]

/-- The exact existing optimizeWith is closed on this domain for cleanup-off
configurations, respecting the real localSSA flag. -/
theorem optimizeWith_defined (context : Context) (cfg : Config) (cleanup : NoCleanup cfg)
    {units : Array Mir.Unit} (defined : Defined context units) :
    Defined context (optimizeWith cfg units) := by
  cases enabled : cfg.localSSA with
  | false =>
    rw [Validation.Finite.optimizeWith_identity cfg units enabled cleanup.constantPropagation
      cleanup.commonSubexpressions cleanup.deadCode cleanup.jumpThreading]
    exact defined
  | true =>
    rw [Validation.Finite.optimizeWith_versionUnits cfg units enabled cleanup.constantPropagation
      cleanup.commonSubexpressions cleanup.deadCode cleanup.jumpThreading]
    exact versionUnits_defined context cfg defined

/-- Complete actual behavior equality for the existing compiler in this
configuration, including its disabled localSSA identity path. -/
theorem optimizeWith_behaviors (context : Context) (cfg : Config) (cleanup : NoCleanup cfg)
    {units : Array Mir.Unit} (defined : Defined context units) :
    behaviors context units = behaviors context (optimizeWith cfg units) := by
  cases enabled : cfg.localSSA with
  | false =>
    rw [Validation.Finite.optimizeWith_identity cfg units enabled cleanup.constantPropagation
      cleanup.commonSubexpressions cleanup.deadCode cleanup.jumpThreading]
  | true =>
    rw [Validation.Finite.optimizeWith_versionUnits cfg units enabled cleanup.constantPropagation
      cleanup.commonSubexpressions cleanup.deadCode cleanup.jumpThreading]
    exact versionUnits_behaviors context cfg defined

/-- Add only subtype proof fields to the exact real total compiler function. -/
def run (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context) :
    Program context :=
  ⟨optimizeWith cfg source.val, optimizeWith_defined context cfg cleanup source.property⟩

theorem run_value (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context) :
    (run context cfg cleanup source).val = optimizeWith cfg source.val := rfl

theorem run_versionUnits (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context)
    (enabled : cfg.localSSA = true) :
    (run context cfg cleanup source).val = Validation.Finite.versionUnits cfg source.val :=
  Validation.Finite.optimizeWith_versionUnits cfg source.val enabled cleanup.constantPropagation
    cleanup.commonSubexpressions cleanup.deadCode cleanup.jumpThreading

theorem run_identity (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context)
    (disabled : cfg.localSSA = false) : run context cfg cleanup source = source := by
  apply Subtype.ext
  exact Validation.Finite.optimizeWith_identity cfg source.val disabled cleanup.constantPropagation
    cleanup.commonSubexpressions cleanup.deadCode cleanup.jumpThreading

theorem run_behaviors (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context) :
    (language context).beh source = (language context).beh (run context cfg cleanup source) :=
  optimizeWith_behaviors context cfg cleanup source.property

/-- The exact total compiler is exposed through the existing partial-pass API
as always successful, without a new runtime acceptance test or fallback. -/
def pass (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) : Category.Pass (𝟙 (language context)) where
  run source := some (run context cfg cleanup source)
  sound source candidate selected := by
    have same : run context cfg cleanup source = candidate := Option.some.inj selected
    subst candidate
    exact (Category.valid_id_iff _ _).mpr ⟨rfl, (run_behaviors context cfg cleanup source).symm.subset⟩

theorem pass_run_value (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context) :
    ((pass context cfg cleanup).run source).map (fun program : Program context => program.val) =
      some (optimizeWith cfg source.val) := rfl

def compiler (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) :=
  (pass context cfg cleanup).toCompiler

def endoPass (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) : Category.EndoPass (language context) :=
  Category.EndoPass.ofPass (pass context cfg cleanup)

theorem endoPass_run (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context) :
    (endoPass context cfg cleanup).run source = run context cfg cleanup source := rfl

/-- Satisfaction equivalence uses the complete actual machine behavior sets. -/
theorem run_room_sat (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context)
    (specification : Set Lir.Behavior) :
    ((language context).room ()).Sat ((language context).beh source) specification ↔
      ((language context).room ()).Sat ((language context).beh (run context cfg cleanup source)) specification := by
  change (language context).beh source ⊆ specification ↔ (language context).beh (run context cfg cleanup source) ⊆ specification
  rw [run_behaviors context cfg cleanup source]

theorem run_sat (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context)
    (specification : Set Lir.Behavior) :
    (language context).Sat source specification ↔ (language context).Sat (run context cfg cleanup source) specification :=
  run_room_sat context cfg cleanup source specification

namespace Hets
open Silmaril.Logic.Institution

theorem run_readback_models (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context) :
    (((graph context).comor Translation.optimize).ρ.app (Discrete.mk ())).mod.obj
        ((language context).beh (run context cfg cleanup source)) = (language context).beh source := by
  change _root_.id '' (language context).beh (run context cfg cleanup source) = (language context).beh source
  rw [Set.image_id]
  exact (run_behaviors context cfg cleanup source).symm

theorem run_graph_sat (context : Context) (cfg : Config) (cleanup : NoCleanup cfg) (source : Program context)
    (specification : Set Lir.Behavior) :
    (((graph context).inst Node.source).I.obj (Discrete.mk ())).Sat ((language context).beh source) specification ↔
      (((graph context).inst Node.optimized).I.obj (Discrete.mk ())).Sat
        ((language context).beh (run context cfg cleanup source))
        ((((graph context).comor Translation.optimize).ρ.app (Discrete.mk ())).sen specification) := by
  have condition := (((graph context).comor Translation.optimize).ρ.app (Discrete.mk ())).sat
    ((language context).beh (run context cfg cleanup source)) specification
  rw [run_readback_models context cfg cleanup source] at condition
  exact condition.symm

theorem optimizerPath_comorphism (context : Context) :
    IndexedCoInst.coHom (graph context).indexed ((graph context).pathHom (optimizerPath context)) =
      (graph context).comor Translation.optimize :=
  (graph context).coHom_toPath Translation.optimize

end Hets
end Silmaril.Compiler.Native.Optimize.FiniteInstitution
