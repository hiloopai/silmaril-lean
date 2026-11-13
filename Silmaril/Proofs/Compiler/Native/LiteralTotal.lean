module

public import Silmaril.Compiler.Native.Correctness.LiteralTotal.Defs
public import Silmaril.Compiler.Native.Correctness.Literal.Thms
public import Silmaril.Compiler.Native.Correctness.Hets.Thms
public import Silmaril.Compiler.Core.ElaborationTotal.Thms
/-! Connect the actual native Source record to universal actual-Core meaning.
This reuses the exact Functions output, enum registry, metadata and arguments;
it is neither an independent Ail semantics nor a native compiler pass proof. -/

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralTotal
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Silmaril.Compiler.Core

namespace Core
export Silmaril.Cerberus.Institution (Model Satisfies)
end Core
namespace Process
export Silmaril.Compiler.Category.Cerberus.Process (model coreUB_iff_realises_ub)
end Process

/-- Runtime recognition strengthens the earlier source-coverage domain. -/
theorem domain_elaborationDomain {number : Int} {source : Source}
    (admitted : domain number source) : Literal.elaborationDomain source := by
  obtain ⟨literal, _, shape, available, bounds, conversion, resultType, parameters, body,
    found, _⟩ := admitted
  exact ⟨literal, shape, available, bounds, conversion, resultType, parameters, body, found⟩

/-- For actual admitted Source inputs, elaboration and startup succeed and the
resulting genuine Core model satisfies the universal integer-return sentence.
Its exact projected observations are derived, including exclusion of source UB.
No compiler success, completed behavior or semantic safety premise is supplied. -/
theorem actual_model {number : Int} {source : Source} (admitted : domain number source) :
    ∃ model : Core.Model, Elaborates source model ∧
      Core.Satisfies model (ElaborationTotal.returnsInteger number) ∧
      ∀ observation, observation ∈ sourceBehaviors source ↔ observation ∈ specification number := by
  obtain ⟨literal, number_eq, shape, available, bounds, conversion, resultType, parameters, body,
    found, recognized⟩ := admitted
  obtain ⟨start, labels, elaborated, started, correct, exactBehavior⟩ :=
    ElaborationTotal.literal_total source.elaboration.config source.types
      source.elaboration.runtime literal source.elaboration.freshness available
      conversion resultType parameters body found recognized bounds
      source.commit source.implementation (some source.enumBindings) source.arguments
  let bindings := literal.bindings source.elaboration.runtime source.elaboration.freshness conversion
  let model := Process.model (document source bindings) start labels
  have accepted : elaborate source = .ok bindings := by
    unfold elaborate
    rw [shape]
    exact congrArg Prod.fst elaborated
  have startup : Silmaril.Compile.Core.Spec.coreStart (document source bindings) source.arguments =
      .ok (start, labels) := started
  have universal : Core.Satisfies model (ElaborationTotal.returnsInteger number) := by
    simpa only [model, Process.model, document, ElaborationProcess.document, bindings, number_eq] using correct
  have actual : Elaborates source model := by
    refine ⟨bindings, accepted, rfl, ?_⟩
    simpa [Silmaril.Compile.Core.Spec.coreStart, document, model, Process.model] using startup
  have noUB : ¬ Silmaril.Compile.Core.Spec.CoreUB (document source bindings) source.arguments := by
    intro undefined
    obtain ⟨actions, state, location, reason, realised, halted⟩ :=
      (Process.coreUB_iff_realises_ub (document source bindings) source.arguments
        start labels startup).1 undefined
    have impossible := (universal (.finite actions state) realised (.ub location reason) halted).1
    cases impossible
  refine ⟨model, actual, universal, ?_⟩
  intro observation
  rw [sourceBehaviors_iff accepted]
  have completed : Silmaril.Compile.Core.Spec.CoreBeh (document source bindings)
      source.arguments (observe observation) ↔ observation ∈ specification number := by
    simpa only [specification, Set.mem_ofPred_eq, expectedExit, number_eq, document,
      ElaborationProcess.document, bindings] using exactBehavior (observe observation)
  constructor
  · rintro (undefined | behavior)
    · exact (noUB undefined).elim
    · exact completed.1 behavior
  · intro expected
    exact .inr (completed.2 expected)

/-- Exact source meaning in the existing native contract: stopped outcomes and
divergence cannot be introduced through UB or failed startup on this domain. -/
theorem sourceBehaviors_iff_exit {number : Int} {source : Source}
    (admitted : domain number source) (observation : Observation) :
    observation ∈ sourceBehaviors source ↔ observe observation = expectedExit number := by
  obtain ⟨_, _, _, exactBehavior⟩ := actual_model admitted
  exact exactBehavior observation

/-- The actual same Core model satisfies the fixed projected-institution
sentence as well as the stronger full-Core integer-return sentence. -/
theorem projected_model {number : Int} {source : Source} (admitted : domain number source) :
    ∃ model : Core.Model, Elaborates source model ∧
      Core.Satisfies model (ElaborationTotal.returnsInteger number) ∧
      Core.Satisfies model (Institution.sentence (specification number)) := by
  obtain ⟨model, elaborated, correct, exactBehavior⟩ := actual_model admitted
  refine ⟨model, elaborated, correct, (Institution.satisfies_sentence_iff _ _).2 ?_⟩
  rw [Institution.project_eq_sourceBehaviors elaborated]
  intro observation behavior
  exact (exactBehavior observation).1 behavior

/-- Every admitted whole program satisfies the sentence in the exact native
source language; this proves no target-machine or native pass result. -/
theorem satisfies {number : Int} (source : Program (domain number)) :
    (sourceLanguage (domain number)).Sat source (specification number) := by
  intro observation behavior
  exact (sourceBehaviors_iff_exit source.property.1 observation).1 behavior

/-- The Hets projectedCore node is exactly this source institution. A toolchain
is needed only to select the existing graph, never as a semantic premise. -/
theorem satisfies_hets {number : Int} (source : Program (domain number))
    (toolchain : Toolchain (domain number)) :
    ((((Hets.graph (domain number) toolchain).inst Hets.Node.projectedCore).I.obj
      (CategoryTheory.Discrete.mk PUnit.unit))).Sat
        (sourceBehaviors source.val) (specification number) :=
  satisfies source

end Silmaril.Compiler.Native.Correctness.LiteralTotal
