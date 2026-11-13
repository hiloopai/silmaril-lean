module

public import Silmaril.Compiler.Native.Correctness.Institution.Defs
public import Silmaril.Compiler.Native.Correctness.Thms
public import Silmaril.Compiler.Category.Cerberus.Process.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.Institution

open Silmaril.Cerberus
namespace Process
export Silmaril.Compiler.Category.Cerberus.Process
  (model Observes coreUB_iff_realises_ub coreBeh_iff_realises_observes)
end Process

/-- The institution projection is the exact fixed process observation of the
same Core startup, including the source-UB escape and genuine divergence. -/
theorem project_model_iff_allowed (doc : Codec.Document) (arguments : List String)
    (initial : Silmaril.Cerberus.Core.Dynamics.State) (labels : Silmaril.Cerberus.Core.Dynamics.Labels)
    (start : Silmaril.Compile.Core.Spec.coreStart doc arguments = .ok (initial, labels))
    (observation : Observation) :
    observation ∈ project (Process.model doc initial labels) ↔
      (Silmaril.Compile.Core.Spec.CoreUB doc arguments ∨
        Silmaril.Compile.Core.Spec.CoreBeh doc arguments (observe observation)) := by
  constructor
  · rintro ⟨behavior, realised, matching⟩
    rcases matching with ub | observed
    · cases behavior with
      | finite actions state =>
        obtain ⟨location, reason, halt⟩ := ub
        exact .inl ((Process.coreUB_iff_realises_ub doc arguments initial labels start).2
          ⟨actions, state, location, reason, realised, halt⟩)
      | infinite states actions => exact ub.elim
    · exact .inr ((Process.coreBeh_iff_realises_observes doc arguments initial labels start _).2
        ⟨behavior, realised, observed⟩)
  · rintro (ub | observed)
    · obtain ⟨actions, state, location, reason, realised, halt⟩ :=
        (Process.coreUB_iff_realises_ub doc arguments initial labels start).1 ub
      exact ⟨.finite actions state, realised, .inl ⟨location, reason, halt⟩⟩
    · obtain ⟨behavior, realised, matching⟩ :=
        (Process.coreBeh_iff_realises_observes doc arguments initial labels start _).1 observed
      exact ⟨behavior, realised, .inr matching⟩

/-- Successful actual source elaboration/startup identifies the graph's
projected operational model with the Driver-tied source behavior language.
Source coverage on the independently selected domain remains a separate
obligation; this equation does not prove native implementation refinement. -/
theorem project_eq_sourceBehaviors {source : Source} {model : Core.Model}
    (elaborated : Elaborates source model) : project model = sourceBehaviors source := by
  obtain ⟨bindings, accepted, file, startup⟩ :
      ∃ bindings, elaborate source = .ok bindings ∧
        model.program = bindings.toFile ∧
        Silmaril.Cerberus.Core.Dynamics.initial model.program
          (Map.ofList source.enumBindings) source.arguments =
            .ok (model.initialState, model.labels) := elaborated
  have start : Silmaril.Compile.Core.Spec.coreStart (document source bindings) source.arguments =
      .ok (model.initialState, model.labels) := by
    simpa [Silmaril.Compile.Core.Spec.coreStart, document, file] using startup
  have model_eq : model =
      Process.model (document source bindings) model.initialState model.labels := by
    cases model with
    | mk program labels initial =>
      exact congrArg (fun program => Silmaril.Cerberus.Institution.Model.mk program labels initial) file
  apply Set.ext
  intro observation
  show observation ∈ project model ↔ observation ∈ sourceBehaviors source
  have operational : observation ∈ project model ↔
      (Silmaril.Compile.Core.Spec.CoreUB (document source bindings) source.arguments ∨
        Silmaril.Compile.Core.Spec.CoreBeh (document source bindings) source.arguments
          (observe observation)) := by
    rw [model_eq]
    exact project_model_iff_allowed (document source bindings) source.arguments
      model.initialState model.labels start observation
  constructor
  · intro realised
    have allowed : Silmaril.Compile.Core.Spec.CoreUB (document source bindings) source.arguments ∨
        Silmaril.Compile.Core.Spec.CoreBeh (document source bindings) source.arguments
          (observe observation) := operational.mp realised
    exact ⟨bindings, accepted, allowed⟩
  · rintro ⟨otherBindings, otherAccepted, allowed⟩
    have same : otherBindings = bindings := Except.ok.inj (otherAccepted.symm.trans accepted)
    have canonical : Silmaril.Compile.Core.Spec.CoreUB (document source bindings) source.arguments ∨
        Silmaril.Compile.Core.Spec.CoreBeh (document source bindings) source.arguments
          (observe observation) := by
      simpa only [same] using allowed
    exact operational.mpr canonical

theorem satisfies_sentence_iff (model : Core.Model) (specification : Set Observation) :
    Core.Satisfies model (sentence specification) ↔ project model ⊆ specification := by
  constructor
  · intro satisfied observation ⟨behavior, realised, matching⟩
    exact satisfied behavior realised observation matching
  · intro satisfied behavior realised observation matching
    exact satisfied ⟨behavior, realised, matching⟩

/-- The actual compile result preserves projected process specifications only
after its actual semantic refinement obligation has been discharged. -/
theorem preserves_projected_specification (domain : Source → Prop) (toolchain : Toolchain domain)
    (refinement : Task.machineRefinement domain toolchain) {source : Program domain} {target : Target}
    (accepted : run source = some target) {specification : Set Observation}
    (satisfied : (sourceLanguage domain).Sat source specification) :
    (targetLanguage toolchain).Sat target specification := by
  intro observation behavior
  exact satisfied (refinement source target accepted behavior)

end Silmaril.Compiler.Native.Correctness.Institution
