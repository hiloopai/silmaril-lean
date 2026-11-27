module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema (Location)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated

public theorem classify_absent {plan : Leaf} {slot level : Nat} {step : Step} :
    plan.classifyDefinition slot level = .ok (.absent step) ↔ plan.steps[level]? = some step := by
  by_cases full : level = plan.maxDefinition
  · simp [Leaf.classifyDefinition, full, Leaf.maxDefinition]
  · cases found : plan.steps[level]? <;> simp [Leaf.classifyDefinition, full, found]

public theorem classify_value {plan : Leaf} {slot level : Nat} :
    plan.classifyDefinition slot level = .ok .value ↔ level = plan.maxDefinition := by
  by_cases full : level = plan.maxDefinition
  · simp [Leaf.classifyDefinition, full]
  · cases found : plan.steps[level]? <;> simp [Leaf.classifyDefinition, full, found]

public theorem classify_continuation {plan : Leaf} {boundary : Boundary} {slot level : Nat}
    (repeated : plan.repeated = some boundary) :
    plan.classify slot 1 level =
      (plan.classifyDefinition slot level).bind (fun presence =>
        if boundary.emptyLevel < level then .ok ⟨.continuation, presence⟩
        else .error (.continuation plan.site.location slot level)) := by
  simp [Leaf.classify, Leaf.maxRepetition, repeated, bind, Except.bind, pure, Except.pure]

public theorem classify_nonRepeated (plan : RecursiveSchema.Leaf) (slot level : Nat) :
    (Leaf.ofNonRepeated plan).classify slot 0 level =
      ((plan.classify slot level).mapError (fun
        | .level source index actual maximum => LevelError.definition source index actual maximum)).map
        (fun
          | .absent source => ⟨.rowStart, .absent (.optional source .node)⟩
          | .value => ⟨.rowStart, .value⟩) := by
  by_cases full : level = plan.maxDefinition
  · simp [Leaf.classify, Leaf.classifyDefinition, Leaf.ofNonRepeated, Leaf.maxDefinition,
      Leaf.maxRepetition, RecursiveSchema.Leaf.classify, RecursiveSchema.Leaf.maxDefinition,
      bind, Except.bind, pure, Except.pure, Except.map, Except.mapError,
      RecursiveSchema.Leaf.maxDefinition] at full ⊢
    simp [full]
  · cases found : plan.optional[level]? <;>
      simp [Leaf.classify, Leaf.classifyDefinition, Leaf.ofNonRepeated, Leaf.maxDefinition,
        Leaf.maxRepetition, RecursiveSchema.Leaf.classify, RecursiveSchema.Leaf.maxDefinition,
        List.getElem?_map, found, bind, Except.bind, pure, Except.pure, Except.map, Except.mapError,
        show level ≠ plan.optional.length from full]

public theorem standalone_nullable (outer wrapper : Location) (plan : Leaf) (slot : Nat)
    (boundary : plan.repeated = some ⟨outer, wrapper, 1⟩)
    (steps : plan.steps =
      [.optional outer .list, .emptyList outer wrapper, .optional plan.site.location .element])
    (event : ListPage.Event) :
    plan.classify slot event.wire.1 event.wire.2.1 = .ok (match event with
      | .nullList => ⟨.rowStart, .absent (.optional outer .list)⟩
      | .emptyList => ⟨.rowStart, .absent (.emptyList outer wrapper)⟩
      | .first item =>
        ⟨.rowStart, if item.isSome then .value else .absent (.optional plan.site.location .element)⟩
      | .next item =>
        ⟨.continuation, if item.isSome then .value else .absent (.optional plan.site.location .element)⟩) := by
  cases event with
  | nullList | emptyList =>
    simp [Leaf.classify, Leaf.maxRepetition, Leaf.classifyDefinition, Leaf.maxDefinition, ListPage.Event.wire,
      steps, boundary, bind, Except.bind, pure, Except.pure]
  | first item | next item =>
    cases item <;>
      simp [Leaf.classify, Leaf.maxRepetition, Leaf.classifyDefinition, Leaf.maxDefinition, ListPage.Event.wire,
        steps, boundary, bind, Except.bind, pure, Except.pure]

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated
