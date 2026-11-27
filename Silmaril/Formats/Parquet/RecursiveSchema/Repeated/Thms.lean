module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs
import Silmaril.Formats.Parquet.Footer.NestedLeaf.Thms
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Binding
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Levels

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated

open RecursiveSchema (Entry Location entries RepetitionWire Unannotated)

@[expose] public section

theorem Source.bytes_exact {limits : Snapshot.Limits} {bytes : Bytes} (source : Source limits bytes) :
    source.snapshot.bytes = bytes :=
  (Snapshot.checkRecursive_exact source.original).2.1

/-- The staged grammar owns the exact typed and raw preorder schema vector. -/
theorem Compiled.original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) :
    Footer.NestedLeaf.ItemsWire limits.footer snapshot schema.container schema.items ∧
      RootWire (Footer.ColumnOrder.footerReader limits.footer snapshot) (entries snapshot schema.items)
        (limits.maxSchemaDepth - 1) schema.root schema.fields :=
  ⟨Footer.NestedLeaf.readItems_wire schema.originalItems, schema.grammar⟩

theorem Compiled.leaf_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf}
    (selected : schema.leaves[column]? = some plan) :
    ∃ entry : Entry, snapshot.metadata.schema[plan.site.location.ordinal]? = some entry.1 ∧
      schema.items[plan.site.location.ordinal]? = some entry.2 ∧ plan.site.name = entry.1.name ∧
      RepetitionWire entry plan.site.nullable ∧ Unannotated entry ∧
      entry.1.physicalType = some plan.kind.physical :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.leaf_original schema selected

/-- Each definition step binds its original optional item or annotated
LIST and repeated wrapper. The unique repeated step also binds its index. -/
theorem Compiled.steps_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf}
    (selected : schema.leaves[column]? = some plan) :
    StepsWire (Footer.ColumnOrder.footerReader limits.footer snapshot) (entries snapshot schema.items)
      plan.site.location.path plan.steps plan.repeated :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.steps_original schema selected

theorem Leaf.maxRepetition_original {reader : ThriftCompact.Traversal.Reader}
    {original : Array Entry} {plan : Leaf}
    (wire : StepsWire reader original plan.site.location.path plan.steps plan.repeated) :
    plan.maxRepetition = (plan.steps.filterMap Step.wrapper?).length := by
  rw [wire.wrappers]
  cases repeated : plan.repeated <;> simp [Leaf.maxRepetition, repeated]

theorem StepWire.list_annotation {reader : ThriftCompact.Traversal.Reader}
    {original : Array Entry} {path : List String} {outer wrapper : Location}
    (wire : StepWire reader original path (.emptyList outer wrapper)) :
    ∃ entry, NamedAt original outer entry ∧ ListFile.AnnotationWire reader entry.2 := by
  cases wire with
  | emptyList atOuter _ _ checked _ _ _ _ => exact ⟨_, atOuter, ListFile.checkList_wire checked⟩

theorem Leaf.classify_absent {plan : Leaf} {slot level : Nat} {step : Step} :
    plan.classifyDefinition slot level = .ok (.absent step) ↔ plan.steps[level]? = some step :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.classify_absent

theorem Compiled.classified_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column slot level : Nat} {plan : Leaf} {step : Step}
    (selected : schema.leaves[column]? = some plan)
    (classified : plan.classifyDefinition slot level = .ok (.absent step)) :
    StepWire (Footer.ColumnOrder.footerReader limits.footer snapshot) (entries snapshot schema.items)
      plan.site.location.path step :=
  (schema.steps_original selected).original step (List.mem_of_getElem? (Leaf.classify_absent.mp classified))

theorem Leaf.classify_value {plan : Leaf} {slot level : Nat} :
    plan.classifyDefinition slot level = .ok .value ↔ level = plan.maxDefinition :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.classify_value

/-- Repetition 1 is locally admissible only after the original empty-list level. -/
theorem Leaf.classify_continuation {plan : Leaf} {boundary : Boundary} {slot level : Nat}
    (repeated : plan.repeated = some boundary) :
    plan.classify slot 1 level =
      (plan.classifyDefinition slot level).bind (fun presence =>
        if boundary.emptyLevel < level then .ok ⟨.continuation, presence⟩
        else .error (.continuation plan.site.location slot level)) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.classify_continuation repeated

theorem Leaf.classify_nonRepeated (plan : RecursiveSchema.Leaf) (slot level : Nat) :
    (Leaf.ofNonRepeated plan).classify slot 0 level =
      ((plan.classify slot level).mapError (fun
        | .level source index actual maximum => LevelError.definition source index actual maximum)).map
        (fun
          | .absent source => ⟨.rowStart, .absent (.optional source .node)⟩
          | .value => ⟨.rowStart, .value⟩) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.classify_nonRepeated plan slot level

/-- The standalone nullable INT32 LIST events use the same local levels and
row-start/continuation boundary as their recursive counterparts. -/
theorem Leaf.standalone_nullable (outer wrapper : Location) (plan : Leaf) (slot : Nat)
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
        ⟨.continuation, if item.isSome then .value else .absent (.optional plan.site.location .element)⟩) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.standalone_nullable outer wrapper plan slot
    boundary steps event

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated
