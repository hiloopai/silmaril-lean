module

public import Silmaril.Formats.Parquet.RecursiveSchema.Defs
import Silmaril.Formats.Parquet.Footer.NestedLeaf.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Binding
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Levels

@[expose] public section

namespace Silmaril.Formats.Parquet.RecursiveSchema

/-- The compiled grammar combines the original raw schema structs with the
typed schema at the same ordinals, including the original requested depth. -/
theorem Compiled.original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) :
    Footer.NestedLeaf.ItemsWire limits.footer snapshot schema.container schema.items ∧
      RootWire (entries snapshot schema.items) (limits.maxSchemaDepth - 1) schema.root schema.fields :=
  ⟨Footer.NestedLeaf.readItems_wire schema.originalItems, schema.grammar⟩

theorem entry_binding {snapshot : Snapshot.Checked} {items : List Footer.ColumnOrder.Item}
    {ordinal : Nat} {entry : Entry} (found : (entries snapshot items)[ordinal]? = some entry) :
    snapshot.metadata.schema[ordinal]? = some entry.1 ∧ items[ordinal]? = some entry.2 :=
  Proofs.Formats.Parquet.RecursiveSchema.entry_binding found

/-- The physical column ordinal selects the corresponding original
SchemaElement and raw item, with its original signed type and repetition. -/
theorem Compiled.leaf_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf}
    (selected : schema.leaves[column]? = some plan) :
    ∃ entry, snapshot.metadata.schema[plan.site.location.ordinal]? = some entry.1 ∧
      schema.items[plan.site.location.ordinal]? = some entry.2 ∧
      plan.site.name = entry.1.name ∧ entry.1.physicalType = some plan.kind.physical ∧
      RepetitionWire entry plan.site.nullable ∧ Unannotated entry :=
  Proofs.Formats.Parquet.RecursiveSchema.leaf_original schema selected

/-- Each definition step refers to the original optional declaration at
a prefix of the selected leaf's full path. -/
theorem Compiled.optional_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf} {position : Location}
    (selected : schema.leaves[column]? = some plan) (member : position ∈ plan.optional) :
    ∃ entry : Entry, snapshot.metadata.schema[position.ordinal]? = some entry.1 ∧
      schema.items[position.ordinal]? = some entry.2 ∧
      entry.1.repetition = some .optional ∧ position.path <+: plan.site.location.path :=
  Proofs.Formats.Parquet.RecursiveSchema.optional_original schema selected member

theorem Source.bytes_exact {limits : Snapshot.Limits} {bytes : Bytes} (source : Source limits bytes) :
    source.snapshot.bytes = bytes :=
  Snapshot.check_bytes source.original

theorem Source.groups_exact {limits : Snapshot.Limits} {bytes : Bytes} (source : Source limits bytes) :
    source.snapshot.groupCount = source.snapshot.metadata.rowGroups.length ∧
      ∀ index, source.snapshot.groupAt index = source.snapshot.metadata.rowGroups[index]? :=
  Snapshot.check_groups source.original

theorem Leaf.classify_value {leaf : Leaf} {row level : Nat} :
    leaf.classify row level = .ok .value ↔ level = leaf.maxDefinition :=
  Proofs.Formats.Parquet.RecursiveSchema.classify_value

theorem Leaf.classify_absent {leaf : Leaf} {row level : Nat} {location : Location} :
    leaf.classify row level = .ok (.absent location) ↔ leaf.optional[level]? = some location :=
  Proofs.Formats.Parquet.RecursiveSchema.classify_absent

theorem Leaf.classify_out_of_range {leaf : Leaf} {row level : Nat} (over : leaf.maxDefinition < level) :
    leaf.classify row level = .error (.level leaf.site.location row level leaf.maxDefinition) :=
  Proofs.Formats.Parquet.RecursiveSchema.classify_out_of_range over

theorem Leaf.bitWidth_exact (leaf : Leaf) :
    leaf.maxDefinition < 2^leaf.bitWidth ∧
      (leaf.bitWidth = 0 ∨ 2^(leaf.bitWidth - 1) ≤ leaf.maxDefinition) :=
  Proofs.Formats.Parquet.RecursiveSchema.bitWidth_exact leaf

end Silmaril.Formats.Parquet.RecursiveSchema
