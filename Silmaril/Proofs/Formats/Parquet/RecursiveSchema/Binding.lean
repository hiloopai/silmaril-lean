module

public import Silmaril.Formats.Parquet.RecursiveSchema.Defs

@[expose] public section

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema

theorem entry_binding {snapshot : Snapshot.Checked} {items : List Footer.ColumnOrder.Item}
    {ordinal : Nat} {entry : Entry} (found : (entries snapshot items)[ordinal]? = some entry) :
    snapshot.metadata.schema[ordinal]? = some entry.1 ∧ items[ordinal]? = some entry.2 := by
  apply List.getElem?_zip_eq_some.mp
  simpa [entries] using found

private def OptionalWire (original : Array Entry) (path : List String)
    (positions : List Location) : Prop :=
  ∀ position ∈ positions, ∃ entry, original[position.ordinal]? = some entry ∧
    entry.1.repetition = some .optional ∧ position.path <+: path

private theorem enter_optional {original : Array Entry} {ctx : Context} {ordinal : Nat}
    {entry : Entry} {nullable : Bool} (found : original[ordinal]? = some entry)
    (repetition : RepetitionWire entry nullable) (prior : OptionalWire original ctx.path ctx.optional) :
    let site := ctx.site ordinal entry.1.name nullable
    OptionalWire original site.location.path (ctx.enter site).optional := by
  intro site position member
  have earlier (member : position ∈ ctx.optional) :
      ∃ entry, original[position.ordinal]? = some entry ∧
        entry.1.repetition = some .optional ∧ position.path <+: site.location.path := by
    obtain ⟨entry, hit, optional, before⟩ := prior position member
    exact ⟨entry, hit, optional, List.prefix_append_of_prefix before⟩
  cases nullable with
  | false => exact earlier member
  | true =>
    change position ∈ ctx.optional ++ [site.location] at member
    rcases List.mem_append.mp member with previous | here
    · exact earlier previous
    · obtain rfl := List.mem_singleton.mp here
      exact ⟨entry, found, repetition, List.prefix_rfl⟩

private def LeafInput (original : Array Entry) (plan : Leaf) : Prop :=
  (∃ entry, original[plan.site.location.ordinal]? = some entry ∧
    plan.site.name = entry.1.name ∧ entry.1.physicalType = some plan.kind.physical ∧
    RepetitionWire entry plan.site.nullable ∧ Unannotated entry) ∧
  OptionalWire original plan.site.location.path plan.optional

private theorem fields_leaf_input {original : Array Entry} {depth count ordinal next : Nat}
    {ctx : Context} {fields : List Field} (wire : FieldsWire original depth ctx count ordinal fields next) :
    OptionalWire original ctx.path ctx.optional →
      ∀ plan ∈ fields.flatMap Field.leaves, LeafInput original plan := by
  apply FieldsWire.rec
    (motive_1 := fun _ ctx _ field _ _ => OptionalWire original ctx.path ctx.optional →
      ∀ plan ∈ field.leaves, LeafInput original plan)
    (motive_2 := fun _ ctx _ _ fields _ _ => OptionalWire original ctx.path ctx.optional →
      ∀ plan ∈ fields.flatMap Field.leaves, LeafInput original plan)
    (t := wire)
  · intro _ _ _ entry _ _ found unannotated repetition _ physical _ prior plan member
    simp only [Field.leaves, List.mem_singleton] at member
    subst plan
    exact ⟨⟨entry, found, rfl, physical, repetition, unannotated⟩, enter_optional found repetition prior⟩
  · intro _ _ _ _ _ _ _ _ found _ repetition _ _ _ _ _ childInput prior plan member
    exact childInput (enter_optional found repetition prior) plan (by simpa only [Field.leaves] using member)
  · intro _ _ _ _ _ member
    simp at member
  · intro _ _ _ _ _ _ _ _ _ _ firstInput restInput prior plan member
    rcases List.mem_append.mp member with here | later
    · exact firstInput prior plan here
    · exact restInput prior plan later

private theorem leaf_input {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf}
    (selected : schema.leaves[column]? = some plan) :
    LeafInput (entries snapshot schema.items) plan := by
  have member : plan ∈ schema.fields.flatMap Field.leaves := by
    rw [schema.ordered] at selected
    exact List.mem_of_getElem? (by simpa using selected)
  obtain ⟨_, _, _, grammar⟩ := schema.grammar.children
  exact fields_leaf_input grammar (by simp [OptionalWire]) plan member

theorem leaf_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf}
    (selected : schema.leaves[column]? = some plan) :
    ∃ entry, snapshot.metadata.schema[plan.site.location.ordinal]? = some entry.1 ∧
      schema.items[plan.site.location.ordinal]? = some entry.2 ∧
      plan.site.name = entry.1.name ∧ entry.1.physicalType = some plan.kind.physical ∧
      RepetitionWire entry plan.site.nullable ∧ Unannotated entry := by
  obtain ⟨entry, selected, rest⟩ := (leaf_input schema selected).1
  obtain ⟨element, item⟩ := entry_binding selected
  exact ⟨entry, element, item, rest⟩

theorem optional_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf} {position : Location}
    (selected : schema.leaves[column]? = some plan) (member : position ∈ plan.optional) :
    ∃ entry : Entry, snapshot.metadata.schema[position.ordinal]? = some entry.1 ∧
      schema.items[position.ordinal]? = some entry.2 ∧
      entry.1.repetition = some .optional ∧ position.path <+: plan.site.location.path := by
  obtain ⟨entry, selected, rest⟩ := (leaf_input schema selected).2 position member
  obtain ⟨element, item⟩ := entry_binding selected
  exact ⟨entry, element, item, rest⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema
