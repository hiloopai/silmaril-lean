module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema (Location Site Entry entries Unannotated RepetitionWire)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated

private theorem step_extend {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader}
    {original : Array Entry} {path next : List String} {step : Step}
    (wire : StepWire reader original path step) (prefixPath : path <+: next) :
    StepWire reader original next step := by
  cases wire with
  | optional hit optional listed prior => exact .optional hit optional listed (prior.trans prefixPath)
  | emptyList outer wrapper shape listTag repeated ordinal name prior =>
    exact .emptyList outer wrapper shape listTag repeated ordinal name (prior.trans prefixPath)

private theorem enter_wire {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader}
    {original : Array Entry} {ctx : Context} {ordinal : Nat} {entry : Entry} {nullable : Bool}
    (item : original[ordinal]? = some entry) (repetition : RepetitionWire entry nullable)
    (prior : StepsWire reader original ctx.path ctx.steps ctx.repeated) :
    let site := ctx.site ordinal entry.1.name nullable
    StepsWire reader original site.location.path (ctx.enter site).steps ctx.repeated := by
  intro site
  have extendsPath : ctx.path <+: site.location.path := List.prefix_append _ _
  cases nullable with
  | false =>
    exact ⟨fun step member => step_extend (prior.original step member) extendsPath,
      prior.wrappers, prior.boundary⟩
  | true =>
    refine ⟨?_, ?_, ?_⟩
    · intro step member
      change step ∈ ctx.steps ++ [.optional site.location ctx.role] at member
      rcases List.mem_append.mp member with previous | current
      · exact step_extend (prior.original step previous) extendsPath
      · obtain rfl := List.mem_singleton.mp current
        refine .optional ⟨item, ctx.path, rfl⟩ repetition ?_ List.prefix_rfl
        intro invalidRole
        unfold Context.role at invalidRole
        split at invalidRole
        · contradiction
        · split at invalidRole <;> contradiction
    · change (ctx.steps ++ [Step.optional site.location ctx.role]).filterMap Step.wrapper? = _
      simpa [List.filterMap_append, List.filterMap_cons, Step.wrapper?] using prior.wrappers
    · intro b stored
      have previous := prior.boundary b stored
      have below := (List.getElem?_eq_some_iff.mp previous).1
      change (ctx.steps ++ [.optional site.location ctx.role])[b.emptyLevel]? = _
      rwa [List.getElem?_append_left below]

private theorem enter_list_wire {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader}
    {original : Array Entry} {ctx : Context} {ordinal : Nat} {entry wrapper : Entry}
    {nullable : Bool} (item : original[ordinal]? = some entry)
    (repetition : RepetitionWire entry nullable) (shape : ListOuter entry)
    (listTag : ListFile.checkList reader entry.2 = .ok ()) (unused : ctx.repeated = none)
    (foundWrapper : original[ordinal + 1]? = some wrapper) (repeated : Wrapper wrapper)
    (prior : StepsWire reader original ctx.path ctx.steps ctx.repeated) :
    let site := ctx.site ordinal entry.1.name nullable
    let child := ctx.enterList site (wrapperAt site ordinal wrapper)
    StepsWire reader original child.path child.steps child.repeated := by
  intro site child
  let physical := wrapperAt site ordinal wrapper
  let steps := if nullable then ctx.steps ++ [.optional site.location .list] else ctx.steps
  change StepsWire reader original physical.path
    (steps ++ [.emptyList site.location physical]) (some ⟨site.location, physical, steps.length⟩)
  have parentToWrapper : site.location.path <+: physical.path := List.prefix_append _ _
  have ancestorToWrapper : ctx.path <+: physical.path :=
    (List.prefix_append ctx.path [entry.1.name]).trans parentToWrapper
  have named : NamedAt original site.location entry := ⟨item, ctx.path, rfl⟩
  have empty : StepWire reader original physical.path (.emptyList site.location physical) :=
    .emptyList named ⟨foundWrapper, site.location.path, rfl⟩ shape listTag repeated
      rfl rfl List.prefix_rfl
  refine ⟨?_, ?_, ?_⟩
  · intro step member
    rcases List.mem_append.mp member with earlier | last
    · cases nullable with
      | false => exact step_extend (prior.original step earlier) ancestorToWrapper
      | true =>
        change step ∈ ctx.steps ++ [.optional site.location .list] at earlier
        rcases List.mem_append.mp earlier with outside | current
        · exact step_extend (prior.original step outside) ancestorToWrapper
        · obtain rfl := List.mem_singleton.mp current
          exact .optional named repetition (fun _ => listTag) parentToWrapper
    · obtain rfl := List.mem_singleton.mp last
      exact empty
  · have noWrapper : ctx.steps.filterMap Step.wrapper? = [] := by
      simpa [unused] using prior.wrappers
    cases nullable <;> simp [steps, List.filterMap_append, List.filterMap_cons, Step.wrapper?, noWrapper]
  · intro b stored
    obtain rfl := Option.some.inj stored
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp

private def LeafWire (reader : Silmaril.Formats.ThriftCompact.Traversal.Reader)
    (original : Array Entry) (plan : Leaf) : Prop :=
  (∃ entry, NamedAt original plan.site.location entry ∧ plan.site.name = entry.1.name ∧
    RepetitionWire entry plan.site.nullable ∧ Unannotated entry ∧
    entry.1.physicalType = some plan.kind.physical) ∧
  StepsWire reader original plan.site.location.path plan.steps plan.repeated

private theorem fields_leaf_wire {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader}
    {original : Array Entry} {depth ctx count ordinal fields next}
    (wire : FieldsWire reader original depth ctx count ordinal fields next) :
    StepsWire reader original ctx.path ctx.steps ctx.repeated →
      ∀ plan ∈ fields.flatMap Field.leaves, LeafWire reader original plan := by
  apply FieldsWire.rec
    (motive_1 := fun _ ctx _ field _ _ => StepsWire reader original ctx.path ctx.steps ctx.repeated →
      ∀ plan ∈ field.leaves, LeafWire reader original plan)
    (motive_2 := fun _ ctx _ _ fields _ _ => StepsWire reader original ctx.path ctx.steps ctx.repeated →
      ∀ plan ∈ fields.flatMap Field.leaves, LeafWire reader original plan)
    (t := wire)
  · intro _ ctx _ entry _ _ item unannotated repetition _ physical _ prior plan member
    simp only [Field.leaves, List.mem_singleton] at member
    subst plan
    exact ⟨⟨entry, ⟨item, ctx.path, rfl⟩, rfl, repetition, unannotated, physical⟩,
      enter_wire item repetition prior⟩
  · intro _ _ _ _ _ _ _ _ item _ repetition _ _ _ _ _ ih prior plan member
    exact ih (enter_wire item repetition prior) plan (by simpa only [Field.leaves] using member)
  · intro _ _ _ _ _ _ _ _ outer repetition shape listTag unused wrapper repeated _ ih prior plan member
    exact ih (enter_list_wire outer repetition shape listTag unused wrapper repeated prior) plan
      (by simpa only [Field.leaves] using member)
  · intro _ _ _ _ _ member
    simp at member
  · intro _ _ _ _ _ _ _ _ _ _ first rest prior plan member
    rcases List.mem_append.mp member with here | later
    · exact first prior plan here
    · exact rest prior plan later

private theorem leaf_wire {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf}
    (selected : schema.leaves[column]? = some plan) :
    LeafWire (Footer.ColumnOrder.footerReader limits.footer snapshot) (entries snapshot schema.items) plan := by
  have member : plan ∈ schema.fields.flatMap Field.leaves := by
    rw [schema.ordered] at selected
    exact List.mem_of_getElem? (by simpa using selected)
  obtain ⟨_, _, _, grammar⟩ := schema.grammar.children
  exact fields_leaf_wire grammar ⟨by simp, rfl, by simp⟩ plan member

public theorem leaf_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf}
    (selected : schema.leaves[column]? = some plan) :
    ∃ entry : Entry, snapshot.metadata.schema[plan.site.location.ordinal]? = some entry.1 ∧
      schema.items[plan.site.location.ordinal]? = some entry.2 ∧ plan.site.name = entry.1.name ∧
      RepetitionWire entry plan.site.nullable ∧ Unannotated entry ∧
      entry.1.physicalType = some plan.kind.physical := by
  obtain ⟨entry, named, rest⟩ := (leaf_wire schema selected).1
  obtain ⟨typed, raw⟩ := RecursiveSchema.entry_binding named.1
  exact ⟨entry, typed, raw, rest⟩

public theorem steps_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {column : Nat} {plan : Leaf}
    (selected : schema.leaves[column]? = some plan) :
    StepsWire (Footer.ColumnOrder.footerReader limits.footer snapshot) (entries snapshot schema.items)
      plan.site.location.path plan.steps plan.repeated :=
  (leaf_wire schema selected).2

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated
