module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Compiler
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Ancestry

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree

open RecursiveSchema (Entry Location)
open Repeated (Absence Boundary)

public section

/-- Every original declaration after the root occurs exactly in physical
preorder, with its original typed item and raw footer field. -/
theorem Compiled.original_nodes {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) :
    compiled.declarations.map (·.location.ordinal) = List.range' 1 (snapshot.metadata.schema.length - 1) ∧
    ∀ node ∈ compiled.declarations, ∃ entry : Entry,
      snapshot.metadata.schema[node.location.ordinal]? = some entry.1 ∧
      compiled.schema.items[node.location.ordinal]? = some entry.2 ∧
      entry.1.physicalType = node.physical :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.original_nodes compiled

theorem Compiled.leaf_order {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) :
    compiled.leaves.toList.map (·.path) = compiled.declarations.filterMap Node.leaf? :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.leaf_order compiled

theorem Compiled.leaf_ordinals_increase {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) :
    (compiled.leaves.toList.map (·.path)).Pairwise
      (fun left right => left.site.location.ordinal < right.site.location.ordinal) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.leaf_ordinals_increase compiled

theorem Compiled.leaf_column {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {column : Nat} {plan : LeafPlan}
    (selected : compiled.leaves[column]? = some plan) :
    plan.column = column ∧ (compiled.declarations.filterMap Node.leaf?)[column]? = some plan.path :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.leaf_column compiled selected

theorem Compiled.leaf_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {column : Nat} {plan : LeafPlan}
    (selected : compiled.leaves[column]? = some plan) :
    ∃ entry : Entry, snapshot.metadata.schema[plan.path.site.location.ordinal]? = some entry.1 ∧
      compiled.schema.items[plan.path.site.location.ordinal]? = some entry.2 ∧
      entry.1.physicalType = some plan.path.kind.physical :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.leaf_original compiled selected

theorem Compiled.leaf_coverage {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {ordinal : Nat} {entry : Footer.SchemaElement}
    (hit : snapshot.metadata.schema[ordinal]? = some entry) (physical : entry.physicalType.isSome = true) :
    ∃ plan ∈ compiled.leaves.toList,
      plan.path.site.location.ordinal = ordinal ∧ some plan.path.kind.physical = entry.physicalType :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.leaf_coverage compiled hit physical

theorem Compiled.distinct_ordinals {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) : (compiled.declarations.map (·.location.ordinal)).Nodup :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.distinct_ordinals compiled

/-- Two distinct declarations, including siblings with equal display names,
have different original ordinal identities. -/
theorem Compiled.same_ordinal {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {first last : Node}
    (left : first ∈ compiled.declarations) (right : last ∈ compiled.declarations)
    (equal : first.location.ordinal = last.location.ordinal) : first = last :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.same_ordinal compiled left right equal

/-- Sharing an original ancestor fixes both its ancestry prefix and all
definition steps through that ancestor. Descendant steps may differ. -/
theorem Compiled.shared_ancestor {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {i j left right : Nat} {lhs rhs : LeafPlan}
    {a b : Ancestor} (first : compiled.leaves[left]? = some lhs) (last : compiled.leaves[right]? = some rhs)
    (atLeft : lhs.path.ancestors[i]? = some a) (atRight : rhs.path.ancestors[j]? = some b)
    (shared : a.site.location.ordinal = b.site.location.ordinal) :
    a = b ∧ i = j ∧ lhs.path.ancestors.take i = rhs.path.ancestors.take j ∧
      lhs.path.ancestorSteps (i + 1) = rhs.path.ancestorSteps (j + 1) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.shared_ancestor compiled first last atLeft atRight shared

theorem LeafPath.steps_prefix (path : LeafPath) (count : Nat) : path.ancestorSteps count <+: path.steps :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.steps_prefix path count

theorem LeafPath.nullable_level {path : LeafPath} {site : Location} {role : Absence} {level : Nat}
    (member : (site, role, level) ∈ path.nullable) :
    path.steps[level]? = some (.optional site role) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.nullable_level member

theorem LeafPath.repeated_level {path : LeafPath} {boundary : Boundary} (member : boundary ∈ path.repeated) :
    path.steps[boundary.emptyLevel]? = some (.emptyList boundary.outer boundary.wrapper) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.repeated_level member

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree
