module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema (Entry entries entry_binding)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Context Field FieldWire FieldsWire wrapperAt)
open Silmaril.Formats.Parquet.RecursiveSchema.Tree

private structure Layout (original : Array Entry) (declarations : List Node) (start stop : Nat) : Prop where
  exactStop : start + declarations.length = stop
  ordinals : declarations.map (·.location.ordinal) = List.range' start declarations.length
  physical : ∀ node ∈ declarations, ∃ entry : Entry,
    original[node.location.ordinal]? = some entry ∧ entry.1.physicalType = node.physical

private theorem Layout.single {original : Array Entry} {node : Node} {ordinal : Nat} {entry : Entry}
    (position : node.location.ordinal = ordinal) (item : original[ordinal]? = some entry)
    (physical : entry.1.physicalType = node.physical) : Layout original [node] ordinal (ordinal + 1) :=
  ⟨rfl, by simp [position, List.range'_succ], fun _ member =>
    List.mem_singleton.mp member ▸ ⟨entry, position.symm ▸ item, physical⟩⟩

private theorem Layout.append {original : Array Entry} {left right : List Node} {start middle stop : Nat}
    (lhs : Layout original left start middle) (rhs : Layout original right middle stop) :
    Layout original (left ++ right) start stop := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Nat.add_assoc, ← rhs.exactStop, ← lhs.exactStop]
  · rw [List.map_append, lhs.ordinals, rhs.ordinals, ← lhs.exactStop, List.range'_append_1, List.length_append]
  · intro node member
    rcases List.mem_append.mp member with left | right
    · exact lhs.physical node left
    · exact rhs.physical node right

private theorem layout {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader} {original : Array Entry}
    {depth count start stop : Nat} {ctx : Context} {fields : List Field}
    (wire : FieldsWire reader original depth ctx count start fields stop) (ancestors : List Ancestor) :
    Layout original (fields.flatMap (nodes ancestors)) start stop := by
  revert ancestors
  apply FieldsWire.rec
    (motive_1 := fun _ _ start field stop _ => ∀ ancestors, Layout original (nodes ancestors field) start stop)
    (motive_2 := fun _ _ _ start fields stop _ =>
      ∀ ancestors, Layout original (fields.flatMap (nodes ancestors)) start stop)
    (t := wire)
  · intro _ ctx ordinal entry nullable kind item _ _ _ physical _ ancestors
    simpa only [nodes] using
      Layout.single (ordinal := ordinal) (node := ⟨.signed (ctx.site ordinal entry.1.name nullable) kind, ancestors⟩) rfl item physical
  · intro _ ctx ordinal entry nullable _ _ _ item _ _ _ physical _ _ _ ih ancestors
    let here := Ancestor.struct (ctx.site ordinal entry.1.name nullable)
    simpa only [nodes, here, List.singleton_append] using
      (Layout.single (ordinal := ordinal) (node := ⟨.ancestor here, ancestors⟩) rfl item physical).append (ih (ancestors ++ [here]))
  · intro _ ctx ordinal entry nullable wrapper _ _ item _ shape _ _ wrapperAtOriginal wrapperShape _ ih ancestors
    let site := ctx.site ordinal entry.1.name nullable
    let wrapperSite := wrapperAt site ordinal wrapper
    let here := Ancestor.list site wrapperSite
    simpa only [nodes, here, site, wrapperSite, List.singleton_append] using
      (Layout.single (ordinal := ordinal) (node := ⟨.ancestor here, ancestors⟩) rfl item shape.1).append
        ((Layout.single (ordinal := ordinal + 1) (node := ⟨.wrapper wrapperSite, ancestors ++ [here]⟩) rfl wrapperAtOriginal
          wrapperShape.2.2.1).append (ih (ancestors ++ [here])))
  · intro _ _ _ _
    exact ⟨Nat.add_zero _, rfl, by simp⟩
  · intro _ _ _ _ _ _ _ _ _ _ head rest ancestors
    exact (head ancestors).append (rest ancestors)

private theorem compiled_layout {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) :
    Layout (entries snapshot compiled.schema.items) compiled.declarations 1
      (entries snapshot compiled.schema.items).size := by
  obtain ⟨_, _, _, grammar⟩ := compiled.schema.grammar.children
  rw [compiled.preorder]
  exact layout grammar []

public theorem original_nodes {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) :
    compiled.declarations.map (·.location.ordinal) = List.range' 1 (snapshot.metadata.schema.length - 1) ∧
    ∀ node ∈ compiled.declarations, ∃ entry : Entry,
      snapshot.metadata.schema[node.location.ordinal]? = some entry.1 ∧
      compiled.schema.items[node.location.ordinal]? = some entry.2 ∧
      entry.1.physicalType = node.physical := by
  have checked := compiled_layout compiled
  have size := checked.exactStop
  simp [entries, ← compiled.schema.aligned] at size
  refine ⟨?_, ?_⟩
  · rw [checked.ordinals]
    congr 1
    omega
  · intro node member
    obtain ⟨entry, item, physical⟩ := checked.physical node member
    obtain ⟨typed, raw⟩ := entry_binding item
    exact ⟨entry, typed, raw, physical⟩

public theorem leaf_order {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) :
    compiled.leaves.toList.map (·.path) = compiled.declarations.filterMap Node.leaf? := by
  rw [compiled.ordered]
  simp only [columns, List.map_map]
  exact List.zipIdx_map_fst _ _

private theorem leaf_ordinal {node : Node} {path : LeafPath} (read : node.leaf? = some path) :
    path.site.location.ordinal = node.location.ordinal := by
  cases node with
  | mk declaration ancestors =>
    cases declaration with
    | ancestor _ => simp [Node.leaf?] at read
    | wrapper _ => simp [Node.leaf?] at read
    | signed _ _ =>
      simp only [Node.leaf?, Option.some.injEq] at read
      cases read
      rfl

public theorem leaf_ordinals_increase {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) :
    (compiled.leaves.toList.map (·.path)).Pairwise
      (fun left right => left.site.location.ordinal < right.site.location.ordinal) := by
  rw [leaf_order]
  have original : (compiled.declarations.map (·.location.ordinal)).Pairwise (· < ·) := by
    rw [(original_nodes compiled).1]
    exact List.pairwise_lt_range' _
  refine (List.pairwise_map.mp original).filterMap _ ?_
  intro left right ordered path lhs other rhs
  rwa [leaf_ordinal lhs, leaf_ordinal rhs]

public theorem leaf_column {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {column : Nat} {plan : LeafPlan}
    (selected : compiled.leaves[column]? = some plan) :
    plan.column = column ∧ (compiled.declarations.filterMap Node.leaf?)[column]? = some plan.path := by
  rw [compiled.ordered] at selected
  simp only [List.getElem?_toArray, columns, List.getElem?_map, List.getElem?_zipIdx, Option.map_map] at selected
  cases hit : (compiled.declarations.filterMap Node.leaf?)[column]? with
  | none => simp [hit, Function.comp_def] at selected
  | some path =>
    simp only [hit, Option.map_some, Function.comp_apply, Option.some.injEq] at selected
    subst plan
    exact ⟨Nat.zero_add _, rfl⟩

public theorem leaf_original {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {column : Nat} {plan : LeafPlan}
    (selected : compiled.leaves[column]? = some plan) :
    ∃ entry : Entry, snapshot.metadata.schema[plan.path.site.location.ordinal]? = some entry.1 ∧
      compiled.schema.items[plan.path.site.location.ordinal]? = some entry.2 ∧
      entry.1.physicalType = some plan.path.kind.physical := by
  have member := List.mem_of_getElem? (leaf_column compiled selected).2
  obtain ⟨node, present, path⟩ := List.mem_filterMap.mp member
  obtain ⟨entry, hit, raw, physical⟩ := (original_nodes compiled).2 node present
  cases node with
  | mk declaration ancestors =>
    cases declaration with
    | ancestor _ => simp [Node.leaf?] at path
    | wrapper _ => simp [Node.leaf?] at path
    | signed site kind =>
      simp only [Node.leaf?, Option.some.injEq] at path
      rw [← path]
      exact ⟨entry, hit, raw, physical⟩

public theorem leaf_coverage {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {ordinal : Nat} {entry : Footer.SchemaElement}
    (hit : snapshot.metadata.schema[ordinal]? = some entry) (physical : entry.physicalType.isSome = true) :
    ∃ plan ∈ compiled.leaves.toList,
      plan.path.site.location.ordinal = ordinal ∧ some plan.path.kind.physical = entry.physicalType := by
  have lt := (List.getElem?_eq_some_iff.mp hit).1
  have positive : 0 < ordinal := by
    by_contra notPositive
    have zero : ordinal = 0 := by omega
    subst ordinal
    have root := (entry_binding compiled.schema.grammar.originalRoot).1
    rw [hit] at root
    simp [(Option.some.inj root), compiled.schema.grammar.group.1] at physical
  obtain ⟨node, inTree, sameOrdinal⟩ := List.mem_map.mp (show ordinal ∈ compiled.declarations.map (·.location.ordinal) by
    rw [(original_nodes compiled).1]
    exact List.mem_range'.mpr ⟨ordinal - 1, by omega, by simp; omega⟩)
  obtain ⟨actual, original, _, matching⟩ := (original_nodes compiled).2 node inTree
  rw [sameOrdinal, hit] at original
  have exactType : entry.physicalType = node.physical := by rw [Option.some.inj original]; exact matching
  cases node with
  | mk declaration ancestors =>
    cases declaration with
    | ancestor _ =>
      simp only [Node.physical, Node.leaf?, Option.map_none] at exactType
      simp [exactType] at physical
    | wrapper _ =>
      simp only [Node.physical, Node.leaf?, Option.map_none] at exactType
      simp [exactType] at physical
    | signed site kind =>
      have member : (⟨site, kind, ancestors⟩ : LeafPath) ∈ compiled.leaves.toList.map (·.path) := by
        rw [leaf_order]
        exact List.mem_filterMap.mpr ⟨_, inTree, rfl⟩
      obtain ⟨plan, listed, samePath⟩ := List.mem_map.mp member
      exact ⟨plan, listed, by simpa [samePath, Node.location] using sameOrdinal,
        by simpa [samePath, Node.physical, Node.leaf?] using exactType.symm⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree
