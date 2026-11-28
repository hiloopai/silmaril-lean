module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Compiler
import Mathlib.Data.List.TakeDrop

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema (Entry Location)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Absence Boundary Context Field FieldWire FieldsWire Step wrapperAt)
open Silmaril.Formats.Parquet.RecursiveSchema.Tree

private def Prefixes (allNodes : List Node) (path : List Ancestor) : Prop :=
  ∀ i ancestor, path[i]? = some ancestor → (⟨.ancestor ancestor, path.take i⟩ : Node) ∈ allNodes

private theorem extend {allNodes : List Node} {before : List Ancestor} {here : Ancestor}
    (prior : Prefixes allNodes before) (member : (⟨.ancestor here, before⟩ : Node) ∈ allNodes) :
    Prefixes allNodes (before ++ [here]) := by
  intro i atSite selected
  by_cases earlier : i < before.length
  · rw [List.getElem?_append_left earlier] at selected
    rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
    exact prior i atSite selected
  · have within := (List.getElem?_eq_some_iff.mp selected).1
    simp only [List.length_append, List.length_singleton] at within
    have position : i = before.length := by omega
    subst i
    rw [List.getElem?_append_right (Nat.le_refl _)] at selected
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at selected
    subst atSite
    simpa only [List.take_left] using member

private theorem grammar_prefixes {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader}
    {original : Array Entry} {depth count start stop : Nat} {ctx : Context} {fields : List Field}
    (wire : FieldsWire reader original depth ctx count start fields stop) (allNodes : List Node) :
    ∀ before, Prefixes allNodes before → fields.flatMap (nodes before) ⊆ allNodes →
      ∀ node ∈ fields.flatMap (nodes before), Prefixes allNodes node.ancestors := by
  apply FieldsWire.rec
    (motive_1 := fun _ _ _ field _ _ => ∀ before, Prefixes allNodes before → nodes before field ⊆ allNodes →
      ∀ node ∈ nodes before field, Prefixes allNodes node.ancestors)
    (motive_2 := fun _ _ _ _ fields _ _ => ∀ before, Prefixes allNodes before →
      fields.flatMap (nodes before) ⊆ allNodes →
      ∀ node ∈ fields.flatMap (nodes before), Prefixes allNodes node.ancestors)
    (t := wire)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ before prior _ node member
    simp only [nodes, List.mem_singleton] at member
    subst node
    exact prior
  · intro _ ctx ordinal entry nullable _ children _ _ _ _ _ _ _ _ _ ih before prior subset node member
    let here := Ancestor.struct (ctx.site ordinal entry.1.name nullable)
    simp only [nodes] at subset member
    rcases List.mem_cons.mp member with rfl | descendants
    · exact prior
    · exact ih (before ++ [here]) (extend prior (subset (List.mem_cons_self ..)))
        (fun _ found => subset (List.mem_cons_of_mem _ found)) node descendants
  · intro _ ctx ordinal entry nullable wrapper element _ _ _ _ _ _ _ _ _ ih before prior subset node member
    let site := ctx.site ordinal entry.1.name nullable
    let here := Ancestor.list site (wrapperAt site ordinal wrapper)
    simp only [nodes] at subset member
    rcases List.mem_cons.mp member with rfl | descendants
    · exact prior
    · have child := extend prior (subset (List.mem_cons_self ..))
      rcases List.mem_cons.mp descendants with rfl | below
      · exact child
      · exact ih (before ++ [here]) child (fun _ found => subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ found)))
          node below
  · simp
  · intro _ _ _ _ _ _ _ _ _ _ first rest before prior subset node member
    simp only [List.flatMap_cons] at member subset
    rcases List.mem_append.mp member with front | back
    · exact first before prior (fun _ found => subset (List.mem_append_left _ found)) node front
    · exact rest before prior (fun _ found => subset (List.mem_append_right _ found)) node back

private theorem all_prefixes {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) (node : Node) (member : node ∈ compiled.declarations) :
    Prefixes compiled.declarations node.ancestors := by
  rw [compiled.preorder] at member
  obtain ⟨_, _, _, grammar⟩ := compiled.schema.grammar.children
  exact grammar_prefixes grammar compiled.declarations [] (by simp [Prefixes])
    (fun _ found => by simpa only [compiled.preorder] using found) node member

public theorem distinct_ordinals {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) : (compiled.declarations.map (·.location.ordinal)).Nodup := by
  rw [(original_nodes compiled).1]
  exact List.nodup_range' _

private theorem unique_of_nodup {allNodes : List Node} {first last : Node}
    (unique : (allNodes.map (·.location.ordinal)).Nodup)
    (left : first ∈ allNodes) (right : last ∈ allNodes)
    (equal : first.location.ordinal = last.location.ordinal) : first = last := by
  induction allNodes with
  | nil => simp at left
  | cons node rest ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with rfl | leftTail
    · rcases List.mem_cons.mp right with rfl | rightTail
      · rfl
      · have found := List.mem_map_of_mem (f := fun n => n.location.ordinal) rightTail
        exact (absent (by simpa only [← equal] using found)).elim
    · rcases List.mem_cons.mp right with rfl | rightTail
      · have found := List.mem_map_of_mem (f := fun n => n.location.ordinal) leftTail
        exact (absent (by simpa only [equal] using found)).elim
      · exact ih tail leftTail rightTail

public theorem same_ordinal {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {first last : Node}
    (left : first ∈ compiled.declarations) (right : last ∈ compiled.declarations)
    (equal : first.location.ordinal = last.location.ordinal) : first = last :=
  unique_of_nodup (distinct_ordinals compiled) left right equal

private theorem leaf_prefixes {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {column : Nat} {plan : LeafPlan}
    (selected : compiled.leaves[column]? = some plan) : Prefixes compiled.declarations plan.path.ancestors := by
  have member := List.mem_of_getElem? (leaf_column compiled selected).2
  obtain ⟨node, here, path⟩ := List.mem_filterMap.mp member
  have known := all_prefixes compiled node here
  cases node with
  | mk declaration ancestors =>
    cases declaration
    · simp [Node.leaf?] at path
    · simp [Node.leaf?] at path
    · simp only [Node.leaf?, Option.some.injEq] at path
      rw [← path]
      exact known

public theorem shared_ancestor {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) {i j left right : Nat} {lhs rhs : LeafPlan}
    {a b : Ancestor} (first : compiled.leaves[left]? = some lhs) (last : compiled.leaves[right]? = some rhs)
    (atLeft : lhs.path.ancestors[i]? = some a) (atRight : rhs.path.ancestors[j]? = some b)
    (shared : a.site.location.ordinal = b.site.location.ordinal) :
    a = b ∧ i = j ∧ lhs.path.ancestors.take i = rhs.path.ancestors.take j ∧
      lhs.path.ancestorSteps (i + 1) = rhs.path.ancestorSteps (j + 1) := by
  have equal := same_ordinal compiled (leaf_prefixes compiled first i a atLeft)
    (leaf_prefixes compiled last j b atRight) shared
  have site : a = b := by
    have h := congrArg Node.declaration equal
    exact Declaration.ancestor.inj h
  have before := congrArg Node.ancestors equal
  change lhs.path.ancestors.take i = rhs.path.ancestors.take j at before
  have leftBound := (List.getElem?_eq_some_iff.mp atLeft).1
  have rightBound := (List.getElem?_eq_some_iff.mp atRight).1
  have position := congrArg List.length before
  simp [Nat.min_eq_left (Nat.le_of_lt leftBound), Nat.min_eq_left (Nat.le_of_lt rightBound)] at position
  refine ⟨site, position, before, ?_⟩
  unfold LeafPath.ancestorSteps
  simp only [List.take_add_one, atLeft, atRight, before, site]

private theorem enter_prefix (ctx : Context) (site : Silmaril.Formats.Parquet.RecursiveSchema.Site) :
    ctx.steps <+: (ctx.enter site).steps := by
  unfold Context.enter
  split
  · exact List.prefix_append _ _
  · exact List.prefix_rfl

private theorem ancestor_prefix (ctx : Context) (ancestor : Ancestor) :
    ctx.steps <+: (ancestor.enter ctx).steps := by
  cases ancestor with
  | struct site => exact enter_prefix ctx site
  | list site wrapper =>
    simp only [Ancestor.enter, Context.enterList]
    split
    · exact (List.prefix_append _ _).trans (List.prefix_append _ _)
    · exact List.prefix_append _ _

private theorem fold_prefix (path : List Ancestor) (ctx : Context) :
    ctx.steps <+: (path.foldl Ancestor.enter ctx).steps := by
  induction path generalizing ctx with
  | nil => exact List.prefix_rfl
  | cons first tail ih => exact (ancestor_prefix ctx first).trans (ih (first.enter ctx))

public theorem steps_prefix (path : LeafPath) (count : Nat) :
    path.ancestorSteps count <+: path.steps := by
  unfold LeafPath.ancestorSteps LeafPath.steps ancestryContext
  conv_rhs => rw [← List.take_append_drop count path.ancestors, List.foldl_append]
  exact (fold_prefix _ _).trans (enter_prefix _ _)

public theorem nullable_level {path : LeafPath} {site : Location}
    {role : Absence} {level : Nat} (member : (site, role, level) ∈ path.nullable) :
    path.steps[level]? = some (.optional site role) := by
  obtain ⟨⟨step, i⟩, indexed, hit⟩ := List.mem_filterMap.mp member
  cases step with
  | optional loc kind =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hit
    obtain ⟨rfl, rfl, rfl⟩ := hit
    exact List.mk_mem_zipIdx_iff_getElem?.mp indexed
  | emptyList _ _ => cases hit

public theorem repeated_level {path : LeafPath} {boundary : Boundary} (member : boundary ∈ path.repeated) :
    path.steps[boundary.emptyLevel]? = some (.emptyList boundary.outer boundary.wrapper) := by
  obtain ⟨⟨step, level⟩, indexed, hit⟩ := List.mem_filterMap.mp member
  cases step with
  | optional _ _ => cases hit
  | emptyList outer wrapper =>
    cases Option.some.inj hit
    exact List.mk_mem_zipIdx_iff_getElem?.mp indexed

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree
