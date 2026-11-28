module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Thms
import Mathlib.Data.List.Forall2

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema (Entry Location Site)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Compiled Context Field FieldWire FieldsWire Leaf Step)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Cell Row Observation)

private theorem leafSteps {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader}
    {original : Array Entry} {depth ordinal next : Nat} {ctx : Context} {leaf : Leaf}
    (wire : FieldWire reader original depth ctx ordinal (.leaf leaf) next) :
    leaf.steps = (ctx.enter leaf.site).steps := by
  cases wire
  rfl

private theorem twoLeaves {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader}
    {original : Array Entry} {depth count ordinal next : Nat} {ctx : Context} {left right : Leaf}
    (wire : FieldsWire reader original depth ctx count ordinal [.leaf left, .leaf right] next) :
    left.steps = (ctx.enter left.site).steps ∧ right.steps = (ctx.enter right.site).steps := by
  cases wire with
  | cons first rest =>
    cases rest with
    | cons second _ => exact ⟨leafSteps first, leafSteps second⟩

private theorem enteredSteps (outer : Site) (wrapper : Location) (element child : Site) :
    (((({} : Context).enterList outer wrapper).enter element).enter child).steps =
      sharedSteps outer wrapper element ++ childSteps child := by
  cases root : outer.nullable <;> cases item : element.nullable <;> cases field : child.nullable <;>
    simp [Context.enterList, Context.enter, Context.role, sharedSteps, childSteps, root, item, field]

private theorem fieldSteps {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader}
    {original : Array Entry} {depth ordinal next : Nat} {outer element : Site} {wrapper : Location}
    {left right : Leaf}
    (wire : FieldWire reader original depth {} ordinal
      (.list outer wrapper (.group element [.leaf left, .leaf right])) next) :
    left.steps = sharedSteps outer wrapper element ++ childSteps left.site ∧
    right.steps = sharedSteps outer wrapper element ++ childSteps right.site := by
  cases wire with
  | list _ _ _ _ _ _ _ inner =>
    cases inner with
    | group _ _ _ _ _ _ _ children =>
      obtain ⟨leftSteps, rightSteps⟩ := twoLeaves children
      exact ⟨leftSteps.trans (enteredSteps _ _ _ _), rightSteps.trans (enteredSteps _ _ _ _)⟩

private theorem singleField {reader : Silmaril.Formats.ThriftCompact.Traversal.Reader}
    {original : Array Entry} {depth count ordinal next : Nat} {ctx : Context} {field : Field}
    (wire : FieldsWire reader original depth ctx count ordinal [field] next) :
    ∃ middle, FieldWire reader original depth ctx ordinal field middle := by
  cases wire with
  | cons first _ => exact ⟨_, first⟩

public theorem schema_steps {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {outer element : Site} {wrapper : Location} {left right : Leaf}
    (shape : schema.fields = [.list outer wrapper (.group element [.leaf left, .leaf right])]) :
    left.steps = sharedSteps outer wrapper element ++ childSteps left.site ∧
    right.steps = sharedSteps outer wrapper element ++ childSteps right.site := by
  obtain ⟨_, _, _, fields⟩ := schema.grammar.children
  rw [shape] at fields
  obtain ⟨_, first⟩ := singleField fields
  exact fieldSteps first

private theorem option_bind {α β : Type} {input : Option α} {next : α → Option β} {value : β}
    (read : (input >>= next) = some value) :
    ∃ checked, input = some checked ∧ next checked = some value := by
  cases input with
  | none => contradiction
  | some checked => exact ⟨checked, rfl, read⟩

private theorem append_topology {ceiling : Nat} {left right moreLeft moreRight : List Atom}
    (before : SharedTopology ceiling left right) (after : SharedTopology ceiling moreLeft moreRight) :
    SharedTopology ceiling (left ++ moreLeft) (right ++ moreRight) := by
  unfold SharedTopology at before after ⊢
  simp [List.map_append, before, after]

private theorem reverse_topology {ceiling : Nat} {left right : List Atom}
    (before : SharedTopology ceiling left right) :
    SharedTopology ceiling left.reverse right.reverse := by
  simpa [SharedTopology, List.map_reverse] using congrArg List.reverse before

private theorem leaf_atom {outer element : Site} {wrapper : Location} {leaf : Leaf}
    {position : Projection.Position} {value : Cell} {columns : List (List Atom)} {depth : Nat}
    (steps : leaf.steps = sharedSteps outer wrapper element ++ childSteps leaf.site)
    (role : position.role = .descendant)
    (projected : Projection.cell (depth + 1) position (.leaf leaf) value = some columns) :
    ∃ slot, columns = [[slot]] ∧
      commonLevels (sharedSteps outer wrapper element).length slot =
        (position.repetition, (sharedSteps outer wrapper element).length) := by
  cases value with
  | none =>
    simp only [Projection.cell, Projection.missing, role, Projection.absent, List.mapM_cons, List.mapM_nil] at projected
    cases siteNull : leaf.site.nullable
    · simp [siteNull] at projected
    · simp [siteNull, steps, sharedSteps, childSteps, List.findIdx?_cons, Option.bind, Bind.bind,
        Pure.pure] at projected
      split at projected <;> split at projected <;>
        simp_all [commonLevels, Projection.atom, sharedSteps] <;> subst columns <;> simp
  | some value =>
    cases value <;> simp [Projection.cell] at projected
    all_goals
      obtain ⟨_, rfl⟩ := projected
      refine ⟨_, rfl, ?_⟩
      simp [commonLevels, Projection.atom, Leaf.maxDefinition, steps, Nat.min_eq_right]

private def Paired (ceiling : Nat) (columns : List (List Atom)) : Prop :=
  ∃ left right, columns = [left, right] ∧ SharedTopology ceiling left right

private theorem sharedAbsent {outer element : Site} {wrapper : Location} {left right : Leaf}
    {position : Projection.Position} {step : Step} {index : Nat} {columns : List (List Atom)}
    (leftSteps : left.steps = sharedSteps outer wrapper element ++ childSteps left.site)
    (rightSteps : right.steps = sharedSteps outer wrapper element ++ childSteps right.site)
    (firstMissing : (sharedSteps outer wrapper element).findIdx? (fun original => decide (original = step)) =
      some index)
    (projected : Projection.absent position step [left, right] = some columns) :
    Paired (sharedSteps outer wrapper element).length columns := by
  simp [Projection.absent, leftSteps, rightSteps, firstMissing, Option.bind, Bind.bind, Pure.pure] at projected
  subst columns
  exact ⟨_, _, rfl, rfl⟩

private theorem fields_length {project : Field → Cell → Option (List (List Atom))}
    {fields : List Field} {cells : Row} {output : List (List Atom)}
    (projected : Projection.fields project fields cells = some output) : fields.length = cells.length := by
  induction fields generalizing cells output with
  | nil => cases cells <;> first | rfl | contradiction
  | cons field fields ih =>
    cases cells with
    | nil => contradiction
    | cons cell rest =>
      obtain ⟨_, _, next⟩ := option_bind projected
      obtain ⟨_, projected, _⟩ := option_bind next
      simp [ih projected]

private theorem element_pair {outer element : Site} {wrapper : Location} {left right : Leaf}
    {position : Projection.Position} {value : Cell} {columns : List (List Atom)} {depth : Nat}
    (leftSteps : left.steps = sharedSteps outer wrapper element ++ childSteps left.site)
    (rightSteps : right.steps = sharedSteps outer wrapper element ++ childSteps right.site)
    (role : position.role = .element)
    (projected : Projection.cell depth position (.group element [.leaf left, .leaf right]) value = some columns) :
    Paired (sharedSteps outer wrapper element).length columns := by
  cases depth with
  | zero => contradiction
  | succ depth =>
    cases value with
    | none =>
      simp only [Projection.cell, Projection.missing, role] at projected
      split at projected
      · rename_i optional
        have missing : Projection.absent position (.optional element.location .element) [left, right] = some columns :=
          by simpa [Field.leaves] using projected
        refine sharedAbsent leftSteps rightSteps (index := if outer.nullable then 2 else 1) ?_ missing
        cases outerNull : outer.nullable <;> simp [sharedSteps, outerNull, optional, List.findIdx?_cons]
      · contradiction
    | some value =>
      cases value <;> simp only [Projection.cell] at projected
      all_goals try contradiction
      rename_i row
      have length := fields_length projected
      cases row with
      | nil => contradiction
      | cons l rest =>
        cases rest with
        | nil => simp at length
        | cons r rest =>
          cases rest with
          | cons => simp at length
          | nil =>
            cases leftRead : Projection.cell depth position.child (.leaf left) l with
            | none => simp [Projection.fields, leftRead, Bind.bind, Option.bind] at projected
            | some lhs =>
              cases rightRead : Projection.cell depth position.child (.leaf right) r with
              | none => simp [Projection.fields, leftRead, rightRead, Bind.bind, Option.bind] at projected
              | some rhs =>
                simp [Projection.fields, leftRead, rightRead, Bind.bind, Option.bind, Pure.pure] at projected
                subst columns
                cases depth with
                | zero => contradiction
                | succ depth =>
                  have childRole : position.child.role = .descendant := by
                    simp [Projection.Position.child, role]
                  obtain ⟨l, rfl, commonLeft⟩ := leaf_atom leftSteps childRole leftRead
                  obtain ⟨r, rfl, commonRight⟩ := leaf_atom rightSteps childRole rightRead
                  exact ⟨[l], [r], rfl, by simp [SharedTopology, commonLeft, commonRight]⟩

private theorem elements_fold {ceiling : Nat}
    {project : Projection.Position → Cell → Option (List (List Atom))}
    (pointwise : ∀ pos value output, pos.role = .element →
      project pos value = some output → Paired ceiling output)
    {indexed : List (Cell × Nat)} {initial output : List (List Atom)}
    (start : Paired ceiling initial)
    (projected : indexed.foldlM (Projection.addElement project 2) initial = some output) :
    Paired ceiling output := by
  induction indexed generalizing initial output with
  | nil =>
    cases Option.some.inj projected
    exact start
  | cons first rest ih =>
    obtain ⟨next, accepted, remaining⟩ := option_bind projected
    obtain ⟨left, right, rfl, before⟩ := start
    obtain ⟨value, index⟩ := first
    unfold Projection.addElement at accepted
    obtain ⟨part, partRead, added⟩ := option_bind accepted
    obtain ⟨nextLeft, nextRight, rfl, after⟩ := pointwise _ _ _ rfl partRead
    cases Option.some.inj added
    exact ih ⟨_, _, rfl, append_topology (reverse_topology after) before⟩ remaining

private theorem elements_pair {ceiling : Nat}
    {project : Projection.Position → Cell → Option (List (List Atom))}
    (pointwise : ∀ pos value output, pos.role = .element →
      project pos value = some output → Paired ceiling output)
    {cells : List Cell} {output : List (List Atom)}
    (projected : Projection.elements project 2 cells = some output) : Paired ceiling output := by
  obtain ⟨_, read, done⟩ := option_bind projected
  obtain ⟨_, _, rfl, reversed⟩ := elements_fold pointwise ⟨[], [], rfl, rfl⟩ read
  cases Option.some.inj done
  exact ⟨_, _, rfl, reverse_topology reversed⟩

private theorem list_pair {outer element : Site} {wrapper : Location} {left right : Leaf}
    {value : Cell} {columns : List (List Atom)} {depth : Nat}
    (leftSteps : left.steps = sharedSteps outer wrapper element ++ childSteps left.site)
    (rightSteps : right.steps = sharedSteps outer wrapper element ++ childSteps right.site)
    (projected : Projection.cell depth {} (.list outer wrapper (.group element [.leaf left, .leaf right])) value =
      some columns) : Paired (sharedSteps outer wrapper element).length columns := by
  cases depth with
  | zero => contradiction
  | succ depth =>
    cases value with
    | none =>
      simp only [Projection.cell, Projection.missing, Field.leaves, List.flatMap_cons, List.flatMap_nil,
        List.singleton_append, List.append_nil] at projected
      split at projected
      · exact sharedAbsent leftSteps rightSteps (index := 0)
          (by simp [sharedSteps, *, List.findIdx?_cons]) projected
      · contradiction
    | some value =>
      cases value <;> try contradiction
      rename_i cells
      cases cells with
      | nil =>
        have absent : Projection.absent {} (.emptyList outer.location wrapper) [left, right] = some columns :=
          by simpa [Projection.cell, Field.leaves] using projected
        exact sharedAbsent leftSteps rightSteps (index := if outer.nullable then 1 else 0)
          (by cases outerNull : outer.nullable <;> simp [sharedSteps, outerNull, List.findIdx?_cons]) absent
      | cons first rest =>
        have elements :
            Projection.elements (fun pos => Projection.cell depth pos (.group element [.leaf left, .leaf right]))
              2 (first :: rest) = some columns := by
          simpa [Projection.cell, Field.leaves] using projected
        exact elements_pair (fun _ _ _ role read => element_pair leftSteps rightSteps role read) elements

public theorem projection_topology {outer element : Site} {wrapper : Location} {left right : Leaf}
    {row : Row} {leftAtoms rightAtoms : List Atom} {depth : Nat}
    (leftSteps : left.steps = sharedSteps outer wrapper element ++ childSteps left.site)
    (rightSteps : right.steps = sharedSteps outer wrapper element ++ childSteps right.site)
    (projected : Projection.row depth [.list outer wrapper (.group element [.leaf left, .leaf right])] row =
      some [leftAtoms, rightAtoms]) :
    SharedTopology (sharedSteps outer wrapper element).length leftAtoms rightAtoms := by
  cases row with
  | nil => contradiction
  | cons first rest =>
    obtain ⟨_, firstRead, restRead⟩ := option_bind projected
    obtain ⟨_, tail, done⟩ := option_bind restRead
    cases rest with
    | cons => contradiction
    | nil =>
      cases Option.some.inj tail
      obtain ⟨_, _, rfl, topology⟩ := list_pair leftSteps rightSteps firstRead
      simp only [pure, List.append_nil, Option.some.injEq, List.cons.injEq, and_true] at done
      obtain ⟨rfl, rfl⟩ := done
      exact topology

private theorem row_topology {outer element : Site} {wrapper : Location} {left right : Leaf}
    {depth : Nat} {position : Position} {leftColumn rightColumn : Column} {row : Row}
    (leftSteps : left.steps = sharedSteps outer wrapper element ++ childSteps left.site)
    (rightSteps : right.steps = sharedSteps outer wrapper element ++ childSteps right.site)
    (wire : RowWire depth position [.list outer wrapper (.group element [.leaf left, .leaf right])]
      [leftColumn, rightColumn] row) :
    SharedRowWire depth position [.list outer wrapper (.group element [.leaf left, .leaf right])]
      (sharedSteps outer wrapper element).length leftColumn rightColumn row := by
  obtain ⟨inputs, atPosition, _, projection⟩ := wire
  cases atPosition with
  | cons leftAt rest =>
    cases rest with
    | cons rightAt remaining =>
      cases remaining
      exact ⟨_, _, leftAt, rightAt, projection, projection_topology leftSteps rightSteps projection⟩

public theorem group_topology {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {group : Nat} {output : Observation}
    {outer element : Site} {wrapper : Location} {left right : Leaf}
    (shape : schema.fields = [.list outer wrapper (.group element [.leaf left, .leaf right])])
    (wire : GroupWire limits schema group output) :
    ListStructWire limits schema group (sharedSteps outer wrapper element).length output := by
  obtain ⟨rowGroup, columns, groupAt, _, _, rowCount, source, rows⟩ := wire.original
  obtain ⟨leftSteps, rightSteps⟩ := schema_steps schema shape
  have width : schema.leaves.size = 2 := by
    rw [schema.ordered, shape]
    simp [Field.leaves]
  rw [width] at source
  change List.Forall₂ (ColumnWire limits.chunk schema group) [0, 1] columns at source
  cases source with
  | cons first remaining =>
    cases remaining with
    | cons second finished =>
      cases finished
      refine ⟨rowGroup, _, _, groupAt, rowCount, first, second, ?_⟩
      rw [shape] at rows ⊢
      exact rows.imp (fun _ _ => row_topology leftSteps rightSteps)

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared
