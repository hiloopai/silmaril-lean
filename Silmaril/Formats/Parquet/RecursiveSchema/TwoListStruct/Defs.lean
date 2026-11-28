module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Defs

/-! Original footer admission for two nested LISTs with a required
Struct element and two independently required or optional signed children. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct

open RecursiveSchema (Entry Kind Site Unannotated RepetitionWire entries)
open TwoList (ListSite ListWire SignedWire Root)

@[expose] public section

inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

def Side.column : Side → Nat
  | .left => 0
  | .right => 1

def Side.select {α : Type} (side : Side) (left right : α) : α :=
  match side with
  | .left => left
  | .right => right

structure Plan where
  outer : ListSite
  inner : ListSite
  element : Site
  left : Site × Kind
  right : Site × Kind
  deriving Repr

def Plan.outerContext (plan : Plan) : Repeated.Context := plan.outer.enter {}
def Plan.innerContext (plan : Plan) : Repeated.Context := plan.inner.enter plan.outerContext
def Plan.elementContext (plan : Plan) : Repeated.Context := plan.innerContext.enter plan.element

def Plan.child (plan : Plan) (side : Side) : Site × Kind := side.select plan.left plan.right

/-- A required Struct contributes no definition or repetition increment.
The signed site keeps its original path through that Struct. -/
def Plan.path (plan : Plan) (side : Side) : ListPath.Plan :=
  let (site, kind) := plan.child side
  ⟨plan.outer, .list plan.inner (.signed site kind)⟩

def Plan.sharedDefinition (plan : Plan) : Nat :=
  plan.outer.site.nullable.toNat + 1 + (plan.inner.site.nullable.toNat + 1)

structure StructWire (original : Array Entry) (ctx : Repeated.Context) (site : Site) : Prop where
  original : ∃ entry, original[5]? = some entry ∧ Unannotated entry ∧
    entry.1.physicalType = none ∧ entry.1.typeLength = none ∧
    entry.1.numChildren = some 2 ∧ entry.1.repetition = some .required ∧
    site = ctx.site 5 entry.1.name false

structure SchemaWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (plan : Plan) : Prop where
  extent : original.size = 8
  root : ∃ entry, original[0]? = some entry ∧ Root entry
  outer : ListWire reader original {} 1 plan.outer
  inner : ListWire reader original plan.outerContext 3 plan.inner
  element : StructWire original plan.innerContext plan.element
  left : SignedWire original plan.elementContext 6 plan.left.1 plan.left.2
  right : SignedWire original plan.elementContext 7 plan.right.1 plan.right.2

structure Compiled (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) where
  container : ThriftCompact.Traversal.Field
  items : List Footer.ColumnOrder.Item
  plan : Plan
  original : Footer.NestedLeaf.readItems limits.footer snapshot = .ok (container, items)
  aligned : snapshot.metadata.schema.length = items.length
  depth : 7 ≤ limits.maxSchemaDepth
  grammar : SchemaWire (Footer.ColumnOrder.footerReader limits.footer snapshot)
    (entries snapshot items) plan

structure Source (limits : Snapshot.Limits) (bytes : Bytes) where
  snapshot : Snapshot.Checked
  schema : Compiled limits snapshot
  original : Snapshot.check (Failure := Unit) limits bytes = .ok snapshot

inductive Error where
  | original (cause : TwoList.Error)
  | depth (admitted : Nat)
  | structShape
  deriving DecidableEq, Repr

end

private def readStruct (original : Array Entry) (ctx : Repeated.Context) :
    Except Error {site // StructWire original ctx site} := do
  let ⟨entry, found⟩ ← (TwoList.entryAt original 5).mapError .original
  if shape : Unannotated entry ∧ entry.1.physicalType = none ∧ entry.1.typeLength = none ∧
      entry.1.numChildren = some 2 ∧ entry.1.repetition = some .required then
    return ⟨ctx.site 5 entry.1.name false, ⟨entry, found, shape.1, shape.2.1, shape.2.2.1,
      shape.2.2.2.1, shape.2.2.2.2, rfl⟩⟩
  else throw .structShape

public def compile (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) :
    Except Error (Compiled limits snapshot) :=
  if depth : 7 ≤ limits.maxSchemaDepth then
    match found : Footer.NestedLeaf.readItems limits.footer snapshot with
    | .error cause => .error (.original (.items cause))
    | .ok (container, items) => do
      let original := entries snapshot items
      let reader := Footer.ColumnOrder.footerReader limits.footer snapshot
      if aligned : snapshot.metadata.schema.length = items.length ∧ original.size = 8 then
        let ⟨root, foundRoot⟩ ← (TwoList.entryAt original 0).mapError .original
        if rootShape : Root root then
          let ⟨outer, outerWire⟩ ← (TwoList.readList reader original {} 1).mapError .original
          let ⟨inner, innerWire⟩ ← (TwoList.readList reader original (outer.enter {}) 3).mapError .original
          let innerContext := inner.enter (outer.enter {})
          let ⟨element, elementWire⟩ ← readStruct original innerContext
          let ctx := innerContext.enter element
          let ⟨left, leftWire⟩ ← (TwoList.readLeaf original ctx 6).mapError .original
          let ⟨right, rightWire⟩ ← (TwoList.readLeaf original ctx 7).mapError .original
          return ⟨container, items, ⟨outer, inner, element, left, right⟩, found, aligned.1, depth,
            ⟨aligned.2, ⟨root, foundRoot, rootShape⟩, outerWire, innerWire, elementWire, leftWire, rightWire⟩⟩
        else throw (.original (.shape 0))
      else throw (.original (.extent snapshot.metadata.schema.length items.length))
  else .error (.depth limits.maxSchemaDepth)

public def openFile (limits : Snapshot.Limits) (bytes : Bytes) : Except Error (Source limits bytes) := do
  match original : Snapshot.check (Failure := Unit) limits bytes with
  | .error cause => throw (.original (.snapshot cause))
  | .ok snapshot => return ⟨snapshot, ← compile limits snapshot, original⟩

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct
