module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs

/-! The footer plan and level semantics for a single canonical List of
canonical Lists of signed words. Each List contributes its original repeated
wrapper. Optional steps come from the original schema markers. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList

open RecursiveSchema (Entry Kind Location RepetitionWire Site Unannotated entries)

@[expose] public section

structure ListSite where
  site : Site
  wrapper : Location
  deriving Repr

structure Plan where
  outer : ListSite
  inner : ListSite
  leaf : Site
  kind : Kind
  deriving Repr

def ListSite.enter (node : ListSite) (ctx : Repeated.Context) : Repeated.Context :=
  ctx.enterList node.site node.wrapper

def Plan.outerContext (plan : Plan) : Repeated.Context := plan.outer.enter {}

def Plan.innerContext (plan : Plan) : Repeated.Context := plan.inner.enter plan.outerContext

def Plan.outerEmpty (plan : Plan) : Nat := plan.outerContext.steps.length - 1

def Plan.innerEmpty (plan : Plan) : Nat := plan.innerContext.steps.length - 1

def Plan.steps (plan : Plan) : List Repeated.Step := (plan.innerContext.enter plan.leaf).steps

def Plan.maxDefinition (plan : Plan) : Nat := plan.steps.length

inductive Presence where
  | nullOuter | emptyOuter | nullInner | emptyInner | nullValue | value
  deriving DecidableEq, Repr

def Plan.presence (plan : Plan) (definition : Nat) : Option Presence :=
  if definition < plan.outerEmpty then some .nullOuter
  else if definition = plan.outerEmpty then some .emptyOuter
  else if definition < plan.innerEmpty then some .nullInner
  else if definition = plan.innerEmpty then some .emptyInner
  else if definition < plan.maxDefinition then some .nullValue
  else if definition = plan.maxDefinition then some .value
  else none

/-- The exact definition represented by a particular event. Required sites
have no null event. The two empty events belong to different wrappers. -/
def DefinitionWire (plan : Plan) (definition : Nat) : Presence → Prop
  | .nullOuter => plan.outer.site.nullable = true ∧ definition = 0
  | .emptyOuter => definition = plan.outerEmpty
  | .nullInner => plan.inner.site.nullable = true ∧ definition = plan.outerEmpty + 1
  | .emptyInner => definition = plan.innerEmpty
  | .nullValue => plan.leaf.nullable = true ∧ definition = plan.innerEmpty + 1
  | .value => definition = plan.maxDefinition

def Root (entry : Entry) : Prop :=
  Unannotated entry ∧ entry.1.physicalType = none ∧ entry.1.typeLength = none ∧
    (entry.1.repetition = none ∨ entry.1.repetition = some .required) ∧ entry.1.numChildren = some 1

instance (entry : Entry) : Decidable (Root entry) := by unfold Root; infer_instance

structure ListWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (ctx : Repeated.Context) (ordinal : Nat) (node : ListSite) : Prop where
  original : ∃ entry wrapper,
    original[ordinal]? = some entry ∧ original[ordinal + 1]? = some wrapper ∧
    RepetitionWire entry node.site.nullable ∧ Repeated.ListOuter entry ∧
    ListFile.checkList reader entry.2 = .ok () ∧ Repeated.Wrapper wrapper ∧
    node.site = ctx.site ordinal entry.1.name node.site.nullable ∧
    node.wrapper = Repeated.wrapperAt node.site ordinal wrapper

structure SignedWire (original : Array Entry) (ctx : Repeated.Context) (ordinal : Nat)
    (site : Site) (kind : Kind) : Prop where
  original : ∃ entry, original[ordinal]? = some entry ∧ RepetitionWire entry site.nullable ∧
    Unannotated entry ∧ entry.1.typeLength = none ∧ entry.1.numChildren.getD 0 = 0 ∧
    entry.1.physicalType = some kind.physical ∧ site = ctx.site ordinal entry.1.name site.nullable

structure SchemaWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (plan : Plan) : Prop where
  extent : original.size = 6
  root : ∃ entry, original[0]? = some entry ∧ Root entry
  outer : ListWire reader original {} 1 plan.outer
  inner : ListWire reader original plan.outerContext 3 plan.inner
  leaf : SignedWire original plan.innerContext 5 plan.leaf plan.kind

structure Compiled (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) where
  container : ThriftCompact.Traversal.Field
  items : List Footer.ColumnOrder.Item
  plan : Plan
  original : Footer.NestedLeaf.readItems limits.footer snapshot = .ok (container, items)
  aligned : snapshot.metadata.schema.length = items.length
  grammar : SchemaWire (Footer.ColumnOrder.footerReader limits.footer snapshot)
    (entries snapshot items) plan

inductive Error where
  | snapshot (original : Snapshot.Error Unit)
  | items (original : Footer.NestedLeaf.Error)
  | extent (schema items : Nat)
  | shape (ordinal : Nat)
  | repetition (ordinal : Nat) (original : Option Footer.Repetition)
  | annotation (ordinal : Nat) (original : ListFile.OpenError)
  deriving DecidableEq, Repr

structure Source (limits : Snapshot.Limits) (bytes : Bytes) where
  snapshot : Snapshot.Checked
  schema : Compiled limits snapshot
  original : Snapshot.check (Failure := Unit) limits bytes = .ok snapshot

end

private def entryAt (original : Array Entry) (ordinal : Nat) :
    Except Error {entry // original[ordinal]? = some entry} :=
  match _found : original[ordinal]? with
  | none => .error (.shape ordinal)
  | some entry => .ok ⟨entry, rfl⟩

private def nullable (entry : Entry) (ordinal : Nat) :
    Except Error {value // RepetitionWire entry value} :=
  match found : entry.1.repetition with
  | some .required => .ok ⟨false, found⟩
  | some .optional => .ok ⟨true, found⟩
  | other => .error (.repetition ordinal other)

private def readList (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (ctx : Repeated.Context) (ordinal : Nat) :
    Except Error {node // ListWire reader original ctx ordinal node} := do
  let ⟨entry, found⟩ ← entryAt original ordinal
  let ⟨optional, repetition⟩ ← nullable entry ordinal
  let site := ctx.site ordinal entry.1.name optional
  let ⟨wrapper, foundWrapper⟩ ← entryAt original (ordinal + 1)
  if shape : Repeated.ListOuter entry ∧ Repeated.Wrapper wrapper then
    match annotation : ListFile.checkList reader entry.2 with
    | .error cause => throw (.annotation ordinal cause)
    | .ok () => return ⟨⟨site, Repeated.wrapperAt site ordinal wrapper⟩,
        ⟨entry, wrapper, found, foundWrapper, repetition, shape.1, annotation, shape.2, rfl, rfl⟩⟩
  else throw (.shape ordinal)

private def readLeaf (original : Array Entry) (ctx : Repeated.Context) (ordinal : Nat) :
    Except Error {result : Site × Kind // SignedWire original ctx ordinal result.1 result.2} := do
  let ⟨entry, found⟩ ← entryAt original ordinal
  let ⟨optional, repetition⟩ ← nullable entry ordinal
  let site := ctx.site ordinal entry.1.name optional
  if shape : Unannotated entry ∧ entry.1.typeLength = none ∧ entry.1.numChildren.getD 0 = 0 then
    match physical : entry.1.physicalType with
    | some .int32 => return ⟨(site, .int32), ⟨entry, found, repetition, shape.1, shape.2.1, shape.2.2,
        physical, rfl⟩⟩
    | some .int64 => return ⟨(site, .int64), ⟨entry, found, repetition, shape.1, shape.2.1, shape.2.2,
        physical, rfl⟩⟩
    | _ => throw (.shape ordinal)
  else throw (.shape ordinal)

/-- Bind the two LIST annotations, both wrappers and the signed leaf to the
original six SchemaElements in preorder. -/
public def compile (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) :
    Except Error (Compiled limits snapshot) := do
  match found : Footer.NestedLeaf.readItems limits.footer snapshot with
  | .error cause => throw (.items cause)
  | .ok (container, items) =>
    let original := entries snapshot items
    if aligned : snapshot.metadata.schema.length = items.length ∧ original.size = 6 then
      let reader := Footer.ColumnOrder.footerReader limits.footer snapshot
      let ⟨root, foundRoot⟩ ← entryAt original 0
      if shape : Root root then
        let ⟨outer, outerWire⟩ ← readList reader original {} 1
        let ⟨inner, innerWire⟩ ← readList reader original (outer.enter {}) 3
        let ⟨(site, kind), leafWire⟩ ← readLeaf original (inner.enter (outer.enter {})) 5
        return ⟨container, items, ⟨outer, inner, site, kind⟩, found, aligned.1,
          ⟨aligned.2, ⟨root, foundRoot, shape⟩, outerWire, innerWire, leafWire⟩⟩
      else throw (.shape 0)
    else throw (.extent snapshot.metadata.schema.length items.length)

public def openFile (limits : Snapshot.Limits) (bytes : Bytes) : Except Error (Source limits bytes) := do
  match original : Snapshot.check (Failure := Unit) limits bytes with
  | .error cause => throw (.snapshot cause)
  | .ok snapshot => return ⟨snapshot, ← compile limits snapshot, original⟩

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList
