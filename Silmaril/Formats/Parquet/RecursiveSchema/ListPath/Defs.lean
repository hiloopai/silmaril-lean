module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Defs

/-! Canonical LIST paths to a single signed leaf. The schema budget charges
one level for the root, two per LIST, and one for the signed leaf.
The logical path can also carry a unary Struct projection from a
multi-leaf schema compiled by a caller. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath

open RecursiveSchema (Entry Site Kind entries)
open TwoList (ListSite ListWire SignedWire Root)

@[expose] public section

inductive Shape where
  | signed (site : Site) (kind : Kind)
  | list (node : ListSite) (child : Shape)
  | struct (site : Site) (child : Shape)
  deriving Repr

def Shape.arrow : Shape → Arrow.RecursiveSchema.Field
  | .signed site kind => .node (some site.name) site.nullable kind.arrow []
  | .list node child => .node (some node.site.name) node.site.nullable .list [child.arrow]
  | .struct site child => .node (some site.name) site.nullable .struct [child.arrow]

def Shape.repetitions : Shape → Nat
  | .signed .. => 0
  | .list _ child => 1 + child.repetitions
  | .struct _ child => child.repetitions

def Shape.definitions : Shape → Nat
  | .signed site _ => site.nullable.toNat
  | .list node child => node.site.nullable.toNat + 1 + child.definitions
  | .struct site child => site.nullable.toNat + child.definitions

def Shape.steps (ctx : Repeated.Context) : Shape → List Repeated.Step
  | .signed site _ => (ctx.enter site).steps
  | .list node child => child.steps (node.enter ctx)
  | .struct site child => child.steps (ctx.enter site)

def Shape.leaf : Shape → Site × Kind
  | .signed site kind => (site, kind)
  | .list _ child => child.leaf
  | .struct _ child => child.leaf

structure Plan where
  outer : ListSite
  child : Shape
  deriving Repr

def Plan.shape (plan : Plan) : Shape := .list plan.outer plan.child
def Plan.arrow (plan : Plan) : Arrow.RecursiveSchema.Schema := ⟨[plan.shape.arrow]⟩

/-- Each step consumes the original consecutive outer and wrapper entries.
The leaf consumes the last entry. Fuel includes the physical wrapper. -/
inductive PathWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry) :
    Nat → Repeated.Context → Nat → Shape → Nat → Prop where
  | signed {fuel ctx ordinal site kind} :
      SignedWire original ctx ordinal site kind →
      PathWire reader original (fuel + 1) ctx ordinal (.signed site kind) (ordinal + 1)
  | list {fuel ctx ordinal node child stop} :
      ListWire reader original ctx ordinal node →
      PathWire reader original fuel (node.enter ctx) (ordinal + 2) child stop →
      PathWire reader original (fuel + 2) ctx ordinal (.list node child) stop

structure SchemaWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (fuel : Nat) (plan : Plan) : Prop where
  root : ∃ entry, original[0]? = some entry ∧ Root entry
  path : PathWire reader original fuel {} 1 plan.shape original.size

structure Compiled (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) where
  container : ThriftCompact.Traversal.Field
  items : List Footer.ColumnOrder.Item
  plan : Plan
  original : Footer.NestedLeaf.readItems limits.footer snapshot = .ok (container, items)
  aligned : snapshot.metadata.schema.length = items.length
  grammar : SchemaWire (Footer.ColumnOrder.footerReader limits.footer snapshot)
    (entries snapshot items) (limits.maxSchemaDepth - 1) plan

structure Source (limits : Snapshot.Limits) (bytes : Bytes) where
  snapshot : Snapshot.Checked
  schema : Compiled limits snapshot
  original : Snapshot.check (Failure := Unit) limits bytes = .ok snapshot

inductive Error where
  | original (error : TwoList.Error)
  | depth (ordinal : Nat)
  | extent (next actual : Nat)
  deriving DecidableEq, Repr

end

private structure Parsed (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (fuel : Nat) (ctx : Repeated.Context) (ordinal : Nat) where
  shape : Shape
  next : Nat
  wire : PathWire reader original fuel ctx ordinal shape next

private def readPath (reader : ThriftCompact.Traversal.Reader) (original : Array Entry) :
    (fuel : Nat) → (ctx : Repeated.Context) → (ordinal : Nat) →
      Except Error (Parsed reader original fuel ctx ordinal)
  | 0, _, ordinal => .error (.depth ordinal)
  | fuel + 1, ctx, ordinal => do
    let entry ← (TwoList.entryAt original ordinal).mapError .original
    if entry.val.1.physicalType.isSome then
      let ⟨(site, kind), wire⟩ ← (TwoList.readLeaf original ctx ordinal).mapError .original
      return ⟨.signed site kind, ordinal + 1, .signed wire⟩
    else
      match remaining : fuel with
      | 0 => throw (.depth (ordinal + 1))
      | rest + 1 =>
        let ⟨node, wire⟩ ← (TwoList.readList reader original ctx ordinal).mapError .original
        let parsed ← readPath reader original rest (node.enter ctx) (ordinal + 2)
        return ⟨.list node parsed.shape, parsed.next, by rw [remaining]; exact .list wire parsed.wire⟩

/-- Consume exactly the canonical one-child root, one or more LIST pairs,
and one unannotated signed leaf from the original Compact footer. -/
public def compile (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) :
    Except Error (Compiled limits snapshot) := do
  match found : Footer.NestedLeaf.readItems limits.footer snapshot with
  | .error cause => throw (.original (.items cause))
  | .ok (container, items) =>
    let original := entries snapshot items
    if aligned : snapshot.metadata.schema.length = items.length then
      let reader := Footer.ColumnOrder.footerReader limits.footer snapshot
      let ⟨root, foundRoot⟩ ← (TwoList.entryAt original 0).mapError .original
      if rootShape : Root root then
        let parsed ← readPath reader original (limits.maxSchemaDepth - 1) {} 1
        match shape : parsed.shape with
        | .signed .. | .struct .. => throw (.original (.shape 1))
        | .list outer child =>
          if exactEnd : parsed.next = original.size then
            return ⟨container, items, ⟨outer, child⟩, found, aligned, ⟨⟨root, foundRoot, rootShape⟩,
              by
                change PathWire reader original _ {} 1 (.list outer child) original.size
                rw [← shape, ← exactEnd]
                exact parsed.wire⟩⟩
          else throw (.extent parsed.next original.size)
      else throw (.original (.shape 0))
    else throw (.original (.extent snapshot.metadata.schema.length items.length))

public def openFile (limits : Snapshot.Limits) (bytes : Bytes) : Except Error (Source limits bytes) := do
  match original : Snapshot.check (Failure := Unit) limits bytes with
  | .error cause => throw (.original (.snapshot cause))
  | .ok snapshot => return ⟨snapshot, ← compile limits snapshot, original⟩

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath
