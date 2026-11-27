module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Defs

/-! Schema-only descriptor placement for the checked recursive IPC profile. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement

@[expose] public section

structure Indices where
  node : Nat := 0
  buffer : Nat := 0
  deriving BEq, Repr

def indices (cursor : Batch.Cursor) : Indices :=
  ⟨cursor.nodeIndex, cursor.bufferIndex⟩

inductive Role where
  | values32
  | values64
  | offsets32
  deriving BEq, Repr

/-- The optional buffer immediately after the validity descriptor. -/
def payloadRole : Wire.Kind → Option Role
  | .struct => none
  | .int32 => some .values32
  | .int64 => some .values64
  | .list => some .offsets32

def Indices.payload (start : Indices) (kind : Wire.Kind) : Option (Nat × Role) :=
  (payloadRole kind).map fun role => (start.buffer + 1, role)

def Indices.afterOwn (start : Indices) (kind : Wire.Kind) : Indices :=
  ⟨start.node + 1, start.buffer + 1 + (if (payloadRole kind).isSome then 1 else 0)⟩

/-- Each entry retains its local declaration and original positional
children. Its start gives its FieldNode and validity Buffer ordinals. -/
inductive FieldPlan where
  | field (name : Option String) (nullable : Bool) (kind : Wire.Kind) (start : Indices)
      (children : List FieldPlan)
  deriving BEq, Repr

def FieldPlan.declaration : FieldPlan → Field
  | .field name nullable kind _ children =>
    .node name nullable kind (children.map FieldPlan.declaration)

structure Plan where
  fields : List FieldPlan
  next : Indices
  deriving BEq, Repr

inductive Error where
  | schema (original : RecursiveSchema.Error)
  | depth (node : Nat)
  | arity (node : Nat) (kind : Wire.Kind) (children : Nat)
  deriving DecidableEq, Repr

def placeFields (place : Field → Indices → Except Error (FieldPlan × Indices)) :
    List Field → Indices → Except Error Plan
  | [], start => .ok ⟨[], start⟩
  | field :: fields, start => do
    let (first, middle) ← place field start
    let rest ← placeFields place fields middle
    return ⟨first :: rest.fields, rest.next⟩

def placeField : Nat → Field → Indices → Except Error (FieldPlan × Indices)
  | 0, _, start => .error (.depth start.node)
  | depth + 1, .node name nullable kind children, start => do
    if !validArity kind children.length then throw (.arity start.node kind children.length)
    let descendants ← placeFields (placeField depth) children (start.afterOwn kind)
    return (.field name nullable kind start descendants.fields, descendants.next)

/-- Place the declarations of an in-memory schema at the given depth.
For a native carrier the read entry point first applies the wire budgets. -/
def ofSchema (depth : Nat) (schema : Schema) : Except Error Plan :=
  placeFields (placeField depth) schema.fields {}

/-- Admit one native schema and compute its descriptor ordinals without
requiring a RecordBatch or reading past the schema metadata. -/
def read (limits : RecursiveSchema.Limits) (input : KBytes) :
    Except Error (Schema × Nat × Plan) := do
  let (schema, next) ← (RecursiveSchema.readFrame limits input).mapError .schema
  return (schema, next, ← ofSchema limits.depth schema)

def PayloadBinding (carrier : Carrier) (expected : Option (Nat × Role))
    (original : Option Buffer) : Prop :=
  match expected, original with
  | none, none => True
  | some (index, _), some buffer =>
    Wire.batchBuffer carrier.metadata carrier.header index = .ok buffer
  | _, _ => False

mutual

/-- Relate schema-only ordinals to the original descriptors in a checked
carrier, pairing children in their original positions. -/
inductive FieldBinding (carrier : Carrier) : FieldPlan → FieldLayout → Prop where
  | field {name nullable kind start planned node validity payload checked} :
      Wire.batchNode carrier.metadata carrier.header start.node = .ok node →
      Wire.batchBuffer carrier.metadata carrier.header start.buffer = .ok validity →
      PayloadBinding carrier (start.payload kind) payload →
      FieldsBinding carrier planned checked →
      FieldBinding carrier (.field name nullable kind start planned)
        (.field node validity payload checked)

inductive FieldsBinding (carrier : Carrier) : List FieldPlan → List FieldLayout → Prop where
  | nil : FieldsBinding carrier [] []
  | cons {first rest layout layouts} :
      FieldBinding carrier first layout →
      FieldsBinding carrier rest layouts →
      FieldsBinding carrier (first :: rest) (layout :: layouts)

end

end

end Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement
