module

public import Silmaril.Formats.Arrow.Metadata.Defs

/-! A checked schema-only Arrow IPC V5 profile for signed Int32 and Int64,
Struct and List. The existing flat and fixed-shape readers remain independent. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema

inductive Field where
  | node (name : Option String) (nullable : Bool) (kind : Wire.Kind) (children : List Field)
  deriving BEq, Repr

structure Schema where
  fields : List Field
  deriving BEq, Repr

structure Limits where
  ipc : Arrow.Limits := {}
  /-- Maximum number of Fields on a path, with root Fields at depth one. -/
  depth : Nat := 32
  deriving Repr

inductive Error where
  | envelope (cause : Arrow.Error)
  | expectedSchema
  | metadata (cause : Arrow.Error)
  | offset (word : Nat) (cause : Arrow.Error)
  | field (position : Nat) (cause : Arrow.Error)
  | arity (position : Nat) (kind : Wire.Kind) (actual : Nat)
  | depth (position : Nat)
  | fields (position : Nat)
  deriving DecidableEq, Repr

def validArity (kind : Wire.Kind) (count : Nat) : Bool :=
  match kind with
  | .int32 | .int64 => count == 0
  | .list => count == 1
  | .struct => true

/-- Walk a checked vector in original slot order. Each sibling receives the
budget left by the preceding sibling's entire subtree. -/
def readFieldsAt (bytes : KBytes) (readField : Nat → Nat → Except Error (Field × Nat)) :
    Nat → Nat → Nat → Except Error (List Field × Nat)
  | 0, _, remaining => .ok ([], remaining)
  | count + 1, word, remaining => do
    let position ← (Wire.fieldOffset bytes word).mapError (.offset word)
    let (field, remaining) ← readField position remaining
    let (fields, remaining) ← readFieldsAt bytes readField count (word + 4) remaining
    return (field :: fields, remaining)

def readFieldAt (bytes : KBytes) : Nat → Nat → Nat → Except Error (Field × Nat)
  | 0, position, _ => .error (.depth position)
  | _ + 1, position, 0 => .error (.fields position)
  | depth + 1, position, remaining + 1 => do
    let header ← (Wire.fieldHeader bytes position).mapError (.field position)
    if !validArity header.kind header.childrenCount then
      throw (.arity position header.kind header.childrenCount)
    let (children, remaining) ← readFieldsAt bytes (readFieldAt bytes depth)
      header.childrenCount header.childrenFirst remaining
    return (.node header.name header.nullable header.kind children, remaining)

/-- Read one original padded V5 Schema message. `limits.ipc.fields` counts
every Field occurrence, including descendants and any repeated references. -/
def readMessage (limits : Limits) (bytes : KBytes) : Except Error Schema := do
  let (first, count) ← (Wire.rootFields limits.ipc bytes).mapError .metadata
  let (fields, _) ← readFieldsAt bytes (readFieldAt bytes limits.depth)
    count first limits.ipc.fields
  return ⟨fields⟩

/-- Read the initial modern Schema frame; the returned byte offset is the
end of the padded metadata. Subsequent frames are outside this profile. -/
def readFrame (limits : Limits) (input : KBytes) : Except Error (Schema × Nat) := do
  if !input.wf then throw (.envelope (.malformed .source))
  let envelope ← (Arrow.readEnvelope limits.ipc input 0).mapError .envelope
  let .metadata size := envelope | throw .expectedSchema
  let schema ← readMessage limits (input.slice 8 size)
  return (schema, 8 + size)

/-- Successful schema admission certifies the immutable carrier for later frames. -/
theorem readFrame_source {limits : Limits} {input : KBytes} {result : Schema × Nat}
    (accepted : readFrame limits input = .ok result) : input.wf = true := by
  cases wf : input.wf <;> simp [readFrame, wf, throw, bind, Except.bind] at accepted ⊢

mutual

/-- The original Field table fixes this node's local metadata and child
vector. Every child is checked at a strictly smaller depth. -/
inductive FieldWire (bytes : KBytes) : Nat → Nat → Field → Nat → Prop where
  | node {depth position header children used} :
      Wire.fieldHeader bytes position = .ok header →
      validArity header.kind header.childrenCount = true →
      FieldsWire bytes depth header.childrenFirst header.childrenCount children used →
      FieldWire bytes (depth + 1) position
        (.node header.name header.nullable header.kind children) (used + 1)

/-- Each vector element binds to the table referenced by its own original
offset word. The last index counts field occurrences, including descendants. -/
inductive FieldsWire (bytes : KBytes) : Nat → Nat → Nat → List Field → Nat → Prop where
  | nil {depth word} : FieldsWire bytes depth word 0 [] 0
  | cons {depth word count position field fields usedHead usedTail} :
      Wire.fieldOffset bytes word = .ok position →
      FieldWire bytes depth position field usedHead →
      FieldsWire bytes depth (word + 4) count fields usedTail →
      FieldsWire bytes depth word (count + 1) (field :: fields) (usedHead + usedTail)

end

/-- Bind the ordered AST to the original Schema vector and bound the total
number of Field occurrences across that vector and all of its descendants. -/
def SchemaWire (limits : Limits) (bytes : KBytes) (schema : Schema) : Prop :=
  ∃ first count used,
    Wire.rootFields limits.ipc bytes = .ok (first, count) ∧
    FieldsWire bytes limits.depth first count schema.fields used ∧ used ≤ limits.ipc.fields

end Silmaril.Formats.Arrow.RecursiveSchema
