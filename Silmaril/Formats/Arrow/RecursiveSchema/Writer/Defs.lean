module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Native schema-only V5 IPC for the recursive signed integer, Struct and
List profile. Sizing and field-budget checks run before byte construction. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Writer

@[expose] public section

namespace Wire

open MetadataWriter.Wire (words halfwords pad fieldOffsets messagePrefix schemaPayloadOf)

def typeFragment : RecursiveSchema.Wire.Kind → KBytes
  | .int32 => words [halfwords 8 12, halfwords 4 8, 8, 32, 1]
  | .int64 => words [halfwords 8 12, halfwords 4 8, 8, 64, 1]
  | .struct | .list => words [halfwords 4 4, 0, 8, 0, 0]

/-- Include the string length and terminator only for an explicitly present name. -/
def nameSize : Option String → Nat
  | none => 0
  | some name => 5 + name.utf8ByteSize

def nameFragment : Option String → KBytes
  | none => KBytes.empty
  | some name =>
    words [name.utf8ByteSize] ++
      (Arrow.Writer.emitWords 1 (name.toByteArray.data.toList.map UInt8.toNat) ++ KBytes.zeros 1)

def vectorEnd (children : Nat) : Nat :=
  72 + 4 * children

/-- Bytes in this field before any child fragment, including its optional
name, child-reference vector, and alignment padding. -/
def fieldPrefixSize (name : Option String) (children : Nat) : Nat :=
  let size := vectorEnd children + nameSize name
  size + Arrow.Writer.padding size

/-- The shared vector builder targets the table at byte 12 of a fragment.
The Field vtable follows the object at byte 32 and its signed displacement
is −20. The type table is at byte 56 and the child vector starts at 68. -/
def fieldHeader (name : Option String) (nullable : Bool) (kind : RecursiveSchema.Wire.Kind)
    (children : Nat) : KBytes :=
  let nameRef := if name.isSome then vectorEnd children - 16 else 0
  let nameSlot := if name.isSome then 4 else 0
  let nullableTag := (if nullable then 1 else 0) + kind.tag * 256
  words [0, 0, 0, 2^32 - 20, nameRef, nullableTag, 32, 40,
    halfwords 16 20, halfwords nameSlot 8, halfwords 9 12, halfwords 0 16] ++ typeFragment kind

def fieldPrefix (name : Option String) (nullable : Bool) (kind : RecursiveSchema.Wire.Kind)
    (children : List KBytes) : KBytes :=
  let offsets := fieldOffsets 72 (fieldPrefixSize name children.length) children
  pad (fieldHeader name nullable kind children.length ++
    (words (children.length :: offsets) ++ nameFragment name))

def fieldFragment (field : Field) : KBytes :=
  match field with
  | .node name nullable kind fields =>
    let children := fields.map fieldFragment
    fieldPrefix name nullable kind children ++ children.foldr (· ++ ·) KBytes.empty

def fieldSize (field : Field) : Nat :=
  match field with
  | .node name _ _ children =>
    fieldPrefixSize name children.length + (children.map fieldSize).sum

def schemaPrefixSize (roots : Nat) : Nat :=
  let size := 20 + 4 * roots
  48 + size + Arrow.Writer.padding size

def metadataSize (schema : Schema) : Nat :=
  schemaPrefixSize schema.fields.length + (schema.fields.map fieldSize).sum

def metadata (schema : Schema) : KBytes :=
  messagePrefix 1 56 0 ++ schemaPayloadOf (schema.fields.map fieldFragment)

end Wire

inductive Error where
  | arity (ordinal : Nat) (kind : RecursiveSchema.Wire.Kind) (children : Nat)
  | depth (ordinal : Nat)
  | fields (ordinal : Nat)
  | offsetLimit (bytes : Nat)
  | metadataLimit (bytes : Nat)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

structure Budget where
  fields : Nat
  bytes : Nat
  deriving DecidableEq, Repr

/-- The metadata limit also bounds each unsigned forward reference and
string or vector extent. V5 modern framing uses a signed 32-bit length. -/
def checkSize (limits : Limits) (bytes : Nat) : Except Error Unit :=
  if bytes ≥ 2^31 then .error (.offsetLimit bytes)
  else if bytes > limits.ipc.metadataBytes then .error (.metadataLimit bytes)
  else .ok ()

def planFields (visit : Field → Budget → Except Error Budget) :
    List Field → Budget → Except Error Budget
  | [], budget => .ok budget
  | field :: tail, budget => do
    let next ← visit field budget
    planFields visit tail next

def planField (limits : Limits) : Nat → Field → Budget → Except Error Budget
  | 0, _, budget => .error (.depth budget.fields)
  | depth + 1, .node name _ kind children, budget => do
    if budget.fields ≥ limits.ipc.fields then throw (.fields budget.fields)
    let count := children.length
    if !validArity kind count then throw (.arity budget.fields kind count)
    let bytes := budget.bytes + Wire.fieldPrefixSize name count
    checkSize limits bytes
    planFields (planField limits depth) children ⟨budget.fields + 1, bytes⟩

def plan (limits : Limits) (schema : Schema) : Except Error Budget := do
  let bytes := Wire.schemaPrefixSize schema.fields.length
  checkSize limits bytes
  planFields (planField limits limits.depth) schema.fields ⟨0, bytes⟩

/-- Serialize the bodyless Schema frame for use at the front of a stream. -/
def serializeFrame (limits : Limits) (schema : Schema) : Except Error KBytes := do
  let budget ← plan limits schema
  return StreamWriter.envelopeBytes budget.bytes ++ Wire.metadata schema

/-- Emit one bodyless Schema message and the explicit modern EOS. -/
def serialize (limits : Limits) (schema : Schema) : Except Error KBytes := do
  let budget ← plan limits schema
  return StreamWriter.envelopeBytes budget.bytes ++ (Wire.metadata schema ++ StreamWriter.eos)

def equalFields (equal : Field → Field → Bool) : List Field → List Field → Bool
  | [], [] => true
  | left :: lefts, right :: rights => equal left right && equalFields equal lefts rights
  | _, _ => false

def equalField : Nat → Field → Field → Bool
  | 0, _, _ => false
  | depth + 1, .node name nullable kind children, .node otherName otherNullable otherKind otherChildren =>
    name == otherName && nullable == otherNullable && kind == otherKind &&
      equalFields (equalField depth) children otherChildren

def agrees (depth : Nat) (schema : Schema) (decoded : Stream.Trace) : Bool :=
  equalFields (equalField depth) decoded.schema.fields schema.fields &&
    decoded.batches.isEmpty && decoded.terminal == .eos 0 decoded.schemaEnd

/-- Certify the real IPC bytes using the unchanged native recursive reader. -/
def emit (limits : Limits) (schema : Schema) : Except Error KBytes := do
  let bytes ← serialize limits schema
  let decoded ← (Stream.read { schema := limits } bytes).mapError .readback
  if agrees limits.depth schema decoded then return bytes else throw .readbackMismatch

/-- An emitted carrier contains exactly the planned metadata and an EOS
marker, and the native reader recovers the admitted recursive schema. -/
structure EmissionWire (limits : Limits) (schema : Schema) (bytes : KBytes) : Prop where
  construction : ∃ budget, plan limits schema = .ok budget ∧
    budget.bytes = Wire.metadataSize schema ∧ budget.bytes = (Wire.metadata schema).len ∧
    budget.bytes < 2^31 ∧ budget.bytes ≤ limits.ipc.metadataBytes ∧
    bytes = StreamWriter.envelopeBytes budget.bytes ++ (Wire.metadata schema ++ StreamWriter.eos)
  readback : ∃ offset,
    Stream.read { schema := limits } bytes = .ok ⟨schema, offset, [], .eos 0 offset⟩ ∧
    EnvelopeWire limits.ipc bytes.toList offset .eos ∧ offset + 8 = bytes.len

end

end Silmaril.Formats.Arrow.RecursiveSchema.Writer
