module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Thms

/-! Write one complete PLAIN UNCOMPRESSED V1 page per signed child and
original group of a canonical two-LIST path ending in a required or optional Struct. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer

open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Repeated.Writer
open RecursiveSchema (Kind)

@[expose] public section

abbrev Limits := ListPath.Writer.Limits
abbrev Input := ListPath.Writer.Input
abbrev Output := ListPath.Writer.Output

inductive Error where
  | declaration
  | schema (cause : Schema.Error)
  | groupLimit (actual : Nat)
  | totalRowLimit (actual : Nat)
  | rowCount (group expected actual : Nat)
  | rowLimit (group actual : Nat)
  | slotLimit (group actual : Nat)
  | totalSlotLimit (group actual : Nat)
  | projection (group : Nat)
  | column (group : Nat) (side : Side) (cause : ListPath.Writer.Error)
  | openReadback (cause : TwoListStruct.Error)
  | readback (cause : Reader.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

end

private structure SignedField where
  name : String
  nullable : Bool
  kind : Kind

private structure Declaration where
  outer : String
  outerNullable : Bool
  inner : String
  innerNullable : Bool
  element : String
  elementNullable : Bool
  left : SignedField
  right : SignedField

private def signedField (field : Arrow.RecursiveSchema.Field) : Option SignedField :=
  match field with
  | .node (some name) nullable .int32 [] => some ⟨name, nullable, .int32⟩
  | .node (some name) nullable .int64 [] => some ⟨name, nullable, .int64⟩
  | _ => none

private def declaration (schema : Arrow.RecursiveSchema.Schema) : Option Declaration := do
  let [.node (some outer) outerNullable .list
    [.node (some inner) innerNullable .list
      [.node (some element) elementNullable .struct [left, right]]]] := schema.fields | none
  return ⟨outer, outerNullable, inner, innerNullable, element, elementNullable, ← signedField left, ← signedField right⟩

/-- Decide membership in the writer profile without consulting target budgets. -/
public def supportsDeclaration (schema : Arrow.RecursiveSchema.Schema) : Bool :=
  (declaration schema).isSome

public def planSchema (limits : Schema.Limits) (schema : Arrow.RecursiveSchema.Schema) :
    Except Error Schema.Plan := do
  let some shape := declaration schema | throw .declaration
  let ⟨outer, outerNullable, inner, innerNullable, element, elementNullable, left, right⟩ := shape
  let compact := limits.snapshot.footer.compact
  if limits.snapshot.maxSchemaDepth < 7 then throw (.schema (.depth []))
  if min limits.maxFields compact.maxCollectionSize < 8 then throw (.schema .fieldLimit)
  let innerPath := [outer, "list", inner]
  let elementPath := innerPath ++ ["list", element]
  if "schema".utf8ByteSize > compact.maxBinaryBytes then throw (.schema (.nameBudget []))
  for (name, path) in [(outer, [outer]), (inner, innerPath), (element, elementPath),
      (left.name, elementPath ++ [left.name]), (right.name, elementPath ++ [right.name])] do
    if name.utf8ByteSize > compact.maxBinaryBytes then throw (.schema (.nameBudget path))
  return ⟨1, [.list outer outerNullable, .wrapper, .list inner innerNullable, .wrapper,
    .struct element elementNullable 2, .leaf left.name left.nullable left.kind, .leaf right.name right.nullable right.kind]⟩

@[expose] public section

structure WrittenGroup where
  left : ListPath.Writer.WrittenGroup
  right : ListPath.Writer.WrittenGroup

def WrittenGroup.index (plan : Plan) (group : WrittenGroup) : Schema.GroupIndex :=
  ⟨group.left.rows,
    (group.left.index (plan.path .left)).columns ++ (group.right.index (plan.path .right)).columns⟩

def WrittenGroup.middle (group : WrittenGroup) (offset : Nat) : Nat :=
  offset + group.left.page.wire.length

def WrittenGroup.stop (group : WrittenGroup) (offset : Nat) : Nat :=
  group.middle offset + group.right.page.wire.length

structure GroupWire (limits : Limits) (checksum : Bool) (plan : Plan) (offset priorSlots : Nat)
    (input : Observation) (output : WrittenGroup) : Prop where
  projected : ∃ leftRows rightRows,
    Rows.projectRows .left input.rows plan.element.nullable = some leftRows ∧
    Rows.projectRows .right input.rows plan.element.nullable = some rightRows ∧
    ListPath.Writer.GroupWire limits checksum (plan.path .left) offset priorSlots
      ⟨input.rowCount, leftRows⟩ output.left ∧
    ListPath.Writer.GroupWire limits checksum (plan.path .right) (output.middle offset)
      (priorSlots + output.left.slots) ⟨input.rowCount, rightRows⟩ output.right

inductive GroupsWire (limits : Limits) (checksum : Bool) (plan : Plan) :
    Nat → Nat → List Observation → List WrittenGroup → Prop where
  | nil (offset priorSlots : Nat) : GroupsWire limits checksum plan offset priorSlots [] []
  | cons {offset priorSlots input inputs output outputs} :
      GroupWire limits checksum plan offset priorSlots input output →
      GroupsWire limits checksum plan (output.stop offset)
        (priorSlots + output.left.slots + output.right.slots) inputs outputs →
      GroupsWire limits checksum plan offset priorSlots (input :: inputs) (output :: outputs)

def payload (groups : List WrittenGroup) : Bytes :=
  ListPath.Writer.payload (groups.flatMap fun group => [group.left, group.right])

structure Construction (limits : Limits) (input : Input) (output : Output) : Prop where
  groupCap : input.groups.length ≤ ListPath.Writer.groupBudget limits
  rowCap : ListPath.Writer.totalRows input < 2 ^ 63 ∧ ListPath.Writer.totalRows input ≤ limits.maxTotalRows
  original : ∃ declared schemaOnly source groups,
    planSchema limits.schema input.schema = .ok declared ∧
    Schema.wrap limits.schema .empty declared [] = .ok schemaOnly ∧
    TwoListStruct.openFile limits.schema.snapshot schemaOnly.bytes = .ok source ∧
    source.schema.plan.arrow = input.schema ∧
    GroupsWire limits input.checksum source.schema.plan 4 0 input.groups groups ∧
    let indices := groups.map (WrittenGroup.index source.schema.plan)
    Schema.wrap limits.schema (payload groups) declared indices = .ok ⟨output.bytes, output.footer⟩ ∧
    output.metadata = Schema.metadata declared indices

end

private def require (condition : Prop) [Decidable condition] (error : Error) :
    Except Error (PLift condition) :=
  if accepted : condition then .ok ⟨accepted⟩ else .error error

private def checked {α ε : Type} (result : Except ε α) (report : ε → Error) :
    Except Error {value // result = .ok value} :=
  match result with
  | .ok value => .ok ⟨value, rfl⟩
  | .error cause => .error (report cause)

private def projectRows (side : Side) (optional : Bool) (input : Observation) (ordinal : Nat) :
    Except Error {rows // Rows.projectRows side input.rows optional = some rows} :=
  match Rows.projectRows side input.rows optional with
  | none => .error (.projection ordinal)
  | some rows => .ok ⟨rows, rfl⟩

/-- Account for the shared LIST topology before allocating either child projection.
The count treats every reached Struct as one slot for each child. -/
private def writeGroup (limits : Limits) (checksum : Bool) (plan : Plan)
    (ordinal offset priorSlots : Nat) (input : Observation) :
    Except Error {out // GroupWire limits checksum plan offset priorSlots input out} := do
  let actual := input.rows.length
  if actual ≠ input.rowCount then throw (.rowCount ordinal input.rowCount actual)
  if actual > limits.chunk.maxRows then throw (.rowLimit ordinal actual)
  let slots := Rows.slotDemand input.rows
  if slots > ListPath.Writer.slotBudget limits then throw (.slotLimit ordinal slots)
  if priorSlots + 2 * slots > limits.maxTotalSlots then
    throw (.totalSlotLimit ordinal (priorSlots + 2 * slots))
  let ⟨leftRows, leftExact⟩ ← projectRows .left plan.element.nullable input ordinal
  let ⟨rightRows, rightExact⟩ ← projectRows .right plan.element.nullable input ordinal
  let ⟨left, lhs⟩ ← (ListPath.Writer.writeGroup limits checksum (plan.path .left) ordinal offset priorSlots
    ⟨input.rowCount, leftRows⟩).mapError (.column ordinal .left)
  let ⟨right, rhs⟩ ← (ListPath.Writer.writeGroup limits checksum (plan.path .right) ordinal
    (offset + left.page.wire.length) (priorSlots + left.slots)
    ⟨input.rowCount, rightRows⟩).mapError (.column ordinal .right)
  return ⟨⟨left, right⟩, ⟨leftRows, rightRows, leftExact, rightExact, lhs, rhs⟩⟩

private def pack (limits : Limits) (checksum : Bool) (plan : Plan) :
    (inputs : List Observation) → (ordinal offset priorSlots : Nat) →
    Except Error {outputs // GroupsWire limits checksum plan offset priorSlots inputs outputs}
  | [], _, offset, priorSlots => .ok ⟨[], .nil offset priorSlots⟩
  | input :: rest, ordinal, offset, priorSlots => do
    let ⟨group, wire⟩ ← writeGroup limits checksum plan ordinal offset priorSlots input
    let ⟨groups, tail⟩ ← pack limits checksum plan rest (ordinal + 1)
      (group.stop offset) (priorSlots + group.left.slots + group.right.slots)
    return ⟨group :: groups, .cons wire tail⟩

public def build (limits : Limits) (input : Input) : Except Error {out // Construction limits input out} := do
  let ⟨groupCap⟩ ← require (input.groups.length ≤ ListPath.Writer.groupBudget limits)
    (.groupLimit input.groups.length)
  let rows := ListPath.Writer.totalRows input
  let ⟨rowCap⟩ ← require (rows < 2 ^ 63 ∧ rows ≤ limits.maxTotalRows) (.totalRowLimit rows)
  let ⟨declared, planned⟩ ← checked (planSchema limits.schema input.schema) id
  let ⟨schemaOnly, envelope⟩ ← checked (Schema.wrap limits.schema .empty declared []) .schema
  let ⟨source, compiled⟩ ← checked (TwoListStruct.openFile limits.schema.snapshot schemaOnly.bytes) .openReadback
  let ⟨exactSchema⟩ ← require
    (Schema.equal limits.schema.snapshot.maxSchemaDepth source.schema.plan.arrow input.schema = true)
    .readbackMismatch
  let ⟨groups, packed⟩ ← pack limits input.checksum source.schema.plan input.groups 0 4 0
  let indices := groups.map (WrittenGroup.index source.schema.plan)
  let ⟨framed, original⟩ ← checked (Schema.wrap limits.schema (payload groups) declared indices) .schema
  return ⟨⟨framed.bytes, framed.footer, Schema.metadata declared indices⟩, ⟨groupCap, rowCap,
    declared, schemaOnly, source, groups, planned, envelope, compiled,
    Schema.equal_exact exactSchema, packed, original, rfl⟩⟩

@[expose] public section

def serialize (limits : Limits) (input : Input) : Except Error Output :=
  (build limits input).map Subtype.val

def agrees (limits : Limits) (input : Input) (output : Output)
    (source : Source limits.schema.snapshot output.bytes) : Bool :=
  Schema.equal limits.schema.snapshot.maxSchemaDepth source.schema.plan.arrow input.schema &&
    decide (source.snapshot.footer = output.footer ∧ source.snapshot.metadata = output.metadata ∧
      source.snapshot.groupCount = input.groups.length)

/-- Check the final emitted carrier using both original native chunks. -/
def certify (limits : Limits) (input : Input) (output : Output) : Except Error Unit := do
  let source ← (TwoListStruct.openFile limits.schema.snapshot output.bytes).mapError .openReadback
  if !agrees limits input output source then throw .readbackMismatch
  let recovered ← (Reader.readAll limits.chunk source.schema).mapError .readback
  let equal := Arrow.RecursiveSchema.Batch.Writer.agrees limits.schema.snapshot.maxSchemaDepth
  if recovered.isEqv input.groups equal then return () else throw .readbackMismatch

def emit (limits : Limits) (input : Input) : Except Error Output := do
  let output ← serialize limits input
  certify limits input output
  return output

structure Readback (limits : Limits) (input : Input) (output : Output) : Prop where
  original : ∃ (source : Source limits.schema.snapshot output.bytes),
    TwoListStruct.openFile limits.schema.snapshot output.bytes = .ok source ∧
    source.snapshot.bytes = output.bytes ∧
    source.snapshot.footer = output.footer ∧ source.snapshot.metadata = output.metadata ∧
    source.schema.plan.arrow = input.schema ∧ source.snapshot.groupCount = input.groups.length ∧
    Reader.readAll limits.chunk source.schema = .ok input.groups ∧
    List.Forall₂ (Reader.GroupWire limits.chunk source.schema)
      (List.range source.snapshot.groupCount) input.groups

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer
