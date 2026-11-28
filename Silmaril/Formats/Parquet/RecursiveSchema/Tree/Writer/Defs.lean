module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms

/-! A checked, schema-driven signed Tree writer using the native V1
payload and Compact footer assemblers. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer

open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Repeated.Writer
open ListPath.Writer (frameSize)
open RecursiveSchema.ListPath.Rows (Atom)

@[expose] public section

abbrev Input := ListPath.Writer.Input
abbrev Output := ListPath.Writer.Output

structure Limits extends ListPath.Writer.Limits where
  maxColumns : Nat := 1024
  maxGroupSlots : Nat := 8 * 1024 * 1024

def Limits.reader (limits : Limits) : Rows.Limits :=
  ⟨limits.chunk, limits.maxColumns, limits.maxGroupSlots⟩

inductive Error where
  | schema (cause : Schema.Error)
  | groupLimit (actual : Nat)
  | totalRowLimit (actual : Nat)
  | columnLimit (actual : Nat)
  | rowCount (group declared actual : Nat)
  | rowLimit (group actual : Nat)
  | projection (group : Nat)
  | slotLimit (group column actual : Nat)
  | groupSlotLimit (group actual : Nat)
  | totalSlotLimit (group actual : Nat)
  | page (group column : Nat) (cause : ListPath.Writer.Error)
  | openReadback (cause : Repeated.Error)
  | readback (group : Nat) (cause : Rows.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

structure WrittenColumn where
  index : Schema.ColumnIndex
  page : PlainV1Writer.Encoded

structure ColumnWire (limits : Limits) (checksum : Bool) (leaf : LeafPlan)
    (offset : Nat) (atoms : List Atom) (column : WrittenColumn) : Prop where
  frame : ListPath.Writer.FrameWire limits.toLimits checksum leaf.path.shape offset atoms column.page
  index : column.index = ⟨leaf.path.kind, leaf.path.site.location.path, atoms.length, offset, frameSize column.page⟩
  pageCap : 1 ≤ limits.chunk.framing.maxPages
  slotCap : atoms.length ≤ ListPath.Writer.slotBudget limits.toLimits
  levelCap : ListPath.Writer.LevelsFit limits.toLimits leaf.path.shape atoms.length

inductive ColumnsWire (limits : Limits) (checksum : Bool) :
    Nat → List LeafPlan → List (List Atom) → List WrittenColumn → Prop where
  | nil (offset : Nat) : ColumnsWire limits checksum offset [] [] []
  | cons {offset leaf leaves atoms traces first rest} :
      ColumnWire limits checksum leaf offset atoms first →
      ColumnsWire limits checksum (offset + frameSize first.page) leaves traces rest →
      ColumnsWire limits checksum offset (leaf :: leaves) (atoms :: traces) (first :: rest)

structure WrittenGroup where
  index : Schema.GroupIndex
  columns : List WrittenColumn
  traces : Rows.Projection.Traces
  slots : Nat

def WrittenGroup.size (group : WrittenGroup) : Nat :=
  group.columns.foldl (fun bytes column => bytes + frameSize column.page) 0

structure GroupWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (checksum : Bool) (compiled : Compiled schemaLimits snapshot)
    (offset priorSlots : Nat) (input : Observation) (output : WrittenGroup) : Prop where
  counts : Rows.Projection.counts (Rows.schemaWidths compiled) compiled.leaves.size schemaLimits.maxSchemaDepth
    compiled.schema.fields input.rows = some (output.traces.map List.length)
  projected : Rows.Projection.trace (Rows.schemaWidths compiled) compiled.leaves.size schemaLimits.maxSchemaDepth
    compiled.schema.fields input.rows = some output.traces
  encoded : ColumnsWire limits checksum offset compiled.leaves.toList output.traces.toList output.columns
  index : output.index = ⟨input.rowCount, output.columns.map WrittenColumn.index⟩
  rowCount : input.rowCount = input.rows.length
  rowCap : input.rowCount ≤ limits.chunk.maxRows
  slots : output.slots = (output.traces.map List.length).toList.sum
  slotCap : output.slots ≤ limits.maxGroupSlots
  fileSlotCap : priorSlots + output.slots ≤ limits.maxTotalSlots

inductive GroupsWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (checksum : Bool) (compiled : Compiled schemaLimits snapshot) :
    Nat → Nat → List Observation → List WrittenGroup → Prop where
  | nil (offset priorSlots : Nat) : GroupsWire limits checksum compiled offset priorSlots [] []
  | cons {offset priorSlots input inputs group groups} :
      GroupWire limits checksum compiled offset priorSlots input group →
      GroupsWire limits checksum compiled (offset + group.size) (priorSlots + group.slots) inputs groups →
      GroupsWire limits checksum compiled offset priorSlots (input :: inputs) (group :: groups)

def payload (groups : List WrittenGroup) : Bytes :=
  groups.foldl (fun bytes group =>
    group.columns.foldl (fun bytes column => (bytes.append column.page.headerBytes).append column.page.body) bytes)
    .empty

structure Construction (limits : Limits) (input : Input) (output : Output) (groups : List WrittenGroup) : Prop where
  groupCap : input.groups.length ≤ ListPath.Writer.groupBudget limits.toLimits
  rowCap : ListPath.Writer.totalRows input < 2^63 ∧ ListPath.Writer.totalRows input ≤ limits.maxTotalRows
  original : ∃ declared schemaOnly source,
    Schema.planWith limits.schema true input.schema = .ok declared ∧
    Schema.wrap limits.schema .empty declared [] = .ok schemaOnly ∧
    Tree.openFile limits.schema.snapshot schemaOnly.bytes = .ok source ∧
    source.schema.arrow = input.schema ∧ source.schema.leaves.size ≤ limits.maxColumns ∧
    GroupsWire limits input.checksum source.schema 4 0 input.groups groups ∧
    let indices := groups.map WrittenGroup.index
    Schema.wrap limits.schema (payload groups) declared indices = .ok ⟨output.bytes, output.footer⟩ ∧
    output.metadata = Schema.metadata declared indices

structure Built (limits : Limits) (input : Input) where
  output : Output
  groups : List WrittenGroup
  construction : Construction limits input output groups

def GroupReadback {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (compiled : Compiled schemaLimits snapshot)
    (ordinal : Nat) (input : Observation) (written : WrittenGroup) : Prop :=
  ∃ result, Rows.readGroupChecked compiled limits.reader ordinal = .ok result ∧
    result.observation = input ∧ ((Rows.tapes result.inputs).map Occurrences.Tape.atoms) = written.traces

inductive GroupsReadback {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (compiled : Compiled schemaLimits snapshot) :
    Nat → List Observation → List WrittenGroup → Prop where
  | nil (ordinal : Nat) : GroupsReadback limits compiled ordinal [] []
  | cons {ordinal input inputs group groups} :
      GroupReadback limits compiled ordinal input group →
      GroupsReadback limits compiled (ordinal + 1) inputs groups →
      GroupsReadback limits compiled ordinal (input :: inputs) (group :: groups)

structure Readback (limits : Limits) (input : Input) (output : Output) (groups : List WrittenGroup) : Prop where
  original : ∃ source,
    Tree.openFile limits.schema.snapshot output.bytes = .ok source ∧ source.snapshot.bytes = output.bytes ∧
    source.schema.arrow = input.schema ∧ source.snapshot.footer = output.footer ∧
    source.snapshot.metadata = output.metadata ∧ source.snapshot.groupCount = input.groups.length ∧
    GroupsReadback limits source.schema 0 input.groups groups

structure Checked (limits : Limits) (input : Input) extends Built limits input where
  readback : Readback limits input output groups

end

private def require (condition : Prop) [Decidable condition] (error : Error) : Except Error (PLift condition) :=
  if valid : condition then .ok ⟨valid⟩ else .error error

private def checked {α ε : Type} (result : Except ε α) (report : ε → Error) :
    Except Error {value // result = .ok value} :=
  match result with
  | .ok value => .ok ⟨value, rfl⟩
  | .error cause => .error (report cause)

private def writeColumn (limits : Limits) (checksum : Bool)
    (group offset : Nat) (leaf : LeafPlan) (atoms : List Atom) :
    Except Error {column // ColumnWire limits checksum leaf offset atoms column} := do
  let fail := Error.page group leaf.column
  let slotCount := atoms.length
  let ⟨pageCap⟩ ← require (1 ≤ limits.chunk.framing.maxPages) (fail (.pageLimit group))
  let ⟨slotCap⟩ ← require (slotCount ≤ ListPath.Writer.slotBudget limits.toLimits)
    (.slotLimit group leaf.column slotCount)
  let ⟨levelCap⟩ ← (ListPath.Writer.checkLevels limits.toLimits leaf.path.shape group slotCount).mapError fail
  let ⟨page, wire⟩ ← (ListPath.Writer.writeFrame limits.toLimits checksum leaf.path.shape group offset atoms).mapError fail
  return ⟨⟨⟨leaf.path.kind, leaf.path.site.location.path, slotCount, offset, frameSize page⟩, page⟩,
    ⟨wire, rfl, pageCap, slotCap, levelCap⟩⟩

private def writeColumns (limits : Limits) (checksum : Bool) (group : Nat) :
    (offset : Nat) → (leaves : List LeafPlan) → (traces : List (List Atom)) →
      Except Error {columns // ColumnsWire limits checksum offset leaves traces columns}
  | offset, [], [] => .ok ⟨[], .nil offset⟩
  | offset, leaf :: leaves, atoms :: traces => do
    let ⟨first, wire⟩ ← writeColumn limits checksum group offset leaf atoms
    let ⟨rest, tail⟩ ← writeColumns limits checksum group (offset + frameSize first.page) leaves traces
    return ⟨first :: rest, .cons wire tail⟩
  | _, _, _ => .error (.projection group)

private def writeGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (checksum : Bool) (compiled : Compiled schemaLimits snapshot)
    (ordinal offset priorSlots : Nat) (input : Observation) :
    Except Error {group // GroupWire limits checksum compiled offset priorSlots input group} := do
  let ⟨rowCount⟩ ← require (input.rowCount = input.rows.length)
    (.rowCount ordinal input.rowCount input.rows.length)
  let ⟨rowCap⟩ ← require (input.rowCount ≤ limits.chunk.maxRows) (.rowLimit ordinal input.rowCount)
  let widths := Rows.schemaWidths compiled
  let count := compiled.leaves.size
  let depth := schemaLimits.maxSchemaDepth
  let fields := compiled.schema.fields
  match counted : Rows.Projection.counts widths count depth fields input.rows with
  | none => throw (.projection ordinal)
  | some slotCounts =>
    for (slots, column) in slotCounts.toList.zipIdx do
      if slots > ListPath.Writer.slotBudget limits.toLimits then throw (.slotLimit ordinal column slots)
    let slots := slotCounts.toList.sum
    let ⟨groupCap⟩ ← require (slots ≤ limits.maxGroupSlots) (.groupSlotLimit ordinal slots)
    let ⟨fileCap⟩ ← require (priorSlots + slots ≤ limits.maxTotalSlots) (.totalSlotLimit ordinal (priorSlots + slots))
    match projected : Rows.Projection.trace widths count depth fields input.rows with
    | none => throw (.projection ordinal)
    | some traces =>
      let ⟨exactCounts⟩ ← require (slotCounts = traces.map List.length) (.projection ordinal)
      let ⟨columns, encoded⟩ ← writeColumns limits checksum ordinal offset compiled.leaves.toList traces.toList
      return ⟨⟨⟨input.rowCount, columns.map WrittenColumn.index⟩, columns, traces, slots⟩,
        ⟨counted.trans (congrArg some exactCounts), projected, encoded, rfl, rowCount, rowCap,
          congrArg (fun counts => counts.toList.sum) exactCounts, groupCap, fileCap⟩⟩

private def pack {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (checksum : Bool) (compiled : Compiled schemaLimits snapshot) :
    (inputs : List Observation) → (ordinal offset priorSlots : Nat) →
      Except Error {groups // GroupsWire limits checksum compiled offset priorSlots inputs groups}
  | [], _, offset, priorSlots => .ok ⟨[], .nil offset priorSlots⟩
  | input :: inputs, ordinal, offset, priorSlots => do
    let ⟨group, wire⟩ ← writeGroup limits checksum compiled ordinal offset priorSlots input
    let ⟨groups, tail⟩ ← pack limits checksum compiled inputs (ordinal + 1)
      (offset + group.size) (priorSlots + group.slots)
    return ⟨group :: groups, .cons wire tail⟩

/-- Compile the emitted schema-only footer and use its ordered leaf plan
to build each physical column and the final file envelope. -/
public def build (limits : Limits) (input : Input) : Except Error (Built limits input) := do
  let ⟨groupCap⟩ ← require (input.groups.length ≤ ListPath.Writer.groupBudget limits.toLimits)
    (.groupLimit input.groups.length)
  let totalRows := ListPath.Writer.totalRows input
  let ⟨rowCap⟩ ← require (totalRows < 2^63 ∧ totalRows ≤ limits.maxTotalRows) (.totalRowLimit totalRows)
  let ⟨declared, planned⟩ ← checked (Schema.planWith limits.schema true input.schema) .schema
  let ⟨schemaOnly, wrapped⟩ ← checked (Schema.wrap limits.schema .empty declared []) .schema
  let ⟨source, opened⟩ ← checked (Tree.openFile limits.schema.snapshot schemaOnly.bytes) .openReadback
  let ⟨same⟩ ← require (Schema.equal limits.schema.snapshot.maxSchemaDepth source.schema.arrow input.schema = true)
    .readbackMismatch
  let ⟨columnsCap⟩ ← require (source.schema.leaves.size ≤ limits.maxColumns) (.columnLimit source.schema.leaves.size)
  let ⟨groups, packed⟩ ← pack limits input.checksum source.schema input.groups 0 4 0
  let indices := groups.map WrittenGroup.index
  let ⟨file, original⟩ ← checked (Schema.wrap limits.schema (payload groups) declared indices) .schema
  return ⟨⟨file.bytes, file.footer, Schema.metadata declared indices⟩, groups,
    ⟨groupCap, rowCap, declared, schemaOnly, source, planned, wrapped, opened,
      Schema.equal_exact same, columnsCap, packed, original, rfl⟩⟩

private def readGroups {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (compiled : Compiled schemaLimits snapshot) :
    (ordinal : Nat) → (inputs : List Observation) → (groups : List WrittenGroup) →
      Except Error (PLift (GroupsReadback limits compiled ordinal inputs groups))
  | ordinal, [], [] => .ok ⟨.nil ordinal⟩
  | ordinal, input :: inputs, group :: groups => do
    let ⟨result, read⟩ ← checked (Rows.readGroupChecked compiled limits.reader ordinal) (.readback ordinal)
    let ⟨same⟩ ← require (Arrow.RecursiveSchema.Batch.Writer.agrees schemaLimits.maxSchemaDepth
      result.observation input = true) .readbackMismatch
    let ⟨traces⟩ ← require ((Rows.tapes result.inputs).map Occurrences.Tape.atoms = group.traces) .readbackMismatch
    let ⟨rest⟩ ← readGroups limits compiled (ordinal + 1) inputs groups
    return ⟨.cons ⟨result, read, Arrow.RecursiveSchema.Batch.Writer.agrees_exact same, traces⟩ rest⟩
  | _, _, _ => .error .readbackMismatch

/-- Accept the emitted file only after the original Tree reader checks
every group and its complete ordered signed traces. -/
public def certify (limits : Limits) (input : Input) (built : Built limits input) :
    Except Error (PLift (Readback limits input built.output built.groups)) := do
  let ⟨source, opened⟩ ← checked (Tree.openFile limits.schema.snapshot built.output.bytes) .openReadback
  let ⟨same⟩ ← require (Schema.equal limits.schema.snapshot.maxSchemaDepth source.schema.arrow input.schema = true)
    .readbackMismatch
  let ⟨original⟩ ← require (source.snapshot.footer = built.output.footer ∧
    source.snapshot.metadata = built.output.metadata ∧ source.snapshot.groupCount = input.groups.length)
    .readbackMismatch
  let ⟨groups⟩ ← readGroups limits source.schema 0 input.groups built.groups
  have bytes := (Snapshot.checkRecursive_exact source.original).2.1
  return ⟨source, opened, bytes, Schema.equal_exact same, original.1, original.2.1, original.2.2, groups⟩

@[expose] public section

def emitChecked (limits : Limits) (input : Input) : Except Error (Checked limits input) := do
  let built ← build limits input
  let ⟨readback⟩ ← certify limits input built
  return ⟨built, readback⟩

def emit (limits : Limits) (input : Input) : Except Error Output :=
  (emitChecked limits input).map (·.output)

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer
