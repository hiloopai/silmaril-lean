module

public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
public import Silmaril.Formats.Parquet.Footer.ColumnOrder.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs

/-! Export one checked flat PLAIN BYTE_ARRAY leaf declared as Parquet STRING. -/

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8

open Footer.ColumnOrder (FlatLeaf)
open ThriftCompact.Traversal (Field)

inductive Annotation where
  | logical | logicalAndConverted | converted
  deriving DecidableEq, Repr

inductive Error where
  | openFile (cause : File.Error)
  | footer (cause : Footer.ColumnOrder.Error)
  | missingAnnotation
  | logicalMember (tag : Int)
  | logicalPayload
  | convertedType (code : Int)
  | physical (cause : FlatColumn.Error File.PageError)
  | invalidText (group slot : Nat)
  | writer (cause : Arrow.MixedFlat.OrderedWriter.Error)
  deriving DecidableEq, Repr

/-- LogicalType field 1 contains the empty STRING marker. -/
@[expose] def checkLogical (selected : FlatLeaf) (member : Field) : Except Error Unit := do
  if member.id ≠ 1 then throw (.logicalMember member.id)
  if member.type ≠ .payload .struct then throw (.footer (.fieldType member.id))
  let (fields, stop) ← (ThriftCompact.Traversal.readStruct selected.selection.reader member.start).mapError
    (.footer ∘ .compact)
  if stop ≠ member.stop then throw (.footer (.fieldExtent member.id))
  if !fields.isEmpty then throw .logicalPayload

/-- ConvertedType.UTF8 is code zero. Present modern metadata is checked first. -/
@[expose] def classify (logical : Bool) (converted : Option Int) : Except Error Annotation :=
  match logical, converted with
  | true, none => .ok .logical
  | false, none => .error .missingAnnotation
  | _, some code =>
    if code = 0 then .ok (if logical then .logicalAndConverted else .converted)
    else .error (.convertedType code)

@[expose] def readAnnotation (selected : FlatLeaf) : Except Error Annotation := do
  let modern ← selected.logicalMember.mapError .footer
  let _ ← modern.mapM (checkLogical selected)
  let converted ← selected.convertedType.mapError .footer
  classify modern.isSome converted

/-- The annotation evidence names the exact snapshot and column of the physical binding. -/
structure Checked (name : String) (layout : FlatColumn.Layout) where
  physical : File.Checked name layout
  annotation : Annotation
  annotationRead : ∃ limits selected, Footer.ColumnOrder.readFlat limits physical.snapshot
    physical.binding.columnOrdinal = .ok selected ∧ readAnnotation selected = .ok annotation

/-- Apply the existing file and row caps, then inspect the selected original
leaf's annotation at the physical binding's column ordinal. -/
@[expose] def openFile (limits : File.Limits) (input : Bytes) (name : String) (layout : FlatColumn.Layout) :
    Except Error (Checked name layout) := do
  let physical ← (File.openFile limits input name layout).mapError .openFile
  match selected : Footer.ColumnOrder.readFlat limits.snapshot.footer physical.snapshot
      physical.binding.columnOrdinal with
  | .error cause => .error (.footer cause)
  | .ok leaf =>
    match decoded : readAnnotation leaf with
    | .error cause => .error cause
    | .ok annotation => .ok ⟨physical, annotation, limits.snapshot.footer, leaf, selected, decoded⟩

@[expose] def decodeSlot (group : Nat) (item : Option Bytes × Nat) : Except Error (Option String) :=
  item.1.mapM fun bytes =>
    match String.fromUTF8? bytes.data with
    | some text => .ok text
    | none => .error (.invalidText group item.2)

@[expose] def decodeSlots (group : Nat) (raw : List (Option Bytes)) : Except Error (List (Option String)) :=
  raw.zipIdx.mapM (decodeSlot group)

/-- Check the complete physical group, then validate present slots as strict
UTF-8 in original logical row order. Null slots retain their positions. -/
@[expose] def Checked.readGroup {name : String} {layout : FlatColumn.Layout}
    (checked : Checked name layout) (limits : File.Limits) (group : Nat) :
    Except Error (List (Option String)) := do
  let raw ← (checked.physical.readGroup limits group).mapError .physical
  decodeSlots group raw

@[expose] def batch (name : String) (layout : FlatColumn.Layout) (slots : List (Option String)) :
    Arrow.MixedFlat.OrderedWriter.BatchInput :=
  ⟨slots.length, [.utf8View name (layout == .optional) slots]⟩

@[expose] def fields (name : String) (layout : FlatColumn.Layout) : List Arrow.MixedFlat.Field :=
  (batch name layout []).fields

/-- Exhaust and validate the selected leaf before passing its typed string
batches to the ordered IPC writer. -/
@[expose] def convert (parquet : File.Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes)
    (name : String) (layout : FlatColumn.Layout) : Except Error KBytes := do
  let checked ← openFile parquet input name layout
  let groups ← (List.range checked.physical.snapshot.groupCount).mapM (checked.readGroup parquet)
  (Arrow.MixedFlat.OrderedWriter.emit ipc (fields name layout)
    (groups.map (batch name layout))).mapError .writer

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8
