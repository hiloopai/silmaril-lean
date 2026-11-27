module

public import Silmaril.Formats.Parquet.ListFile.Multi.Defs
public import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Defs

/-! Opt-in conversion from the complete checked Parquet LIST trace to
the native Arrow IPC LIST stream. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.ToIpc

open Silmaril.Relational

structure Limits where
  parquet : Multi.Limits := {}
  ipc : Arrow.ListInt32.Stream.Limits := {}

abbrev SourceTrace := Arrow.Events.EventStream String ListFile.Cell Multi.Error

inductive Error where
  | source (cause : Multi.Error)
  | closed
  | schemaWidth (actual : Nat)
  | writer (cause : Arrow.ListInt32.Stream.Writer.Error)
  deriving DecidableEq, Repr

/-- An error has no IPC carrier. The original source observation is kept
regardless of the writer's outcome. -/
structure Result where
  trace : SourceTrace
  wire : Except Error KBytes

/-- The parent and child names come from the checked schema elements.
The admitted nullable LIST and nullable INT32 types are fixed. -/
def fieldOf (checked : ListFile.Checked) : Arrow.ListInt32.Field :=
  ⟨checked.shape.outer.name, checked.shape.element.name⟩

/-- A complete one-column trace contributes exactly one native batch per
source batch. A terminal source error takes precedence over writer limits. -/
def writeTrace (limits : Arrow.ListInt32.Stream.Limits) (childName : String)
    (source : SourceTrace) : Except Error KBytes := do
  let ⟨schema, trace⟩ ← source.mapError .source
  match trace.termination with
  | .readError cause | .closeError cause => throw (.source cause)
  | .closed => throw .closed
  | .eos =>
    if width : schema.width = 1 then
      let column := Fin.cast width.symm (0 : Fin 1)
      let field : Arrow.ListInt32.Field := ⟨(schema.kind column).1, childName⟩
      (Arrow.ListInt32.Stream.Writer.emit limits field (trace.batches.map (·.values column))).mapError .writer
    else throw (.schemaWidth schema.width)

/-- Open the footer once, use the original full group reader and retain its
trace. Publish native IPC bytes only after successful source EOS and writer
readback. -/
def convert (limits : Limits) (source : Bytes) : Result :=
  match ListFile.openFile limits.parquet.file source with
  | .error cause =>
    let error := Multi.Error.openFailure cause
    ⟨.error error, .error (.source error)⟩
  | .ok checked =>
    let trace := Reader.readAll (.ok ⟨ListFile.schema checked, Multi.groupSource limits.parquet checked⟩)
    ⟨trace, writeTrace limits.ipc (fieldOf checked).childName trace⟩

/-- Exact source and native witness over the same ordered, nested rows. -/
structure Readback (limits : Limits) (source : Bytes) (wire : KBytes) : Prop where
  data : ∃ checked groups decoded size,
    ListFile.openFile limits.parquet.file source = .ok checked ∧
    ListFile.OpenWire limits.parquet.file source checked ∧
    (List.range checked.snapshot.groupCount).mapM (Multi.readGroup limits.parquet.maxGroupSlots checked) =
      .ok groups ∧
    List.Forall₂ (Multi.GroupWire limits.parquet.maxGroupSlots checked)
      (List.range checked.snapshot.groupCount) groups ∧
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .eos⟩⟩ ∧
    Arrow.ListInt32.Stream.read limits.ipc wire = .ok decoded ∧
    Arrow.ListInt32.Stream.Writer.Agrees (fieldOf checked) groups decoded ∧
    wire.wf = true ∧
    Arrow.readEnvelope limits.ipc.ipc wire 0 = .ok (.metadata size) ∧
    Arrow.ListInt32.readSchema limits.ipc.ipc (wire.slice 8 size) = .ok (fieldOf checked) ∧
    Arrow.ListInt32.Stream.BatchesWire limits.ipc wire limits.ipc.ipc.batches 0 0 (8 + size) decoded.batches

end Silmaril.Formats.Parquet.ListFile.Multi.ToIpc
