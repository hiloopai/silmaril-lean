module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Field.Defs

/-! Exact external view prefix mismatches. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

namespace PrefixMismatch

open MixedFlat.Events

def columnCause (slot : Nat) : MixedFlat.ColumnError :=
  .view (.slot slot .prefixMismatch)

def mismatchError (ordinal offset field slot : Nat) : Incremental.Error :=
  .batch ordinal offset (.record (.decode (.field field (columnCause slot))))

/-- Admitted fragments through a checked Schema and the successfully
published prefix. The final feed reports the first semantic failure. -/
structure Run (limits : Incremental.Limits) (wire : KBytes) where
  fields : List MixedFlat.Field
  batches : List (Delivered fields)
  ordinal : Nat
  offset : Nat
  field : Nat
  slot : Nat
  ran : ∃ opened final chunk,
    SchemaSteps wire.len (wire.read 0 wire.len) fields (start limits) opened ∧
    RecordSteps wire.len (wire.read 0 wire.len) fields opened batches final ∧
    Arrow.Framing.Incremental.Window (Portable.reference wire) final.position chunk ∧
    feed final chunk = .error (mismatchError ordinal offset field slot)

/-- The prefix mismatch schedule is an admitted field failure. -/
def Run.toField {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Field.Run limits wire :=
  ⟨run.fields, run.batches, run.ordinal, run.offset, run.field, columnCause run.slot, run.ran⟩

def Run.ranges {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    List Stream.BatchRange :=
  run.batches.map (·.record.range)

def Run.cause {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Incremental.Error :=
  mismatchError run.ordinal run.offset run.field run.slot

def Run.trace {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Incremental.Error :=
  .ok ⟨schema run.fields, ⟨run.batches.map Delivered.event, .readError run.cause⟩⟩

/-- The complete prefix replays on the immutable reader and stops at the
same batch, field and slot in the same complete, rejected frame. -/
def Agreement (limits : Incremental.Limits) (wire : KBytes) (run : Run limits wire) : Prop :=
  let input := Portable.reference wire
  let fault := Stream.BatchError.decode (.field run.field (columnCause run.slot))
  ∃ startOffset running range,
    Stream.readSchemaFrame limits.mixed.observation.ipc input = .ok (run.fields, startOffset) ∧
    Replay limits.mixed input run.fields (.ofRunning limits.mixed {} startOffset)
      (run.batches.map Delivered.published) (.ofRunning limits.mixed running run.offset) ∧
    running.ordinal = run.ordinal ∧ range.offset = run.offset ∧
    FieldFailureWire limits input run.fields running range run.field (columnCause run.slot) ∧
    (Position.ofRunning limits.mixed running run.offset).readNext limits.mixed input run.fields =
      .error (.message run.ordinal run.offset fault) ∧
    Stream.read limits.mixed input = .error (.batch run.ordinal fault)

end PrefixMismatch

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure
