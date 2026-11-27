module

public import Silmaril.Formats.Arrow.Binary.Stream.Defs
public import Silmaril.Formats.Arrow.Events.Defs

/-! # Standard Arrow events for one plain Binary field

The adapter consumes the checked cursor for either admitted framing profile.
The descriptor labels the sole column, whose present cells are opaque bytes. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.Binary.Stream.Events

open Silmaril.Relational

inductive Kind where
  | binary
  deriving DecidableEq, Repr

abbrev Cell (_ : Kind) := KBytes

def schema (field : Binary.Field) : Scan.Schema Binary.Field Kind :=
  ⟨1, fun _ => (field, .binary)⟩

abbrev Batch (field : Binary.Field) := Arrow.Events.Batch (schema field) Cell
abbrev Trace (field : Binary.Field) := Arrow.Events.Trace (schema field) Cell Stream.Error
abbrev EventStream := Arrow.Events.EventStream Binary.Field Cell Stream.Error

/-- Preserve every slot and row, including an explicitly empty record. -/
def ofBatch (field : Binary.Field) (record : Stream.Batch) : Batch field :=
  ⟨record.values.length, fun _ => record.values, fun _ => rfl⟩

def termination : Stream.End → Arrow.Events.Termination Stream.Error
  | .eos _ => .eos
  | .failed failure => .readError (.record failure)

def ofTrace (field : Binary.Field) (trace : Stream.Trace) : Trace field :=
  ⟨trace.batches.map (ofBatch field), termination trace.terminal⟩

/-- The field declared at open labels all events from this cursor. -/
inductive Cursor : Scan.Schema Binary.Field Kind → Type where
  | at (field : Binary.Field) (source : Stream.Cursor) : Cursor (schema field)

def reader (limits : Limits) (framing : Stream.Framing) :
    Arrow.Events.BatchReader KBytes Binary.Field Cell Stream.Error Cursor where
  openInput input :=
    ((Stream.openInput limits framing input).mapError .schema).map fun cursor =>
      ⟨schema cursor.field, .at cursor.field cursor⟩
  next
    | .at field source =>
      (source.next.mapError .record).map
        (Option.map fun (record, after) => (ofBatch field record, .at field after))
  close _ := .ok ()

/-- One extra attempt checks EOS or the first limit failure after exactly
the permitted number of records. The original cursor retains the carrier. -/
def readAll (limits : Limits) (framing : Stream.Framing) (input : KBytes) : EventStream :=
  (reader limits framing).read (limits.batches + 1) input

end Silmaril.Formats.Arrow.Binary.Stream.Events
