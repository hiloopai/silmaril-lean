module

public import Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Defs
public import Silmaril.Formats.Arrow.Events.Defs

/-! A standard Arrow event reader and modern sink for one LargeUtf8 field. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeUtf8.Stream.Events

open Silmaril.Relational

inductive Kind where
  | largeUtf8
  deriving DecidableEq, Repr

abbrev Cell (_ : Kind) := String
abbrev Signature := Scan.Schema LargeUtf8.Field Kind

def schema (field : LargeUtf8.Field) : Signature :=
  ⟨1, fun _ => (field, .largeUtf8)⟩

abbrev Batch (field : LargeUtf8.Field) := Arrow.Events.Batch (schema field) Cell
abbrev Trace (field : LargeUtf8.Field) := Arrow.Events.Trace (schema field) Cell Stream.Error
abbrev EventStream := Arrow.Events.EventStream LargeUtf8.Field Cell Stream.Error

def ofValues (field : LargeUtf8.Field) (values : LargeUtf8.Column) : Batch field :=
  ⟨values.length, fun _ => values, fun _ => rfl⟩

def ofBatch (field : LargeUtf8.Field) (record : Stream.Batch) : Batch field :=
  ofValues field record.values

def slots {field : LargeUtf8.Field} (batch : Batch field) : LargeUtf8.Column :=
  batch.values ⟨0, Nat.zero_lt_one⟩

structure Position where
  remaining : Nat
  ordinal : Nat
  offset : Nat

def Position.advance (position : Position) (record : Stream.Batch) : Position :=
  ⟨position.remaining - 1, position.ordinal + 1, record.range.next⟩

def Position.failure (position : Position) (cause : Stream.Cause) : Stream.Error :=
  .record position.ordinal position.offset cause

def admit (limits : Limits) (framing : Framing) (input : KBytes) :
    Except Stream.Error (LargeUtf8.Field × Nat) :=
  if !input.wf then .error (.schema .source)
  else (Stream.readSchemaFrame limits framing input).mapError .schema

/-- Read one original frame. The native decoder checks batch metadata, body
and column bounds. A complete terminal marker must exhaust the carrier. -/
def readNext (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeUtf8.Field) (position : Position) : Except Stream.Error (Option Stream.Batch) := do
  let envelope ← (framing.readEnvelope limits input position.offset).mapError
    fun cause => position.failure (.ipc (.envelope cause))
  match envelope with
  | .eos =>
    if position.offset + framing.prefixSize = input.len then .ok none
    else .error (position.failure (.ipc .trailingBytes))
  | .metadata size =>
    if position.remaining = 0 then .error (position.failure (.ipc .batchLimit))
    else ((Stream.readRecord limits framing input field position.offset size).mapError position.failure).map some

inductive Cursor : Signature → Type where
  | at (input : KBytes) (field : LargeUtf8.Field) (position : Position) : Cursor (schema field)

def reader (limits : Limits) (framing : Framing) :
    Arrow.Events.BatchReader KBytes LargeUtf8.Field Cell Stream.Error Cursor where
  openInput input :=
    (admit limits framing input).map fun (field, offset) =>
      ⟨schema field, .at input field ⟨limits.batches, 0, offset⟩⟩
  next
    | .at input field position =>
      (readNext limits framing input field position).map (Option.map fun record =>
        (ofBatch field record, .at input field (position.advance record)))
  close _ := .ok ()

/-- Use one extra pull to check EOS or the next indexed failure. The source
cursor holds the original immutable carrier. -/
def readAll (limits : Limits) (framing : Framing) (input : KBytes) : EventStream :=
  (reader limits framing).read (limits.batches + 1) input

inductive SinkError where
  | openError (cause : Stream.Error)
  | termination (actual : Arrow.Events.Termination Stream.Error)
  | fieldCount (actual : Nat)
  | writer (cause : StreamWriter.Error)
  deriving DecidableEq

/-- A complete one-field trace emits a modern stream. A failed or closed
trace is refused with its original termination. -/
def emit (limits : Limits) (events : EventStream) : Except SinkError KBytes :=
  match events with
  | .error cause => .error (.openError cause)
  | .ok ⟨signature, trace⟩ =>
    match trace.termination with
    | .eos =>
      if one : signature.width = 1 then
        let i : Fin signature.width := ⟨0, by rw [one]; decide⟩
        let field := (signature.kind i).1
        (StreamWriter.emit limits field (trace.batches.map fun batch => batch.values i)).mapError .writer
      else .error (.fieldCount signature.width)
    | termination => .error (.termination termination)

/-- Each successful source step retains the checked range and nullable strings
from the same original record. -/
inductive Prefix (limits : Limits) (framing : Framing) (input : KBytes) (field : LargeUtf8.Field) :
    Position → List Stream.Batch → Position → Prop where
  | stop (position) : Prefix limits framing input field position [] position
  | more {position record rest final size} :
      readNext limits framing input field position = .ok (some record) →
      framing.readEnvelope limits input position.offset = .ok (.metadata size) →
      Stream.RecordWire limits framing input field position.offset size record →
      Prefix limits framing input field (position.advance record) rest final →
      Prefix limits framing input field position (record :: rest) final

def SourceWire (limits : Limits) (framing : Framing) (input : KBytes) (field : LargeUtf8.Field)
    (offset : Nat) (trace : Trace field) : Prop :=
  match Stream.read limits framing input with
  | .ok native =>
    native.field = field ∧ Stream.StreamWire limits framing input native ∧
      trace = ⟨native.batches.map (ofBatch field), .eos⟩
  | .error error =>
    ∃ records final cause,
      Prefix limits framing input field ⟨limits.batches, 0, offset⟩ records final ∧
      readNext limits framing input field final = .error (final.failure cause) ∧
      error = final.failure cause ∧
      trace = ⟨records.map (ofBatch field), .readError error⟩

/-- A complete native read fixes the exact descriptor and the input record
windows before the sink emits a modern stream. -/
def TranscodeWire (readLimits writeLimits : Limits) (framing : Framing)
    (input output : KBytes) : Prop :=
  ∃ source target,
    Stream.read readLimits framing input = .ok source ∧
    Stream.StreamWire readLimits framing input source ∧
    Stream.read writeLimits .modern output = .ok target ∧
    Stream.StreamWire writeLimits .modern output target ∧
    StreamWriter.Agrees source.field (source.batches.map Stream.Batch.values) target

end Silmaril.Formats.Arrow.LargeUtf8.Stream.Events
