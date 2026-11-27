module

public import Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Defs
public import Silmaril.Formats.Arrow.Events.Defs

/-! A standard Arrow event reader and modern sink for one LargeBinary field. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeBinary.Stream.Events

open Silmaril.Relational

inductive Kind where
  | largeBinary
  deriving DecidableEq, Repr

abbrev Cell (_ : Kind) := KBytes
abbrev Octets (_ : Kind) := List UInt8
abbrev Signature := Scan.Schema LargeBinary.Field Kind

def schema (field : LargeBinary.Field) : Signature :=
  ⟨1, fun _ => (field, .largeBinary)⟩

abbrev Batch (field : LargeBinary.Field) := Arrow.Events.Batch (schema field) Cell
abbrev Trace (field : LargeBinary.Field) := Arrow.Events.Trace (schema field) Cell Stream.Error
abbrev EventStream := Arrow.Events.EventStream LargeBinary.Field Cell Stream.Error
abbrev ObservedEvents := Arrow.Events.EventStream LargeBinary.Field Octets Stream.Error

def ofValues {value : Type} (field : LargeBinary.Field) (values : List (Option value)) :
    Arrow.Events.Batch (schema field) (fun _ => value) :=
  ⟨values.length, fun _ => values, fun _ => rfl⟩

def ofBatch (field : LargeBinary.Field) (record : Stream.Batch) : Batch field :=
  ofValues field record.values

def slots {field : LargeBinary.Field} (batch : Batch field) : LargeBinary.Column :=
  batch.values ⟨0, Nat.zero_lt_one⟩

def observeBatch {signature : Signature} (batch : Arrow.Events.Batch signature Cell) :
    Arrow.Events.Batch signature Octets :=
  ⟨batch.rowCount, fun i => (batch.values i).map (Option.map KBytes.toList), by
    intro i
    exact (List.length_map _).trans (batch.length_eq i)⟩

/-- Observe cells as octets, preserving schema, batches and termination. -/
def observe (stream : EventStream) : ObservedEvents :=
  stream.map fun ⟨signature, trace⟩ =>
    ⟨signature, ⟨trace.batches.map observeBatch, trace.termination⟩⟩

structure Position where
  remaining : Nat
  ordinal : Nat
  offset : Nat

def Position.advance (position : Position) (record : Stream.Batch) : Position :=
  ⟨position.remaining - 1, position.ordinal + 1, record.range.next⟩

def Position.failure (position : Position) (cause : Binary.Stream.Cause) : Stream.Error :=
  .record ⟨position.ordinal, position.offset, cause⟩

def admit (limits : Limits) (framing : Framing) (input : KBytes) :
    Except Stream.Error (LargeBinary.Field × Nat) :=
  if !input.wf then .error (.schema .source)
  else (Stream.readSchemaFrame limits framing input).mapError .schema

/-- Read one original frame. The native decoder checks batch metadata, body
and column bounds. A complete terminal marker must exhaust the carrier. -/
def readNext (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeBinary.Field) (position : Position) : Except Stream.Error (Option Stream.Batch) := do
  let envelope ← (framing.readEnvelope limits input position.offset).mapError
    (position.failure ∘ Binary.Stream.Cause.envelope)
  match envelope with
  | .eos =>
    if position.offset + framing.prefixSize = input.len then .ok none
    else .error (position.failure .trailingBytes)
  | .metadata size =>
    if position.remaining = 0 then .error (position.failure .batchLimit)
    else ((Stream.readRecord limits framing input field position.offset size).mapError position.failure).map some

inductive Cursor : Signature → Type where
  | at (input : KBytes) (field : LargeBinary.Field) (position : Position) : Cursor (schema field)

def reader (limits : Limits) (framing : Framing) :
    Arrow.Events.BatchReader KBytes LargeBinary.Field Cell Stream.Error Cursor where
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

/-- Each successful source step retains the checked range and opaque slots
from the same original record. -/
inductive Prefix (limits : Limits) (framing : Framing) (input : KBytes) (field : LargeBinary.Field) :
    Position → List Stream.Batch → Position → Prop where
  | stop (position) : Prefix limits framing input field position [] position
  | more {position record rest final size} :
      readNext limits framing input field position = .ok (some record) →
      framing.readEnvelope limits input position.offset = .ok (.metadata size) →
      Stream.RecordWire limits framing input field position.offset size record →
      Prefix limits framing input field (position.advance record) rest final →
      Prefix limits framing input field position (record :: rest) final

def SourceWire (limits : Limits) (framing : Framing) (input : KBytes) (field : LargeBinary.Field)
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
    StreamWriter.Agrees source.field (source.batches.map Binary.Stream.Batch.values) target

end Silmaril.Formats.Arrow.LargeBinary.Stream.Events
