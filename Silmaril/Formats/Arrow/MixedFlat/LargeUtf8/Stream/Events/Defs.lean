module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Defs
public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Thms
import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events.Thms

/-! Pull events over the opt-in mixed-flat LargeUtf8 IPC profile. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events

open Silmaril.Relational
open MixedFlat.LargeUtf8.Events

inductive Error where
  | schema (cause : Stream.SchemaError)
  | record (ordinal offset : Nat) (cause : Stream.Cause)
  deriving DecidableEq, Repr

def observeTermination : Stream.Termination → Arrow.Events.Termination Error
  | .eos _ => .eos
  | .error ordinal offset cause => .readError (.record ordinal offset cause)

abbrev Trace (signature : Signature) := Arrow.Events.Trace signature Cell Error
abbrev EventStream := Arrow.Events.EventStream Field Cell Error

structure Decoded (fields : List Field) where
  record : Stream.Batch
  event : MixedFlat.LargeUtf8.Events.Batch (schema fields)
  aligned : Agrees (schema fields) record.observed event

/-- Select the next original frame and delegate record checks and decoding
to the same decoder used by the direct reader. -/
def readNext (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes) (fields : List Field)
    (remaining ordinal rows offset : Nat) : Except Error (Option (Decoded fields)) :=
  match framing.readEnvelope limits.observation.ipc input offset with
  | .error cause => .error (.record ordinal offset (.envelope cause))
  | .ok .eos =>
    if offset + framing.prefixSize = input.len then .ok none
    else .error (.record ordinal offset .trailingBytes)
  | .ok (.metadata size) =>
    if remaining = 0 then .error (.record ordinal offset .batchLimit)
    else match decoded : Stream.readRecord limits framing input fields rows offset size with
    | .error cause => .error (.record ordinal offset cause)
    | .ok record =>
      have shape : record.observed.columns.map Prod.fst = fields ∧
          ∀ pair ∈ record.observed.columns, (cells pair.1.kind pair.2).length = record.observed.rowCount := by
        obtain ⟨_, _, _, _, _, _, wire⟩ := Stream.readRecord_sound decoded
        exact batch_shape wire
      .ok (some ⟨record, ofObserved fields record.observed shape.1 shape.2,
        by exact ofObserved_agrees fields record.observed shape.1 shape.2⟩)

/-- A live cursor retains the full immutable input and the next original
frame position. It decodes one record per successful pull. -/
inductive Cursor : Signature → Type where
  | at (input : KBytes) (fields : List Field) (remaining ordinal rows offset : Nat) :
      Cursor (schema fields)

def admit (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes) :
    Except Stream.SchemaError (List Field × Nat) :=
  if !input.wf then .error .source
  else Stream.readSchemaFrame limits.observation.ipc framing input

def reader (limits : MixedFlat.Limits) (framing : Framing) :
    Arrow.Events.BatchReader KBytes Field Cell Error Cursor where
  openInput input :=
    ((admit limits framing input).mapError .schema).map fun (fields, offset) =>
      ⟨schema fields, .at input fields limits.observation.ipc.batches 0 0 offset⟩
  next
    | .at input fields remaining ordinal rows offset =>
      (readNext limits framing input fields remaining ordinal rows offset).map (Option.map fun decoded =>
        (decoded.event, .at input fields (remaining - 1) (ordinal + 1)
          (rows + decoded.record.observed.rowCount) decoded.record.range.next))
  close _ := .ok ()

/-- Drain through the first failure or exact EOS, including a terminal check
after consuming the maximum allowed number of records. -/
def readAll (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes) : EventStream :=
  (reader limits framing).read (limits.observation.ipc.batches + 1) input

def projectTrace {source : Signature} (projection : Scan.Projection source) (trace : Trace source) :
    Trace projection.schema :=
  ⟨trace.batches.map projection.projectColumns, trace.termination⟩

/-- Project decoded columns by their checked positions while preserving the
explicit row count of every batch and the original terminal outcome. -/
def readProjected (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes)
    (projection : (source : Signature) → Scan.Projection source) : EventStream :=
  (readAll limits framing input).map fun ⟨source, trace⟩ =>
    ⟨(projection source).schema, projectTrace (projection source) trace⟩

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events
