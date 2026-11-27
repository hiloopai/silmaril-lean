module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Defs

/-! Observable terminal failures over admitted ordered fragments. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

open MixedFlat.Events

abbrev Published (fields : List MixedFlat.Field) :=
  Stream.Batch × MixedFlat.Events.Batch (schema fields)

def Delivered.published {fields : List MixedFlat.Field} (batch : Delivered fields) :
    Published fields :=
  (batch.record, batch.event)

structure Position where
  remaining : Nat
  ordinal : Nat
  rows : Nat
  offset : Nat

def Position.readNext (position : Position) (limits : MixedFlat.Limits) (input : KBytes)
    (fields : List MixedFlat.Field) :
    Except Stream.Events.Error (Option (Stream.Events.Decoded fields)) :=
  Stream.Events.readNext limits input fields position.remaining position.ordinal position.rows position.offset

def Position.after (position : Position) (record : Stream.Batch) : Position :=
  ⟨position.remaining - 1, position.ordinal + 1,
    position.rows + record.observed.rowCount, record.range.next⟩

def Position.ofRunning (limits : MixedFlat.Limits) (running : Running) (offset : Nat) : Position :=
  ⟨limits.observation.ipc.batches - running.ordinal, running.ordinal, running.rows, offset⟩

/-- Each published record and event are taken from the same immutable pull
step. Its absolute range remains observable even when the suffix fails. -/
inductive Replay (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field) :
    Position → List (Published fields) → Position → Prop where
  | stop (atByte : Position) : Replay limits input fields atByte [] atByte
  | next {before final decoded following} :
      before.readNext limits input fields = .ok (some decoded) →
      Replay limits input fields (before.after decoded.record) following final →
      Replay limits input fields before ((decoded.record, decoded.event) :: following) final

/-- The exact feed error for the first byte following modern EOS. -/
def tailError (ordinal firstTail : Nat) : Incremental.Error :=
  .framing (some ordinal) ⟨.tail, firstTail, .malformed .trailingBytes⟩

/-- A checked Schema, a finite successful prefix and one terminal feed call.
Every supplied chunk refers to the complete original carrier, including the
offending tail byte. The last reply has no successor cursor. -/
structure TailFailure (limits : Incremental.Limits) (wire : KBytes) where
  fields : List MixedFlat.Field
  batches : List (Delivered fields)
  ordinal : Nat
  firstTail : Nat
  ran : ∃ opened final chunk,
    SchemaSteps wire.len (wire.read 0 wire.len) fields (start limits) opened ∧
    RecordSteps wire.len (wire.read 0 wire.len) fields opened batches final ∧
    Arrow.Framing.Incremental.Window (Portable.reference wire) final.position chunk ∧
    feed final chunk = .error (tailError ordinal firstTail)

def TailFailure.ranges {limits : Incremental.Limits} {wire : KBytes} (result : TailFailure limits wire) :
    List Stream.BatchRange :=
  result.batches.map (·.record.range)

def TailFailure.cause {limits : Incremental.Limits} {wire : KBytes} (result : TailFailure limits wire) :
    Incremental.Error :=
  tailError result.ordinal result.firstTail

def TailFailure.trace {limits : Incremental.Limits} {wire : KBytes} (result : TailFailure limits wire) :
    Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Incremental.Error :=
  .ok ⟨schema result.fields, ⟨result.batches.map Delivered.event, .readError result.cause⟩⟩

/-- The immutable comparison uses its own error reporting convention.
Its ordinal is the next record ordinal and its offset is the EOS marker. -/
def TailAgreement (limits : Incremental.Limits) (wire : KBytes) (result : TailFailure limits wire) : Prop :=
  let input := Portable.reference wire
  ∃ startOffset final,
    Stream.readSchemaFrame limits.mixed.observation.ipc input = .ok (result.fields, startOffset) ∧
    Replay limits.mixed input result.fields (.ofRunning limits.mixed {} startOffset)
      (result.batches.map Delivered.published) final ∧
    final.ordinal = result.ordinal ∧ final.offset + 8 = result.firstTail ∧ result.firstTail < wire.len ∧
    final.readNext limits.mixed input result.fields = .error (.message result.ordinal final.offset .trailingBytes) ∧
    Stream.read limits.mixed input = .error (.batch result.ordinal .trailingBytes)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure
