module

public import Silmaril.Formats.Arrow.Binary.Stream.Defs
public import Silmaril.Formats.Arrow.Binary.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.Binary.Stream

open Silmaril Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Binary.Stream

theorem openInput_sound {limits : Limits} {framing : Framing} {input : KBytes} {cursor : Cursor}
    (opened : openInput limits framing input = .ok cursor) :
    SchemaWire limits framing input cursor := by
  unfold openInput at opened
  cases wf : input.wf
  · simp [wf] at opened
  · simp only [wf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at opened
    cases envelopeEq : framing.readEnvelope limits input 0 with
    | error cause => simp [envelopeEq, Except.mapError, Bind.bind, Except.bind] at opened
    | ok envelope =>
      cases envelope with
      | eos => simp [envelopeEq, Except.mapError, Bind.bind, Except.bind] at opened
      | metadata size =>
        cases schemaEq : Binary.readSchema limits (input.slice framing.prefixSize size) with
        | error cause =>
          simp [envelopeEq, schemaEq, Except.mapError, Bind.bind, Except.bind] at opened
        | ok field =>
          simp only [envelopeEq, schemaEq, Except.mapError, Bind.bind, Except.bind] at opened
          cases opened
          exact ⟨wf, size, field, envelopeEq, schemaEq, rfl⟩

theorem readRecord_sound {cursor : Cursor} {size : Nat} {batch : Batch}
    (read : cursor.readRecord size = .ok batch) : RecordWire cursor size batch := by
  unfold Cursor.readRecord at read
  cases parsed : Silmaril.Formats.Arrow.readMessage cursor.limits
      (cursor.input.slice (cursor.offset + cursor.framing.prefixSize) size) with
  | error cause => simp [parsed, Except.mapError, Bind.bind, Except.bind] at read
  | ok message =>
    obtain ⟨header, bodyLength⟩ := message
    cases header with
    | schema fields => simp [parsed, Except.mapError, Bind.bind, Except.bind] at read
    | recordBatch metadata =>
      let range : Range := ⟨cursor.offset, cursor.framing.prefixSize, size, bodyLength⟩
      cases bodyEq : Silmaril.Formats.Arrow.readBody cursor.limits cursor.input
          range.bodyStart bodyLength with
      | error cause =>
        simp [parsed, bodyEq, range, Except.mapError, Bind.bind, Except.bind] at read
      | ok body =>
        cases bound : Binary.bindBody cursor.limits metadata body with
        | error cause =>
          simp [parsed, bodyEq, range, bound, Except.mapError, Bind.bind, Except.bind] at read
        | ok physical =>
          obtain ⟨node, buffers⟩ := physical
          cases column : Binary.readColumn cursor.limits cursor.field.nullable node buffers with
          | error cause =>
            simp [parsed, bodyEq, range, bound, column, Except.mapError, Bind.bind, Except.bind] at read
          | ok values =>
            simp only [parsed, bodyEq, range, bound, column, Except.mapError, Bind.bind,
              Except.bind] at read
            cases read
            exact ⟨metadata, node, buffers, body, parsed, rfl, bodyEq,
              Binary.bindBody_sound bound, Binary.readColumn_sound column⟩

private theorem readNext_batch {cursor : Cursor} {batch : { _batch : Batch // 0 < cursor.remaining }}
    (reply : cursor.readNext = .ok (some batch)) :
    ∃ size, cursor.framing.readEnvelope cursor.limits cursor.input cursor.offset =
      .ok (.metadata size) ∧ RecordWire cursor size batch.val := by
  unfold Cursor.readNext at reply
  cases framed : cursor.framing.readEnvelope cursor.limits cursor.input cursor.offset with
  | error cause => simp [framed, Except.mapError, Bind.bind, Except.bind] at reply
  | ok envelope =>
    cases envelope with
    | eos =>
      by_cases full : cursor.offset + cursor.framing.prefixSize = cursor.input.len <;>
        simp [framed, full, Except.mapError, Bind.bind, Except.bind] at reply
    | metadata size =>
      by_cases budget : 0 < cursor.remaining
      · cases record : cursor.readRecord size with
        | error cause => simp [framed, budget, record, Except.mapError, Bind.bind, Except.bind] at reply
        | ok result =>
          simp only [framed, budget, record, Except.mapError, Bind.bind, Except.bind, ↓reduceDIte] at reply
          cases reply
          exact ⟨size, rfl, readRecord_sound record⟩
      · simp [framed, budget, Except.mapError, Bind.bind, Except.bind] at reply

private theorem readNext_eos {cursor : Cursor} (reply : cursor.readNext = .ok none) :
    EndWire cursor (.eos cursor.offset) := by
  have next : cursor.next = .ok none := by simp [Cursor.next, reply, Except.map, Except.mapError]
  unfold Cursor.readNext at reply
  cases framed : cursor.framing.readEnvelope cursor.limits cursor.input cursor.offset with
  | error cause => simp [framed, Except.mapError, Bind.bind, Except.bind] at reply
  | ok envelope =>
    cases envelope with
    | eos =>
      by_cases full : cursor.offset + cursor.framing.prefixSize = cursor.input.len
      · exact ⟨rfl, framed, full, next⟩
      · simp [framed, full, Except.mapError, Bind.bind, Except.bind] at reply
    | metadata size =>
      by_cases budget : 0 < cursor.remaining
      · cases record : cursor.readRecord size <;>
          simp [framed, budget, record, Except.mapError, Bind.bind, Except.bind, pure, Except.pure] at reply
      · simp [framed, budget, Except.mapError, Bind.bind, Except.bind] at reply

theorem next_batch {cursor after : Cursor} {batch : Batch}
    (next : cursor.next = .ok (some (batch, after))) :
    after = cursor.advance batch ∧ 0 < cursor.remaining ∧
      ∃ size, cursor.framing.readEnvelope cursor.limits cursor.input cursor.offset =
        .ok (.metadata size) ∧ RecordWire cursor size batch := by
  unfold Cursor.next at next
  cases reply : cursor.readNext with
  | error cause => simp [reply, Except.mapError, Except.map] at next
  | ok result =>
    cases result with
    | none => simp [reply, Except.mapError, Except.map] at next
    | some hit =>
      simp only [reply, Except.mapError, Except.map, Option.map] at next
      cases next
      exact ⟨rfl, hit.property, readNext_batch reply⟩

theorem next_failure {cursor : Cursor} {failure : Failure}
    (next : cursor.next = .error failure) :
    failure.ordinal = cursor.ordinal ∧ failure.offset = cursor.offset ∧
      cursor.readNext = .error failure.cause := by
  unfold Cursor.next at next
  cases step : cursor.readNext with
  | error cause =>
    simp only [step, Except.mapError, Except.map] at next
    cases next
    exact ⟨rfl, rfl, rfl⟩
  | ok value => simp [step, Except.mapError, Except.map] at next

theorem drain_sound (cursor : Cursor) : TraceWire cursor cursor.drain := by
  induction count : cursor.remaining using Nat.strongRecOn generalizing cursor with
  | ind n ih =>
    rw [Cursor.drain]
    split
    · rename_i cause returned
      exact ⟨cursor, .stop cursor, rfl, rfl, by
        simp [Cursor.next, returned, Except.mapError, Except.map]⟩
    · rename_i returned
      exact ⟨cursor, .stop cursor, readNext_eos returned⟩
    · rename_i batch returned
      have smaller : (cursor.advance batch.val).remaining < n := by
        rw [← count]
        exact Nat.pred_lt (Nat.ne_of_gt batch.property)
      obtain ⟨final, preceding, terminal⟩ := ih _ smaller (cursor.advance batch.val) rfl
      have next : cursor.next = .ok (some (batch.val, cursor.advance batch.val)) := by
        simp [Cursor.next, returned, Except.mapError, Except.map]
      obtain ⟨_, budget, _, envelope, record⟩ := next_batch next
      exact ⟨final, .more envelope budget record next preceding, terminal⟩

theorem readAll_sound {limits : Limits} {framing : Framing} {input : KBytes}
    {field : Binary.Field} {trace : Trace} (read : readAll limits framing input = .ok (field, trace)) :
    ∃ cursor, SchemaWire limits framing input cursor ∧ cursor.field = field ∧ TraceWire cursor trace := by
  unfold readAll at read
  cases opened : openInput limits framing input with
  | error cause => simp [opened, Except.map] at read
  | ok cursor =>
    simp only [opened, Except.map] at read
    cases read
    exact ⟨cursor, openInput_sound opened, rfl, drain_sound cursor⟩

theorem read_sound {limits : Limits} {framing : Framing} {input : KBytes} {observed : Observed}
    (read : read limits framing input = .ok observed) : StreamWire limits framing input observed := by
  unfold Silmaril.Formats.Arrow.Binary.Stream.read at read
  cases drained : readAll limits framing input with
  | error cause => simp [drained, Except.mapError, Bind.bind, Except.bind] at read
  | ok result =>
    obtain ⟨field, trace⟩ := result
    obtain ⟨cursor, schema, declares, final, preceding, terminal⟩ := readAll_sound drained
    cases endEq : trace.terminal with
    | failed failure => simp [drained, endEq, Except.mapError, Bind.bind, Except.bind] at read
    | eos offset =>
      simp only [drained, endEq, Except.mapError, Bind.bind, Except.bind] at read
      cases read
      exact ⟨cursor, final, schema, declares, preceding, endEq ▸ terminal⟩

theorem read_failed {limits : Limits} {framing : Framing} {input : KBytes} {field : Binary.Field}
    {trace : Trace} {failure : Failure} (drained : readAll limits framing input = .ok (field, trace))
    (failed : trace.terminal = .failed failure) :
    read limits framing input = .error (.record failure) := by
  simp [Silmaril.Formats.Arrow.Binary.Stream.read, drained, failed, Except.mapError, Bind.bind, Except.bind]

theorem next_suffix_error {cursor : Cursor}
    (marker : cursor.framing.readEnvelope cursor.limits cursor.input cursor.offset = .ok .eos)
    (tail : cursor.offset + cursor.framing.prefixSize ≠ cursor.input.len) :
    cursor.next = .error ⟨cursor.ordinal, cursor.offset, .trailingBytes⟩ := by
  simp [Cursor.next, Cursor.readNext, marker, tail, Cursor.failure, Except.mapError,
    Except.map, Bind.bind, Except.bind]

theorem prefix_ordinal {start final : Cursor} {batches : List Batch}
    (preceding : Prefix start batches final) : final.ordinal = start.ordinal + batches.length := by
  induction preceding with
  | stop => simp
  | more _ _ _ _ _ ih =>
    simpa [Cursor.advance, Nat.add_assoc, Nat.add_comm 1] using ih

theorem readAll_failed_prefix {limits : Limits} {framing : Framing} {input : KBytes}
    {field : Binary.Field} {trace : Trace} {failure : Failure}
    (drained : readAll limits framing input = .ok (field, trace))
    (failed : trace.terminal = .failed failure) :
    ∃ start final, SchemaWire limits framing input start ∧ start.field = field ∧
      Prefix start trace.batches final ∧ failure.ordinal = trace.batches.length ∧
      failure.offset = final.offset ∧ final.readNext = .error failure.cause := by
  obtain ⟨start, schema, declares, final, preceding, terminal⟩ := readAll_sound drained
  obtain ⟨ordinal, offset, pull⟩ := failed ▸ terminal
  have first : start.ordinal = 0 := by
    obtain ⟨_, _, _, _, _, rfl⟩ := schema
    rfl
  refine ⟨start, final, schema, declares, preceding, ?_, offset, (next_failure pull).2.2⟩
  rw [ordinal, prefix_ordinal preceding, first, Nat.zero_add]

end Silmaril.Proofs.Formats.Arrow.Binary.Stream
