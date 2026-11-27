module

public import Silmaril.Formats.Arrow.LargeBinary.Stream.Events.Defs
import Silmaril.Formats.Arrow.LargeBinary.Stream.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream.Events

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open LargeBinary.Stream.Events

private def Suffix (limits : Limits) (framing : LargeBinary.Stream.Framing) (input : KBytes)
    (field : LargeBinary.Field) (position : Position) :=
  LargeBinary.Stream.readBatches limits framing input field
    position.remaining position.ordinal position.offset

private def StepWire (limits : Limits) (framing : LargeBinary.Stream.Framing) (input : KBytes)
    (field : LargeBinary.Field) (position : Position) :
    Except LargeBinary.Stream.Error (Option LargeBinary.Stream.Batch) → Prop
  | .error error =>
    (∃ cause, error = position.failure cause) ∧ Suffix limits framing input field position = .error error
  | .ok none => Suffix limits framing input field position = .ok ([], position.offset)
  | .ok (some record) =>
    0 < position.remaining ∧ ∃ size,
      framing.readEnvelope limits input position.offset = .ok (.metadata size) ∧
      LargeBinary.Stream.RecordWire limits framing input field position.offset size record ∧
      Suffix limits framing input field position =
        (Suffix limits framing input field (position.advance record)).map
          (fun (rest, eos) => (record :: rest, eos))

private theorem step_exact {limits : Limits} {framing : LargeBinary.Stream.Framing} {input : KBytes}
    {field : LargeBinary.Field} {position : Position} {reply : Except LargeBinary.Stream.Error
      (Option LargeBinary.Stream.Batch)}
    (step : readNext limits framing input field position = reply) :
    StepWire limits framing input field position reply := by
  obtain ⟨remaining, ordinal, offset⟩ := position
  cases envelope : framing.readEnvelope limits input offset with
  | error cause =>
    simp [readNext, envelope, Except.mapError, Bind.bind, Except.bind] at step
    subst reply
    exact ⟨⟨.envelope cause, rfl⟩, by
      simp [Suffix, LargeBinary.Stream.readBatches, envelope, Except.mapError, Bind.bind,
        Except.bind, Position.failure]⟩
  | ok framed =>
    cases framed with
    | eos =>
      by_cases full : offset + framing.prefixSize = input.len
      · simp [readNext, envelope, full, Except.mapError, Bind.bind, Except.bind] at step
        subst reply
        simp [StepWire, Suffix, LargeBinary.Stream.readBatches, envelope, full, Except.mapError,
          Bind.bind, Except.bind]
      · simp [readNext, envelope, full, Except.mapError, Bind.bind, Except.bind] at step
        subst reply
        exact ⟨⟨.trailingBytes, rfl⟩, by
          simp [Suffix, LargeBinary.Stream.readBatches, envelope, full, Except.mapError, Bind.bind,
            Except.bind, Position.failure]⟩
    | metadata size =>
      cases remaining with
      | zero =>
        simp [readNext, envelope, Except.mapError, Bind.bind, Except.bind] at step
        subst reply
        exact ⟨⟨.batchLimit, rfl⟩, by
          simp [Suffix, LargeBinary.Stream.readBatches, envelope, Except.mapError, Bind.bind,
            Except.bind, Position.failure]⟩
      | succ fuel =>
        cases batchEq : LargeBinary.Stream.readRecord limits framing input field offset size with
        | error cause =>
          simp [readNext, envelope, batchEq, Except.mapError, Bind.bind, Except.bind, Except.map] at step
          subst reply
          exact ⟨⟨cause, rfl⟩, by
            simp [Suffix, LargeBinary.Stream.readBatches, envelope, batchEq, Except.mapError,
              Bind.bind, Except.bind, Position.failure]⟩
        | ok record =>
          simp [readNext, envelope, batchEq, Except.mapError, Bind.bind, Except.bind, Except.map] at step
          subst reply
          refine ⟨Nat.zero_lt_succ _, size, envelope, LargeBinary.Stream.readRecord_sound batchEq, ?_⟩
          simp only [Suffix, Position.advance, Nat.succ_sub_one]
          rw [LargeBinary.Stream.readBatches]
          simp [envelope, batchEq, Except.mapError, Bind.bind, Except.bind, Except.map]
          cases LargeBinary.Stream.readBatches limits framing input field fuel (ordinal + 1)
            record.range.next <;> rfl

private theorem pull_exact (limits : Limits) (framing : LargeBinary.Stream.Framing) (input : KBytes)
    (field : LargeBinary.Field) (position : Position) (reversed : List (Batch field)) :
    let trace := Arrow.Events.BatchReader.read.pull (reader limits framing) (schema field)
      (position.remaining + 1) (.at input field position) reversed
    match Suffix limits framing input field position with
    | .ok (records, _) => trace = ⟨reversed.reverse ++ records.map (ofBatch field), .eos⟩
    | .error error =>
      ∃ records final cause,
        Prefix limits framing input field position records final ∧
        readNext limits framing input field final = .error (final.failure cause) ∧
        error = final.failure cause ∧
        trace = ⟨reversed.reverse ++ records.map (ofBatch field), .readError error⟩ := by
  induction count : position.remaining using Nat.strongRecOn generalizing position reversed with
  | ind available ih =>
    cases next : readNext limits framing input field position with
    | error error =>
      obtain ⟨⟨cause, rfl⟩, native⟩ := step_exact next
      simp only [native]
      exact ⟨[], position, cause, .stop position, next, rfl, by
        simp [Arrow.Events.BatchReader.read.pull, reader, next, Except.map]⟩
    | ok reply =>
      cases reply with
      | none =>
        have native := step_exact next
        change Suffix limits framing input field position = .ok ([], position.offset) at native
        simp [native, Arrow.Events.BatchReader.read.pull, reader, next, Except.map]
      | some record =>
        obtain ⟨budget, size, envelope, layout, native⟩ := step_exact next
        let after := position.advance record
        have smaller : after.remaining < available := by
          show position.remaining - 1 < available
          omega
        have calls : after.remaining + 1 = available := by
          show position.remaining - 1 + 1 = available
          omega
        have adapted : (reader limits framing).next (.at input field position) =
            .ok (some (ofBatch field record, .at input field after)) := by
          simp [reader, next, Except.map, after]
        have tail := ih _ smaller after (ofBatch field record :: reversed) rfl
        rw [Arrow.Events.BatchReader.read.pull, adapted, ← calls]
        rw [native]
        cases rest : Suffix limits framing input field after with
        | error error =>
          rw [rest] at tail
          obtain ⟨records, final, cause, done, failed, same, observed⟩ := tail
          exact ⟨record :: records, final, cause, .more next envelope layout done, failed, same, by
            simpa [List.reverse_cons, List.append_assoc] using observed⟩
        | ok result =>
          obtain ⟨records, eos⟩ := result
          rw [rest] at tail
          simp only [Except.map]
          simpa [List.reverse_cons, List.append_assoc] using tail

private theorem native_read (limits : Limits) (framing : LargeBinary.Stream.Framing) (input : KBytes) :
    LargeBinary.Stream.read limits framing input = (do
      let (field, offset) ← admit limits framing input
      let (records, eos) ← Suffix limits framing input field ⟨limits.batches, 0, offset⟩
      return ⟨field, records, eos⟩) := by
  cases wf : input.wf <;>
    simp [LargeBinary.Stream.read, admit, wf, Suffix, Except.mapError, Bind.bind, Except.bind]

theorem readAll_exact (limits : Limits) (framing : LargeBinary.Stream.Framing) (input : KBytes) :
    match admit limits framing input with
    | .error error =>
      readAll limits framing input = .error error ∧ LargeBinary.Stream.read limits framing input = .error error
    | .ok (field, offset) =>
      ∃ trace : Trace field,
        readAll limits framing input = .ok ⟨schema field, trace⟩ ∧
        SourceWire limits framing input field offset trace := by
  cases ready : admit limits framing input with
  | error cause =>
    simp [readAll, Arrow.Events.BatchReader.read, reader, native_read, ready,
      Except.map, Bind.bind, Except.bind]
  | ok checked =>
    obtain ⟨field, offset⟩ := checked
    let position : Position := ⟨limits.batches, 0, offset⟩
    let trace := Arrow.Events.BatchReader.read.pull (reader limits framing) (schema field)
      (position.remaining + 1) (.at input field position) []
    refine ⟨trace, ?_, ?_⟩
    · simp [readAll, Arrow.Events.BatchReader.read, reader, ready, Except.map, trace, position]
    · have agreed := pull_exact limits framing input field position []
      cases native : Suffix limits framing input field position with
      | error cause =>
        simp [SourceWire, native_read, ready, native, position, Bind.bind, Except.bind]
        rw [native] at agreed
        simpa [trace, position] using agreed
      | ok result =>
        obtain ⟨records, stop⟩ := result
        have decoded : LargeBinary.Stream.read limits framing input = .ok ⟨field, records, stop⟩ := by
          simp [native_read, ready, native, position, Bind.bind, Except.bind, Pure.pure, Except.pure]
        simp only [SourceWire, decoded]
        rw [native] at agreed
        exact ⟨by simp, LargeBinary.Stream.read_sound decoded, by simpa [trace] using agreed⟩

theorem read_success {limits : Limits} {framing : LargeBinary.Stream.Framing} {input : KBytes}
    {native : LargeBinary.Stream.Observed} (decoded : LargeBinary.Stream.read limits framing input = .ok native) :
    readAll limits framing input = .ok ⟨schema native.field,
      ⟨native.batches.map (ofBatch native.field), .eos⟩⟩ := by
  have agreed := readAll_exact limits framing input
  cases admitted : admit limits framing input with
  | error cause =>
    rw [admitted] at agreed
    rw [decoded] at agreed
    exact False.elim (by cases agreed.2)
  | ok result =>
    obtain ⟨field, offset⟩ := result
    rw [admitted] at agreed
    obtain ⟨trace, read, wire⟩ := agreed
    simp only [SourceWire, decoded] at wire
    obtain ⟨rfl, _, rfl⟩ := wire
    exact read

end Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream.Events
