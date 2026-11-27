module

public import Silmaril.Formats.Arrow.Binary.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.Binary.Stream.Correctness

public section

namespace Silmaril.Formats.Arrow.Binary.Stream

theorem openInput_sound {limits : Limits} {framing : Framing} {input : KBytes} {cursor : Cursor}
    (opened : openInput limits framing input = .ok cursor) :
    SchemaWire limits framing input cursor :=
  Proofs.Formats.Arrow.Binary.Stream.openInput_sound opened

theorem readRecord_sound {cursor : Cursor} {size : Nat} {batch : Batch}
    (read : cursor.readRecord size = .ok batch) : RecordWire cursor size batch :=
  Proofs.Formats.Arrow.Binary.Stream.readRecord_sound read

theorem next_batch {cursor after : Cursor} {batch : Batch}
    (next : cursor.next = .ok (some (batch, after))) :
    after = cursor.advance batch ∧ 0 < cursor.remaining ∧
      ∃ size, cursor.framing.readEnvelope cursor.limits cursor.input cursor.offset =
        .ok (.metadata size) ∧ RecordWire cursor size batch :=
  Proofs.Formats.Arrow.Binary.Stream.next_batch next

theorem next_failure {cursor : Cursor} {failure : Failure}
    (next : cursor.next = .error failure) :
    failure.ordinal = cursor.ordinal ∧ failure.offset = cursor.offset ∧
      cursor.readNext = .error failure.cause :=
  Proofs.Formats.Arrow.Binary.Stream.next_failure next

theorem next_suffix_error {cursor : Cursor}
    (marker : cursor.framing.readEnvelope cursor.limits cursor.input cursor.offset = .ok .eos)
    (tail : cursor.offset + cursor.framing.prefixSize ≠ cursor.input.len) :
    cursor.next = .error ⟨cursor.ordinal, cursor.offset, .trailingBytes⟩ :=
  Proofs.Formats.Arrow.Binary.Stream.next_suffix_error marker tail

theorem Prefix.ordinal {start final : Cursor} {batches : List Batch}
    (preceding : Prefix start batches final) : final.ordinal = start.ordinal + batches.length :=
  Proofs.Formats.Arrow.Binary.Stream.prefix_ordinal preceding

theorem drain_sound (cursor : Cursor) : TraceWire cursor cursor.drain :=
  Proofs.Formats.Arrow.Binary.Stream.drain_sound cursor

theorem readAll_sound {limits : Limits} {framing : Framing} {input : KBytes}
    {field : Binary.Field} {trace : Trace} (read : readAll limits framing input = .ok (field, trace)) :
    ∃ cursor, SchemaWire limits framing input cursor ∧ cursor.field = field ∧ TraceWire cursor trace :=
  Proofs.Formats.Arrow.Binary.Stream.readAll_sound read

/-- A failed drain retains precisely the ordered successful prefix. The
terminal ordinal counts records, including empty ones. -/
theorem readAll_failed_prefix {limits : Limits} {framing : Framing} {input : KBytes}
    {field : Binary.Field} {trace : Trace} {failure : Failure}
    (drained : readAll limits framing input = .ok (field, trace))
    (failed : trace.terminal = .failed failure) :
    ∃ start final, SchemaWire limits framing input start ∧ start.field = field ∧
      Prefix start trace.batches final ∧ failure.ordinal = trace.batches.length ∧
      failure.offset = final.offset ∧ final.readNext = .error failure.cause :=
  Proofs.Formats.Arrow.Binary.Stream.readAll_failed_prefix drained failed

theorem read_sound {limits : Limits} {framing : Framing} {input : KBytes} {observed : Observed}
    (read : read limits framing input = .ok observed) : StreamWire limits framing input observed :=
  Proofs.Formats.Arrow.Binary.Stream.read_sound read

theorem read_failed {limits : Limits} {framing : Framing} {input : KBytes} {field : Binary.Field}
    {trace : Trace} {failure : Failure} (drained : readAll limits framing input = .ok (field, trace))
    (failed : trace.terminal = .failed failure) :
    read limits framing input = .error (.record failure) :=
  Proofs.Formats.Arrow.Binary.Stream.read_failed drained failed

end Silmaril.Formats.Arrow.Binary.Stream
