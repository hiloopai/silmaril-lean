module

public import Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Defs
public import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Proofs.Formats.Arrow.LargeUtf8.Stream.Events.Source
import Silmaril.Proofs.Formats.Arrow.LargeUtf8.Stream.Events.Sink

public section

namespace Silmaril.Formats.Arrow.LargeUtf8.Stream.Events

open Silmaril.Relational

theorem Prefix.ordinal {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeUtf8.Field} {start final : Position} {records : List Stream.Batch}
    (delivered : Prefix limits framing input field start records final) :
    final.ordinal = start.ordinal + records.length := by
  induction delivered with
  | stop => simp
  | more _ _ _ _ ih => simpa [Position.advance, Nat.add_assoc, Nat.add_comm 1] using ih

/-- The standard reader follows the original record windows. Its first
failed pull retains the preceding batch events and original source error. -/
theorem readAll_exact (limits : Limits) (framing : Framing) (input : KBytes) :
    match admit limits framing input with
    | .error error =>
      readAll limits framing input = .error error ∧ Stream.read limits framing input = .error error
    | .ok (field, offset) =>
      ∃ trace : Trace field,
        readAll limits framing input = .ok ⟨schema field, trace⟩ ∧
        SourceWire limits framing input field offset trace :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.Events.readAll_exact limits framing input

/-- Successful modern emission preserves the exact event trace, including
nullable strings, batch boundaries and termination. -/
theorem emit_readback {limits : Limits} {field : LargeUtf8.Field} {trace : Trace field} {wire : KBytes}
    (done : trace.termination = .eos) (written : emit limits (.ok ⟨schema field, trace⟩) = .ok wire) :
    ∃ native, Stream.read limits .modern wire = .ok native ∧
      Stream.StreamWire limits .modern wire native ∧
      StreamWriter.Agrees field (trace.batches.map slots) native ∧
      readAll limits .modern wire = .ok ⟨schema field, trace⟩ :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.Events.emit_readback done written

theorem emit_events {limits : Limits} {source : EventStream} {wire : KBytes}
    (written : emit limits source = .ok wire) :
    readAll limits .modern wire = source :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.Events.emit_events written

/-- Either source framing can feed the modern sink. The source and target
certificates bind their own original byte windows and exact EOS. -/
theorem transcode_exact {readLimits writeLimits : Limits} {framing : Framing}
    {input output : KBytes} (written : emit writeLimits (readAll readLimits framing input) = .ok output) :
    TranscodeWire readLimits writeLimits framing input output ∧
      readAll writeLimits .modern output = readAll readLimits framing input :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.Events.transcode_exact written

/-- Two checked emissions of the same rows at one schema have the same
collected observation, even if the input batch partitions differ. -/
theorem emit_rechunk {limits : Limits} {field : LargeUtf8.Field} {left right : Trace field}
    {first second : KBytes} (firstWritten : emit limits (.ok ⟨schema field, left⟩) = .ok first)
    (secondWritten : emit limits (.ok ⟨schema field, right⟩) = .ok second) (rows : left.rows = right.rows) :
    Arrow.Events.EventStream.Equivalent (readAll limits .modern first) (readAll limits .modern second) :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.Events.emit_rechunk firstWritten secondWritten rows

/-- Logical scans of the two wire readbacks agree at the row level, including
the row positions retained by a projection to width zero. -/
theorem emit_scan_rechunk {limits : Limits} {field : LargeUtf8.Field} {left right : Trace field}
    {first second : KBytes} (firstWritten : emit limits (.ok ⟨schema field, left⟩) = .ok first)
    (secondWritten : emit limits (.ok ⟨schema field, right⟩) = .ok second) (rows : left.rows = right.rows)
    (projection : (signature : Signature) → Scan.Projection signature)
    (predicate : (signature : Signature) → Scan.Predicate signature Cell) :
    Arrow.Events.EventStream.Equivalent ((readAll limits .modern first).scan projection predicate)
      ((readAll limits .modern second).scan projection predicate) :=
  (emit_rechunk firstWritten secondWritten rows).scan projection predicate

/-- A late source failure retains the completed events and cannot produce a
successful sink EOS. The sink reports the original terminal error. -/
theorem transcode_late_error {readLimits writeLimits : Limits} {framing : Framing}
    {input : KBytes} {field : LargeUtf8.Field} {offset : Nat} {error : Stream.Error}
    (opened : admit readLimits framing input = .ok (field, offset))
    (failed : Stream.read readLimits framing input = .error error) :
    ∃ records final cause,
      Prefix readLimits framing input field ⟨readLimits.batches, 0, offset⟩ records final ∧
      readNext readLimits framing input field final = .error error ∧ error = final.failure cause ∧
      readAll readLimits framing input = .ok ⟨schema field, ⟨records.map (ofBatch field), .readError error⟩⟩ ∧
      emit writeLimits (readAll readLimits framing input) = .error (.termination (.readError error)) :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.Events.transcode_late_error opened failed

end Silmaril.Formats.Arrow.LargeUtf8.Stream.Events
