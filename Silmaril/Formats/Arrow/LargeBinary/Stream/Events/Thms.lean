module

public import Silmaril.Formats.Arrow.LargeBinary.Stream.Events.Defs
public import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream.Events.Source
import Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream.Events.Sink

public section

namespace Silmaril.Formats.Arrow.LargeBinary.Stream.Events

theorem Prefix.ordinal {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeBinary.Field} {start final : Position} {records : List Stream.Batch}
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
  Proofs.Formats.Arrow.LargeBinary.Stream.Events.readAll_exact limits framing input

/-- Successful modern emission preserves the complete event observation,
including batch boundaries, after observing opaque cells as octets. -/
theorem emit_readback {limits : Limits} {field : LargeBinary.Field} {trace : Trace field} {wire : KBytes}
    (done : trace.termination = .eos) (written : emit limits (.ok ⟨schema field, trace⟩) = .ok wire) :
    ∃ native, Stream.read limits .modern wire = .ok native ∧
      Stream.StreamWire limits .modern wire native ∧
      StreamWriter.Agrees field (trace.batches.map slots) native ∧
      observe (readAll limits .modern wire) = observe (.ok ⟨schema field, trace⟩) :=
  Proofs.Formats.Arrow.LargeBinary.Stream.Events.emit_readback done written

theorem emit_observed {limits : Limits} {source : EventStream} {wire : KBytes}
    (written : emit limits source = .ok wire) :
    observe (readAll limits .modern wire) = observe source :=
  Proofs.Formats.Arrow.LargeBinary.Stream.Events.emit_observed written

/-- Either source framing can feed the modern sink. The source and target
certificates bind their own original byte windows and exact EOS. -/
theorem transcode_exact {readLimits writeLimits : Limits} {framing : Framing}
    {input output : KBytes} (written : emit writeLimits (readAll readLimits framing input) = .ok output) :
    TranscodeWire readLimits writeLimits framing input output ∧
      observe (readAll writeLimits .modern output) = observe (readAll readLimits framing input) :=
  Proofs.Formats.Arrow.LargeBinary.Stream.Events.transcode_exact written

theorem transcode_rows {readLimits writeLimits : Limits} {framing : Framing}
    {input output : KBytes} (written : emit writeLimits (readAll readLimits framing input) = .ok output) :
    Arrow.Events.EventStream.Equivalent
      (observe (readAll writeLimits .modern output)) (observe (readAll readLimits framing input)) := by
  unfold Arrow.Events.EventStream.Equivalent
  rw [(transcode_exact written).2]

/-- A late source failure retains the completed events and cannot produce a
successful sink EOS. The sink reports the original terminal error. -/
theorem transcode_late_error {readLimits writeLimits : Limits} {framing : Framing}
    {input : KBytes} {field : LargeBinary.Field} {offset : Nat} {error : Stream.Error}
    (opened : admit readLimits framing input = .ok (field, offset))
    (failed : Stream.read readLimits framing input = .error error) :
    ∃ records final cause,
      Prefix readLimits framing input field ⟨readLimits.batches, 0, offset⟩ records final ∧
      readNext readLimits framing input field final = .error error ∧ error = final.failure cause ∧
      readAll readLimits framing input = .ok ⟨schema field, ⟨records.map (ofBatch field), .readError error⟩⟩ ∧
      emit writeLimits (readAll readLimits framing input) = .error (.termination (.readError error)) :=
  Proofs.Formats.Arrow.LargeBinary.Stream.Events.transcode_late_error opened failed

end Silmaril.Formats.Arrow.LargeBinary.Stream.Events
