module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.Conversion

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc

open Arrow.RecursiveSchema hiding Limits Error
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)

public section

theorem convert_open_error {limits : Limits} {input : KBytes} {checksum : Bool}
    {cause : Arrow.RecursiveSchema.Error}
    (original : Arrow.RecursiveSchema.readFrame limits.ipc.schema input = .error cause) :
    convert limits input checksum = .error (.openError cause) := by
  simp [convert, Stream.readTrace_open_error original, Except.mapError, bind, Except.bind]

/-- The first original failure and complete prefix take precedence under
every Parquet budget. -/
theorem convert_terminal_error {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} {ordinal offset : Nat} {cause : Stream.Cause}
    (original : Stream.readTrace limits.ipc input = .ok source)
    (failed : source.terminal = .failed ordinal offset cause) :
    convert limits input checksum = .error (.terminal source) := by
  simp [convert, original, failed, Except.mapError, bind, Except.bind]

theorem convert_terminal_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (rejected : convert limits input checksum = .error (.terminal source)) :
    TerminalWire limits.ipc input source :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.convert_terminal_wire rejected

/-- Once the original stream is strict, the result is the original writer's
output or typed cause for the exact source observations. -/
theorem convert_of_strict {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (strict : Stream.read limits.ipc input = .ok source) :
    convert limits input checksum = (Writer.emit limits.parquet (writerInput source checksum)).mapError .writer := by
  obtain ⟨original, _, _, eos⟩ := Stream.read_iff.mp strict
  simp [convert, original, eos, Except.mapError, bind, Except.bind]

theorem convert_writer_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {cause : Writer.Error} (rejected : convert limits input checksum = .error (.writer cause)) :
    ∃ source, SourceWire limits.ipc input source ∧
      Writer.emit limits.parquet (writerInput source checksum) = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.convert_writer_wire rejected

theorem convert_readback {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} (accepted : convert limits input checksum = .ok output) :
    Readback limits input checksum output :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.convert_readback accepted

/-- Events of the two original carriers agree through EOS. -/
theorem agrees_events {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} {parquet : Σ sig : Signature, Reader.Events.Trace sig}
    {ipc : Σ sig : Signature, Stream.Events.Trace sig}
    (written : convert limits input checksum = .ok output)
    (direct : Reader.Events.read limits.parquet.schema.snapshot limits.parquet.chunk output.bytes = .ok parquet)
    (original : Stream.Events.read limits.ipc input = .ok ipc) :
    declarations parquet.1 = declarations ipc.1 ∧
    parquet.2.batches.map eraseBatch = ipc.2.batches.map eraseBatch ∧
    parquet.2.termination = .eos ∧ ipc.2.termination = .eos :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.agrees_events written direct original

/-- A successful full-field forward conversion preserves the exact source
declaration and ordered batch observations through its own strict EOS. -/
theorem round_trip {limits : Limits} {input returned : KBytes} {checksum : Bool}
    {output : Writer.Output} {reverse : Arrow.RecursiveSchema.Batch.Limits}
    (written : convert limits input checksum = .ok output)
    (forward : Reader.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.chunk reverse
      output.bytes .field = .ok returned) :
    ∃ source, SourceWire limits.ipc input source ∧
      Stream.Writer.Readback reverse source.schema (source.batches.map Stream.Completed.observed) returned :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.round_trip written forward

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc
