module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.Conversion
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.RoundTrip

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc

open Arrow.RecursiveSchema.Stream (Completed Trace)

@[expose] public section

theorem SourceWire.strict {limits : Arrow.RecursiveSchema.Batch.Limits} {input : KBytes}
    {source : Trace} (checked : SourceWire limits input source) :
    Arrow.RecursiveSchema.Stream.read limits input = .ok source := by
  obtain ⟨offset, eos, _, _⟩ := checked.eos
  exact Arrow.RecursiveSchema.Stream.read_iff.mpr ⟨checked.trace, _, offset, eos⟩

theorem writerInput_exact {options : Options} {source : Trace} {rows : Writer.Input}
    (bound : writerInput options source = .ok rows) :
    rows.schema = source.schema ∧ rows.observations = source.batches.map Completed.observed ∧
      rows.checksum = options.checksum :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.writerInput_exact bound

theorem convert_open_error {limits : Limits} {options : Options} {input : KBytes}
    {cause : Arrow.RecursiveSchema.Error}
    (original : Arrow.RecursiveSchema.readFrame limits.ipc.schema input = .error cause) :
    convert limits options input = .error (.openError cause) := by
  simp [convert, Arrow.RecursiveSchema.Stream.readTrace_open_error original, Except.mapError, Except.bind, bind]

/-- Any reached source failure precedes every writer option and budget. -/
theorem convert_terminal_error {limits : Limits} {options : Options} {input : KBytes}
    {source : Trace} {ordinal offset : Nat} {cause : Arrow.RecursiveSchema.Stream.Cause}
    (original : Arrow.RecursiveSchema.Stream.readTrace limits.ipc input = .ok source)
    (failed : source.terminal = .failed ordinal offset cause) :
    convert limits options input = .error (.terminal source) := by
  simp [convert, original, failed, Except.mapError, Except.bind, bind]

/-- The retained trace binds the exact checked prefix and first original cause. -/
theorem convert_terminal_wire {limits : Limits} {options : Options} {input : KBytes}
    {source : Trace} (rejected : convert limits options input = .error (.terminal source)) :
    TerminalWire limits.ipc input source :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.terminal_wire rejected

theorem convert_writer_error {limits : Limits} {options : Options} {input : KBytes}
    {source : Trace} {rows : Writer.Input} {cause : Writer.Error}
    (original : SourceWire limits.ipc input source)
    (bound : writerInput options source = .ok rows)
    (failed : Writer.emit limits.parquet rows = .error cause) :
    convert limits options input = .error (.writer cause) := by
  obtain ⟨_, eos, _, _⟩ := original.eos
  simp [convert, original.trace, eos, bound, failed, Except.mapError, Except.bind, bind]

/-- Strict source completion and the actual native file share the original
declaration and one ordered row-group observation per original batch. -/
theorem convert_readback {limits : Limits} {options : Options} {input : KBytes}
    {output : Writer.Output} (accepted : convert limits options input = .ok output) :
    Readback limits options input output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.convert_readback accepted

theorem Readback.file {limits : Limits} {options : Options} {input : KBytes}
    {output : Writer.Output} (readback : Readback limits options input output) :
    ∃ (trace : Trace) (file : Source limits.parquet.schema.snapshot output.bytes),
      SourceWire limits.ipc input trace ∧
      openFile limits.parquet.schema.snapshot output.bytes = .ok file ∧
      file.snapshot.bytes = output.bytes ∧ file.snapshot.footer = output.footer ∧
      file.snapshot.metadata = output.metadata ∧ file.schema.arrow = trace.schema ∧
      file.snapshot.groupCount = trace.batches.length ∧
      Rows.readAll limits.parquet.rows file.schema = .ok (trace.batches.map Completed.observed) ∧
      List.Forall₂ (Rows.GroupWire limits.parquet.rows file.schema)
        (List.range file.snapshot.groupCount) (trace.batches.map Completed.observed) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.file readback

/-- Successful native conversion in both directions preserves declarations,
logical batches and their explicit counts, through exact EOS at both ends. -/
theorem round_trip {limits : Limits} {options : Options} {input returned : KBytes}
    {output : Writer.Output} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {decoded : Source limits.parquet.schema.snapshot output.bytes}
    (written : convert limits options input = .ok output)
    (opened : openFile limits.parquet.schema.snapshot output.bytes = .ok decoded)
    (reverse : Rows.ToIpc.convert limits.parquet.rows ipc decoded.schema = .ok returned) :
    RoundTripWire limits.ipc ipc input returned :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.round_trip written opened reverse

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc
