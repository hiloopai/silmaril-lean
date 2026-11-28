module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Conversion

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc

open Arrow.RecursiveSchema hiding Limits Error
open Parquet.Reader.Recursive (Selection)

public section

theorem convert_open_error {limits : Limits} {input : KBytes} {checksum : Bool}
    {cause : Arrow.RecursiveSchema.Error}
    (original : Arrow.RecursiveSchema.readFrame limits.ipc.schema input = .error cause) :
    convert limits input checksum = .error (.openError cause) := by
  simp [convert, Stream.Import.admit, Stream.readTrace_open_error original]

/-- The first original failure and complete prefix take precedence under
every Parquet budget. -/
theorem convert_terminal_error {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} {ordinal offset : Nat} {cause : Stream.Cause}
    (original : Stream.readTrace limits.ipc input = .ok source)
    (failed : source.terminal = .failed ordinal offset cause) :
    convert limits input checksum = .error (.terminal source) := by
  simp [convert, Stream.Import.admit, original, failed]

theorem convert_terminal_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (rejected : convert limits input checksum = .error (.terminal source)) :
    TerminalWire limits.ipc input source :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.convert_terminal_wire rejected

/-- Once the original stream is strict, the result is the original writer's
output or typed cause for the exact source observations. -/
theorem convert_of_strict {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (strict : Stream.read limits.ipc input = .ok source)
    (supported : Writer.supportsRequiredDeclaration source.schema = true) :
    convert limits input checksum = (Writer.emit limits.parquet (writerInput source checksum)).mapError .writer := by
  simp [convert, Stream.Import.admit_iff.mpr strict, supported]

/-- Unsupported or unnamed declarations retain the complete strict source
trace before any writer budget is consulted. -/
theorem convert_declaration_error {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (strict : Stream.read limits.ipc input = .ok source)
    (unsupported : Writer.supportsRequiredDeclaration source.schema = false) :
    convert limits input checksum = .error (.declaration source) := by
  simp [convert, Stream.Import.admit_iff.mpr strict, unsupported]

theorem convert_declaration_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (rejected : convert limits input checksum = .error (.declaration source)) :
    SourceWire limits.ipc input source ∧ Writer.supportsRequiredDeclaration source.schema = false :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.convert_declaration_wire rejected

theorem convert_writer_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {cause : Writer.Error} (rejected : convert limits input checksum = .error (.writer cause)) :
    ∃ source, SourceWire limits.ipc input source ∧
      Writer.emit limits.parquet (writerInput source checksum) = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.convert_writer_wire rejected

theorem convert_readback {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} (accepted : convert limits input checksum = .ok output) :
    Readback limits input checksum output :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.convert_readback accepted

/-- An admitted forward bridge preserves the selected declaration and
observations of the strict source through the returned IPC's exact EOS. -/
theorem round_trip {limits : Limits} {input returned : KBytes} {checksum : Bool}
    {output : Writer.Output} {reverse : Arrow.RecursiveSchema.Batch.Limits} {selection : Selection}
    (written : convert limits input checksum = .ok output)
    (forward : Reader.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.chunk reverse
      output.bytes selection = .ok returned) :
    ∃ source, SourceWire limits.ipc input source ∧
      Stream.Writer.Readback reverse (selection.schema source.schema)
        ((source.batches.map Stream.Completed.observed).map selection.batch) returned :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.round_trip written forward

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc
