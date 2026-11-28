module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Conversion

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc

open Arrow.RecursiveSchema hiding Limits Error

public section

theorem convert_open_error {limits : Limits} {input : KBytes} {checksum : Bool}
    {cause : Arrow.RecursiveSchema.Error}
    (original : Arrow.RecursiveSchema.readFrame limits.ipc.schema input = .error cause) :
    convert limits input checksum = .error (.openError cause) := by
  simp [convert, Stream.Import.admit, Stream.readTrace_open_error original]

/-- The original cause, frame offset and exact completed prefix take
precedence under every target limit. -/
theorem convert_terminal_error {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} {ordinal offset : Nat} {cause : Stream.Cause}
    (original : Stream.readTrace limits.ipc input = .ok source)
    (failed : source.terminal = .failed ordinal offset cause) :
    convert limits input checksum = .error (.terminal source) := by
  simp [convert, Stream.Import.admit, original, failed]

theorem convert_terminal_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (rejected : convert limits input checksum = .error (.terminal source)) :
    TerminalWire limits.ipc input source :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.terminal_wire rejected

theorem convert_of_strict {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (strict : Stream.read limits.ipc input = .ok source) :
    convert limits input checksum = (Writer.emit limits.parquet (writerInput source checksum)).mapError .writer := by
  simp [convert, Stream.Import.admit_iff.mpr strict]

/-- Any target error comes from the existing writer after exact source EOS. -/
theorem convert_writer_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {cause : Parquet.RecursiveSchema.Tree.Writer.Error} (rejected : convert limits input checksum = .error (.writer cause)) :
    ∃ source, SourceWire limits.ipc input source ∧
      Writer.emit limits.parquet (writerInput source checksum) = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.writer_wire rejected

theorem convert_readback {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} (accepted : convert limits input checksum = .ok output) :
    Readback limits input checksum output :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.readback accepted

/-- At each source ordinal the original IPC record and the corresponding
original Parquet group have exactly the same observation. The group
certificate retains the addressed signed column witnesses. -/
theorem batch_group {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} {snapshot : Snapshot.Checked}
    {compiled : Compiled limits.parquet.schema.snapshot snapshot} {groups : List Writer.WrittenGroup}
    (original : SourceWire limits.ipc input source)
    (reopened : Writer.GroupsReadback limits.parquet compiled 0 (writerInput source checksum).groups groups)
    {index : Nat} {batch : Stream.Completed} (found : source.batches[index]? = some batch) :
    Stream.RecordWire limits.ipc source.schema input index batch.offset batch ∧
      ∃ group, groups[index]? = some group ∧
        Writer.GroupReadback limits.parquet compiled index batch.observed group :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.batch_group original reopened found

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc
