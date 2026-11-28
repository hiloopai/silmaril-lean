module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc

open Silmaril.Formats
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Writer.FromIpc
open Arrow.RecursiveSchema hiding Limits Error
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)

public theorem convert_terminal_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (rejected : convert limits input checksum = .error (.terminal source)) :
    TerminalWire limits.ipc input source := by
  unfold convert at rejected
  cases decoded : Stream.readTrace limits.ipc input with
  | error => simp [decoded, Except.mapError, bind, Except.bind] at rejected
  | ok trace =>
    simp only [decoded, Except.mapError, bind, Except.bind] at rejected
    cases terminal : trace.terminal with
    | eos =>
      cases written : Writer.emit limits.parquet (writerInput trace checksum) <;>
        simp [terminal, written] at rejected
    | failed ordinal offset cause =>
      simp only [terminal, Except.error.injEq, Error.terminal.injEq] at rejected
      subst source
      obtain ⟨count, remaining, budget, failure⟩ := Stream.readTrace_failure decoded terminal
      subst ordinal
      exact ⟨decoded, Stream.readTrace_wire decoded, offset, cause, remaining, terminal, budget, failure⟩

private theorem writer_result {limits : Limits} {input : KBytes} {checksum : Bool}
    {result : Except Parquet.RecursiveSchema.ListPath.Writer.Error Writer.Output}
    (converted : convert limits input checksum = result.mapError Error.writer) :
    ∃ source, SourceWire limits.ipc input source ∧
      Writer.emit limits.parquet (writerInput source checksum) = result := by
  unfold convert at converted
  cases decoded : Stream.readTrace limits.ipc input with
  | error => cases result <;> simp [decoded, Except.mapError, bind, Except.bind] at converted
  | ok source =>
    simp only [decoded, Except.mapError, bind, Except.bind] at converted
    cases terminal : source.terminal with
    | failed => cases result <;> simp [terminal] at converted
    | eos ordinal offset =>
      have writer : Writer.emit limits.parquet (writerInput source checksum) = result := by
        cases current : Writer.emit limits.parquet (writerInput source checksum) <;>
          cases result <;> simp_all
      obtain ⟨count, envelope, extent⟩ := Stream.readTrace_eos decoded terminal
      have strict := Stream.read_iff.mpr ⟨decoded, ordinal, offset, terminal⟩
      subst ordinal
      exact ⟨source, ⟨strict, Stream.readTrace_wire decoded, offset, terminal, envelope, extent⟩, writer⟩

public theorem convert_writer_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {cause : Parquet.RecursiveSchema.ListPath.Writer.Error} (rejected : convert limits input checksum = .error (.writer cause)) :
    ∃ source, SourceWire limits.ipc input source ∧
      Writer.emit limits.parquet (writerInput source checksum) = .error cause :=
  writer_result (result := .error cause) rejected

public theorem convert_readback {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} (accepted : convert limits input checksum = .ok output) :
    Readback limits input checksum output := by
  obtain ⟨source, checked, written⟩ := writer_result (result := .ok output) accepted
  exact ⟨source, checked, written, Writer.emit_wire written⟩

public theorem agrees_events {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} {parquet : Σ sig : Signature, Reader.Events.Trace sig}
    {ipc : Σ sig : Signature, Stream.Events.Trace sig}
    (written : convert limits input checksum = .ok output)
    (direct : Reader.Events.read limits.parquet.schema.snapshot limits.parquet.chunk output.bytes = .ok parquet)
    (original : Stream.Events.read limits.ipc input = .ok ipc) :
    declarations parquet.1 = declarations ipc.1 ∧
    parquet.2.batches.map eraseBatch = ipc.2.batches.map eraseBatch ∧
    parquet.2.termination = .eos ∧ ipc.2.termination = .eos := by
  obtain ⟨source, checked, _, _, readback⟩ := (convert_readback written).original
  obtain ⟨_, events, _, _, _, _, _, _, read, fields, ending, batches, _, _⟩ := readback.original
  obtain ⟨_, eos, _, _⟩ := checked.eos
  obtain ⟨sourceFields, sourceBatches, sourceEnd⟩ :=
    Stream.Events.read_checked_eos checked.checked eos original
  cases Except.ok.inj (direct.symm.trans read)
  exact ⟨fields.trans sourceFields.symm, batches.trans sourceBatches.symm, ending, sourceEnd⟩

public theorem round_trip {limits : Limits} {input returned : KBytes} {checksum : Bool}
    {output : Writer.Output} {reverse : Arrow.RecursiveSchema.Batch.Limits}
    (written : convert limits input checksum = .ok output)
    (forward : Reader.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.chunk reverse
      output.bytes .field = .ok returned) :
    ∃ source, SourceWire limits.ipc input source ∧
      Stream.Writer.Readback reverse source.schema (source.batches.map Stream.Completed.observed) returned := by
  obtain ⟨source, original, _, _, readback⟩ := (convert_readback written).original
  obtain ⟨opened, _, reopen, _, _, _, fields, _, _, _, _, _, groups, _⟩ := readback.original
  obtain ⟨sameFile, completed, sameOpen, read, _, certificate⟩ := (Reader.ToIpc.convert_readback forward).original
  cases Except.ok.inj (sameOpen.symm.trans reopen)
  cases Except.ok.inj (read.symm.trans groups)
  refine ⟨source, original, ?_⟩
  simpa only [Parquet.Reader.Recursive.Selection.schema, fields,
    show Parquet.Reader.Recursive.Selection.batch .field = id from rfl, List.map_id, writerInput] using certificate

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc
