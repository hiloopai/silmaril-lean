module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc

open Silmaril.Formats
open Parquet.RecursiveSchema.TwoListStruct
open Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc
open Arrow.RecursiveSchema hiding Limits Error
open Parquet.Reader.Recursive (Selection)

public theorem convert_terminal_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (rejected : convert limits input checksum = .error (.terminal source)) :
    TerminalWire limits.ipc input source := by
  cases admitted : Stream.Import.admit limits.ipc input with
  | ok trace =>
    cases supported : Writer.supportsDeclaration trace.schema <;>
      cases writer : Writer.emit limits.parquet (writerInput trace checksum) <;>
      simp [convert, admitted, supported, writer, Except.mapError] at rejected
  | error cause =>
    cases cause with
    | openError => simp [convert, admitted] at rejected
    | terminal trace =>
      simp only [convert, admitted, Except.error.injEq, Error.terminal.injEq] at rejected
      subst source
      exact Stream.Import.admit_terminal_wire admitted

public theorem convert_declaration_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (rejected : convert limits input checksum = .error (.declaration source)) :
    SourceWire limits.ipc input source ∧ Writer.supportsDeclaration source.schema = false := by
  cases admitted : Stream.Import.admit limits.ipc input with
  | error cause => cases cause <;> simp [convert, admitted] at rejected
  | ok trace =>
    cases supported : Writer.supportsDeclaration trace.schema with
    | true =>
      cases writer : Writer.emit limits.parquet (writerInput trace checksum) <;>
        simp [convert, admitted, supported, writer, Except.mapError] at rejected
    | false =>
      simp only [convert, admitted, supported, Bool.false_eq_true, ite_false,
        Except.error.injEq, Error.declaration.injEq] at rejected
      subst source
      exact ⟨Stream.Import.admit_wire admitted, supported⟩

private theorem writer_result {limits : Limits} {input : KBytes} {checksum : Bool}
    {result : Except Parquet.RecursiveSchema.TwoListStruct.Writer.Error Writer.Output}
    (converted : convert limits input checksum = result.mapError Error.writer) :
    ∃ source, SourceWire limits.ipc input source ∧
      Writer.emit limits.parquet (writerInput source checksum) = result := by
  cases admitted : Stream.Import.admit limits.ipc input with
  | error cause => cases cause <;> cases result <;> simp [convert, admitted, Except.mapError] at converted
  | ok source =>
    cases supported : Writer.supportsDeclaration source.schema with
    | false => cases result <;> simp [convert, admitted, supported, Except.mapError] at converted
    | true =>
      refine ⟨source, Stream.Import.admit_wire admitted, ?_⟩
      cases current : Writer.emit limits.parquet (writerInput source checksum) <;>
        cases result <;> simp_all [convert, Except.mapError]

public theorem convert_writer_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {cause : Parquet.RecursiveSchema.TwoListStruct.Writer.Error} (rejected : convert limits input checksum = .error (.writer cause)) :
    ∃ source, SourceWire limits.ipc input source ∧
      Writer.emit limits.parquet (writerInput source checksum) = .error cause :=
  writer_result (result := .error cause) rejected

public theorem convert_readback {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} (accepted : convert limits input checksum = .ok output) :
    Readback limits input checksum output := by
  obtain ⟨source, checked, written⟩ := writer_result (result := .ok output) accepted
  exact ⟨source, checked, written, Writer.emit_wire written⟩

public theorem round_trip {limits : Limits} {input returned : KBytes} {checksum : Bool}
    {output : Writer.Output} {reverse : Arrow.RecursiveSchema.Batch.Limits} {selection : Selection}
    (written : convert limits input checksum = .ok output)
    (forward : Reader.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.chunk reverse
      output.bytes selection = .ok returned) :
    ∃ source, SourceWire limits.ipc input source ∧
      Stream.Writer.Readback reverse (selection.schema source.schema)
        ((source.batches.map Stream.Completed.observed).map selection.batch) returned := by
  obtain ⟨source, original, _, _, readback⟩ := (convert_readback written).original
  obtain ⟨opened, reopen, _, _, _, fields, _, groups, _⟩ := readback.original
  obtain ⟨sameFile, completed, sameOpen, read, _, certificate⟩ := (Reader.ToIpc.convert_readback forward).original
  cases Except.ok.inj (sameOpen.symm.trans reopen)
  cases Except.ok.inj (read.symm.trans groups)
  exact ⟨source, original, by simpa only [fields, writerInput] using certificate⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc
