module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc

open Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.RecursiveSchema.Tree Parquet.RecursiveSchema.Tree.Writer.FromIpc
open Arrow.RecursiveSchema hiding Limits Error

public theorem terminal_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (rejected : convert limits input checksum = .error (.terminal source)) :
    TerminalWire limits.ipc input source := by
  cases admitted : Stream.Import.admit limits.ipc input with
  | ok trace =>
    cases written : Writer.emit limits.parquet (writerInput trace checksum) <;>
      simp [convert, admitted, written, Except.mapError] at rejected
  | error cause =>
    cases cause with
    | openError => simp [convert, admitted] at rejected
    | terminal trace =>
      simp only [convert, admitted, Except.error.injEq, Error.terminal.injEq] at rejected
      subst source
      exact Stream.Import.admit_terminal_wire admitted

private theorem writer_result {limits : Limits} {input : KBytes} {checksum : Bool}
    {result : Except Parquet.RecursiveSchema.Tree.Writer.Error Writer.Output}
    (converted : convert limits input checksum = result.mapError Error.writer) :
    ∃ source, SourceWire limits.ipc input source ∧
      Writer.emit limits.parquet (writerInput source checksum) = result := by
  cases admitted : Stream.Import.admit limits.ipc input with
  | error cause => cases cause <;> cases result <;> simp [convert, admitted, Except.mapError] at converted
  | ok source =>
    refine ⟨source, Stream.Import.admit_wire admitted, ?_⟩
    cases written : Writer.emit limits.parquet (writerInput source checksum) <;>
      cases result <;> simp_all [convert, Except.mapError]

public theorem writer_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {cause : Parquet.RecursiveSchema.Tree.Writer.Error} (rejected : convert limits input checksum = .error (.writer cause)) :
    ∃ source, SourceWire limits.ipc input source ∧
      Writer.emit limits.parquet (writerInput source checksum) = .error cause :=
  writer_result (result := .error cause) rejected

public theorem readback {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} (accepted : convert limits input checksum = .ok output) :
    Readback limits input checksum output := by
  obtain ⟨source, original, written⟩ := writer_result (result := .ok output) accepted
  obtain ⟨groups, construction, reopened⟩ := Writer.emit_wire written
  exact ⟨source, groups, original, written, construction, reopened⟩

private theorem record_at {limits : Arrow.RecursiveSchema.Batch.Limits} {input : KBytes}
    {schema : Arrow.RecursiveSchema.Schema} {remaining ordinal offset : Nat}
    {batches : List Stream.Completed} {terminal : Stream.End}
    (chain : Stream.CursorChain limits schema input remaining ordinal offset batches terminal)
    {index : Nat} {batch : Stream.Completed} (found : batches[index]? = some batch) :
    Stream.RecordWire limits schema input (ordinal + index) batch.offset batch := by
  induction chain generalizing index with
  | stop => simp at found
  | more original _ ih =>
    cases index with
    | zero =>
      simp at found
      subst batch
      simpa only [Nat.add_zero, original.coordinates.2.1] using original
    | succ index =>
      have later := ih (by simpa only [List.getElem?_cons_succ] using found)
      simpa only [Nat.add_assoc, Nat.add_comm 1 index] using later

public theorem batch_group {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} {snapshot : Snapshot.Checked}
    {compiled : Compiled limits.parquet.schema.snapshot snapshot} {groups : List Writer.WrittenGroup}
    (original : SourceWire limits.ipc input source)
    (reopened : Writer.GroupsReadback limits.parquet compiled 0 (writerInput source checksum).groups groups)
    {index : Nat} {batch : Stream.Completed} (found : source.batches[index]? = some batch) :
    Stream.RecordWire limits.ipc source.schema input index batch.offset batch ∧
      ∃ group, groups[index]? = some group ∧
        Writer.GroupReadback limits.parquet compiled index batch.observed group := by
  have observed : (writerInput source checksum).groups[index]? = some batch.observed := by
    simp [writerInput, List.getElem?_map, found]
  exact ⟨by simpa only [Nat.zero_add] using record_at original.wire.chain found,
    by simpa only [Nat.zero_add] using reopened.group_at observed⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc
