module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.Defs

/-! Strict recursive Arrow V5 IPC to the checked canonical two-LIST Parquet file. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc

open Arrow.RecursiveSchema.Stream (Completed Trace)

@[expose] public section

structure Limits where
  ipc : Arrow.RecursiveSchema.Batch.Limits := {}
  parquet : Writer.Limits := {}

inductive Error where
  | openError (original : Arrow.RecursiveSchema.Error)
  | terminal (original : Trace)
  | writer (original : Writer.Error)
  deriving Repr

/-- Preserve the original declaration and one group per native record batch. -/
def writerInput (source : Trace) (checksum : Bool) : Writer.Input :=
  ⟨source.schema, source.batches.map Completed.observed, checksum⟩

/-- Finish checking the IPC stream before admitting any Parquet output.
A terminal error retains the original cursor, cause and complete prefix. -/
def convert (limits : Limits) (input : KBytes) (checksum : Bool := false) :
    Except Error Writer.Output := do
  let source ← (Arrow.RecursiveSchema.Stream.readTrace limits.ipc input).mapError .openError
  match source.terminal with
  | .failed .. => .error (.terminal source)
  | .eos .. => (Writer.emit limits.parquet (writerInput source checksum)).mapError .writer

structure SourceWire (limits : Arrow.RecursiveSchema.Batch.Limits) (input : KBytes)
    (source : Trace) : Prop where
  checked : Arrow.RecursiveSchema.Stream.read limits input = .ok source
  wire : Arrow.RecursiveSchema.Stream.TraceWire limits input source
  eos : ∃ offset, source.terminal = .eos source.batches.length offset ∧
    Arrow.EnvelopeWire limits.schema.ipc input.toList offset .eos ∧ offset + 8 = input.len

structure TerminalWire (limits : Arrow.RecursiveSchema.Batch.Limits) (input : KBytes)
    (source : Trace) : Prop where
  trace : Arrow.RecursiveSchema.Stream.readTrace limits input = .ok source
  wire : Arrow.RecursiveSchema.Stream.TraceWire limits input source
  failed : ∃ offset cause remaining,
    source.terminal = .failed source.batches.length offset cause ∧
    remaining + source.batches.length = limits.schema.ipc.batches ∧
    Arrow.RecursiveSchema.Stream.FailureWire limits source.schema input offset remaining cause

/-- Bind the original strict stream, native construction and exact logical
Parquet readback using the same ordered schema and batch observations. -/
structure Readback (limits : Limits) (input : KBytes) (checksum : Bool)
    (output : Writer.Output) : Prop where
  original : ∃ source,
    SourceWire limits.ipc input source ∧
    Writer.emit limits.parquet (writerInput source checksum) = .ok output ∧
    Writer.Construction limits.parquet (writerInput source checksum) output ∧
    Writer.Readback limits.parquet (writerInput source checksum) output

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc
