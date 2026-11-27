module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Defs

/-! Checked recursive Arrow V5 IPC to a complete native signed Parquet file. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc

open Arrow.RecursiveSchema
open Arrow.RecursiveSchema.Stream (Completed Trace)

@[expose] public section

structure Limits where
  ipc : Arrow.RecursiveSchema.Batch.Limits := {}
  parquet : Writer.Limits := {}

structure Options where
  checksum : Bool := false
  /-- When supplied, every native batch has one entry. Within a batch,
  the entries are explicit per-leaf page slot counts in physical order. -/
  cuts : Option (List (List (List Nat))) := none

inductive Error where
  | openError (original : Arrow.RecursiveSchema.Error)
  | terminal (original : Trace)
  | cutGroups (expected actual : Nat)
  | writer (original : Writer.Error)
  deriving Repr

/-- Keep the original schema and one group for each completed native batch.
Explicit partitions must cover the entire ordered batch vector. -/
def writerInput (options : Options) (source : Trace) : Except Error Writer.Input :=
  match options.cuts with
  | none => .ok ⟨source.schema, source.batches.map (fun batch => ⟨batch.observed, none⟩), options.checksum⟩
  | some cuts =>
    if cuts.length = source.batches.length then
      .ok ⟨source.schema,
        List.zipWith (fun batch sizes => ⟨batch.observed, some sizes⟩) source.batches cuts,
        options.checksum⟩
    else .error (.cutGroups source.batches.length cuts.length)

/-- Complete the strict native reader before applying any writer option
or limit. A terminal refusal carries the original completed prefix. -/
def convert (limits : Limits) (options : Options) (input : KBytes) : Except Error Writer.Output := do
  let source ← (Stream.readTrace limits.ipc input).mapError .openError
  match source.terminal with
  | .failed .. => .error (.terminal source)
  | .eos .. =>
    let rows ← writerInput options source
    (Writer.emit limits.parquet rows).mapError .writer

structure SourceWire (limits : Arrow.RecursiveSchema.Batch.Limits)
    (input : KBytes) (source : Trace) : Prop where
  trace : Stream.readTrace limits input = .ok source
  wire : Stream.TraceWire limits input source
  eos : ∃ offset, source.terminal = .eos source.batches.length offset ∧
    Arrow.EnvelopeWire limits.schema.ipc input.toList offset .eos ∧ offset + 8 = input.len

structure TerminalWire (limits : Arrow.RecursiveSchema.Batch.Limits)
    (input : KBytes) (source : Trace) : Prop where
  trace : Stream.readTrace limits input = .ok source
  wire : Stream.TraceWire limits input source
  failed : ∃ offset cause remaining,
    source.terminal = .failed source.batches.length offset cause ∧
    remaining + source.batches.length = limits.schema.ipc.batches ∧
    Stream.FailureWire limits source.schema input offset remaining cause

/-- Native source witnesses and exact logical file readback refer to the
same unmodified declaration and one observation per original batch. -/
structure Readback (limits : Limits) (options : Options) (input : KBytes)
    (output : Writer.Output) : Prop where
  original : ∃ (source : Trace) (rows : Writer.Input),
    SourceWire limits.ipc input source ∧ writerInput options source = .ok rows ∧
    rows.schema = source.schema ∧ rows.observations = source.batches.map Completed.observed ∧
    Writer.emit limits.parquet rows = .ok output ∧
    Writer.Construction limits.parquet rows output ∧ Writer.Readback limits.parquet rows output

/-- The two exact EOS streams share positional declarations, logical rows
and explicit batch row counts. Their physical byte layouts may differ. -/
structure RoundTripWire (forward reverse : Arrow.RecursiveSchema.Batch.Limits)
    (input returned : KBytes) : Prop where
  original : ∃ (source result : Trace) (offset : Nat),
    SourceWire forward input source ∧
    Stream.read reverse returned = .ok result ∧ Stream.TraceWire reverse returned result ∧
    result.schema = source.schema ∧
    result.batches.map Completed.observed = source.batches.map Completed.observed ∧
    result.terminal = .eos source.batches.length offset ∧
    Arrow.EnvelopeWire reverse.schema.ipc returned.toList offset .eos ∧ offset + 8 = returned.len

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc
