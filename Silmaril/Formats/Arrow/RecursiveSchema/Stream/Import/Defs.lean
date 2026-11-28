module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Defs

/-! Strict source admission for consumers that need the original IPC
failure and completed prefix before admitting a target. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import

@[expose] public section

inductive Error where
  | openError (original : RecursiveSchema.Error)
  | terminal (original : Trace)
  deriving Repr

def admit (limits : Batch.Limits) (input : KBytes) : Except Error Trace :=
  match readTrace limits input with
  | .error cause => .error (.openError cause)
  | .ok source =>
    match source.terminal with
    | .failed .. => .error (.terminal source)
    | .eos .. => .ok source

structure SourceWire (limits : Batch.Limits) (input : KBytes) (source : Trace) : Prop where
  checked : read limits input = .ok source
  wire : TraceWire limits input source
  eos : ∃ offset, source.terminal = .eos source.batches.length offset ∧
    EnvelopeWire limits.schema.ipc input.toList offset .eos ∧ offset + 8 = input.len

structure TerminalWire (limits : Batch.Limits) (input : KBytes) (source : Trace) : Prop where
  trace : readTrace limits input = .ok source
  wire : TraceWire limits input source
  failed : ∃ offset cause remaining,
    source.terminal = .failed source.batches.length offset cause ∧
    remaining + source.batches.length = limits.schema.ipc.batches ∧
    FailureWire limits source.schema input offset remaining cause

end

end Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import
