module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Conversion

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc

public section

theorem schemaOf_exact {source : Signature} {schema : Schema}
    (declared : declarations source = schema.fields.map (fun field => (fieldName field, field))) :
    schemaOf source = schema := by
  cases schema
  simp [schemaOf, declared, List.map_map, Function.comp_def]

theorem emit_read_error {Failure : Type} {limits : Batch.Limits} {source : Signature}
    {trace : Arrow.Events.Trace source Value Failure} {cause : Failure}
    (failed : trace.termination = .readError cause) :
    emit limits (.ok ⟨source, trace⟩) = .error (.readError cause (trace.batches.map eraseBatch)) := by
  simp [emit, failed]

theorem emit_readback {Failure : Type} {limits : Batch.Limits}
    {source : Signature} {trace : Arrow.Events.Trace source Value Failure} {wire : KBytes}
    (accepted : emit limits (.ok ⟨source, trace⟩) = .ok wire) :
    trace.termination = .eos ∧ Stream.Writer.Readback limits (schemaOf source) (trace.batches.map eraseBatch) wire :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.emit_readback accepted

/-- The strict IPC reader observes the same positional names and fields,
complete batches and EOS when the input labels are the field names. -/
theorem agrees_events {Failure : Type} {limits : Batch.Limits}
    {source : Signature} {trace : Arrow.Events.Trace source Value Failure} {wire : KBytes}
    {native : Σ sig : Signature, Events.Trace sig}
    (names : declarations source = (schemaOf source).fields.map (fun field => (fieldName field, field)))
    (accepted : emit limits (.ok ⟨source, trace⟩) = .ok wire)
    (readback : Events.read limits wire = .ok native) :
    declarations native.1 = declarations source ∧
      native.2.batches.map eraseBatch = trace.batches.map eraseBatch ∧ native.2.termination = .eos :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.agrees_events names accepted readback

end

end Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc
