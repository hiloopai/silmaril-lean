module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc

open Silmaril.Formats
open Silmaril.Formats.Arrow
open RecursiveSchema.Stream.Events (Signature Value declarations eraseBatch fieldName)
open RecursiveSchema.Stream.Events.ToIpc

public theorem emit_readback {Failure : Type} {limits : RecursiveSchema.Batch.Limits}
    {source : Signature} {trace : Arrow.Events.Trace source Value Failure} {wire : KBytes}
    (accepted : emit limits (.ok ⟨source, trace⟩) = .ok wire) :
    trace.termination = .eos ∧
      RecursiveSchema.Stream.Writer.Readback limits (schemaOf source) (trace.batches.map eraseBatch) wire := by
  cases ending : trace.termination with
  | closed => simp [emit, ending] at accepted
  | readError cause => simp [emit, ending] at accepted
  | closeError cause => simp [emit, ending] at accepted
  | eos =>
    cases written : RecursiveSchema.Stream.Writer.emit limits (schemaOf source) (trace.batches.map eraseBatch) with
    | error cause => simp [emit, ending, written, Except.mapError] at accepted
    | ok output =>
      have same : output = wire := by simpa [emit, ending, written, Except.mapError] using accepted
      exact ⟨rfl, same ▸ RecursiveSchema.Stream.Writer.emit_readback written⟩

public theorem agrees_events {Failure : Type} {limits : RecursiveSchema.Batch.Limits}
    {source : Signature} {trace : Arrow.Events.Trace source Value Failure} {wire : KBytes}
    {native : Σ sig : Signature, RecursiveSchema.Stream.Events.Trace sig}
    (names : declarations source = (schemaOf source).fields.map (fun field => (fieldName field, field)))
    (accepted : emit limits (.ok ⟨source, trace⟩) = .ok wire)
    (readback : RecursiveSchema.Stream.Events.read limits wire = .ok native) :
    declarations native.1 = declarations source ∧
      native.2.batches.map eraseBatch = trace.batches.map eraseBatch ∧ native.2.termination = .eos := by
  obtain ⟨_, checked⟩ := emit_readback accepted
  obtain ⟨_, _, strict, _, schema, batches, ending, _, _⟩ := checked.result
  obtain ⟨declared, groups, terminal⟩ :=
    RecursiveSchema.Stream.Events.read_checked_eos strict ending readback
  rw [schema, ← names] at declared
  exact ⟨declared, groups.trans batches, terminal⟩

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc
