module

public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.Events.Prefix
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.Events.Ipc

namespace Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events

@[expose] public section

open Silmaril.Relational
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)

theorem read_open_error {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {bytes : Bytes}
    {cause : RecursiveSchema.Error} (original : openFile schemaLimits bytes = .error cause) :
    read schemaLimits limits bytes = .error (.openError cause) := by
  simp [read, original]

theorem readSource_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) : SourceWire limits schema events.1 events.2 :=
  Proofs.Formats.Parquet.RecursiveSchema.Rows.Events.readSource_wire accepted

/-- Each emitted batch has the original row group's wire witness. The trace
retains precisely the complete prefix and the original reached failure or EOS. -/
theorem read_wire {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : read schemaLimits limits bytes = .ok events) :
    FileWire schemaLimits limits bytes events.1 events.2 :=
  Proofs.Formats.Parquet.RecursiveSchema.Rows.Events.read_wire accepted

theorem read_failure {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source} {ordinal : Nat} {cause : Rows.Error}
    (accepted : read schemaLimits limits bytes = .ok events)
    (failed : events.2.termination = .readError (.group ordinal cause)) :
    ordinal = events.2.batches.length ∧
      ∃ opened, openFile schemaLimits bytes = .ok opened ∧
        Rows.readGroup limits opened.schema ordinal = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.Rows.Events.read_failure accepted failed

theorem read_eos {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : read schemaLimits limits bytes = .ok events)
    (eos : events.2.termination = .eos) :
    ∃ opened, openFile schemaLimits bytes = .ok opened ∧
      Rows.readAll limits opened.schema = .ok (events.2.batches.map eraseBatch) :=
  Proofs.Formats.Parquet.RecursiveSchema.Rows.Events.read_eos accepted eos

theorem readProjected_open_error {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {bytes : Bytes} {cause : RecursiveSchema.Error}
    (original : openFile schemaLimits bytes = .error cause)
    (projection : (source : Signature) → Scan.Projection source) :
    readProjected schemaLimits limits bytes projection = .error (.openError cause) := by
  simp [readProjected, Arrow.RecursiveSchema.Stream.Events.project, read_open_error original,
    Except.map]

theorem readProjected_of_read {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {bytes : Bytes} {source : Signature} {events : Trace source}
    (accepted : read schemaLimits limits bytes = .ok ⟨source, events⟩)
    (projection : (source : Signature) → Scan.Projection source) :
    readProjected schemaLimits limits bytes projection =
      .ok ⟨(projection source).schema, projectTrace (projection source) events⟩ := by
  simp [readProjected, Arrow.RecursiveSchema.Stream.Events.project, accepted, Except.map]

/-- The direct and native IPC routes agree on ordered declarations, logical
batches with explicit counts, and EOS whenever the native output succeeds. -/
theorem agrees_ipc {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {bytes : KBytes}
    {direct : Σ source : Signature, Trace source}
    {native : Σ source : Signature, Arrow.RecursiveSchema.Stream.Events.Trace source}
    (accepted : readSource limits schema = .ok direct)
    (written : Rows.ToIpc.convert limits ipc schema = .ok bytes)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc bytes = .ok native) :
    declarations direct.1 = declarations native.1 ∧
      direct.2.batches.map eraseBatch = native.2.batches.map eraseBatch ∧
      direct.2.termination = .eos ∧ native.2.termination = .eos :=
  Proofs.Formats.Parquet.RecursiveSchema.Rows.Events.agrees_ipc accepted written readback

end

end Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events
