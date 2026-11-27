module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Defs
import Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Correctness

public section

namespace Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

open Arrow.MixedFlat

/-- The native pull reader reaches exact EOS after delivering the ordered
writer observations, including every explicit empty record. -/
theorem read_emitted {limits : Arrow.MixedFlat.Limits} {fields : List Field}
    {batches : List OrderedWriter.BatchInput} {wire : KBytes}
    (emitted : OrderedWriter.emit limits fields batches = .ok wire) :
    readEvents limits wire = observeSource ⟨fields, batches.map OrderedWriter.BatchInput.observe⟩ ∧
      ∃ (start : Nat) (trace : Stream.Events.Trace (Arrow.MixedFlat.Events.schema fields)),
        Stream.readSchemaFrame limits.observation.ipc wire = .ok (fields, start) ∧
        Stream.Events.readAll limits wire = .ok ⟨Arrow.MixedFlat.Events.schema fields, trace⟩ ∧
        trace.termination = .eos :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.read_emitted emitted

/-- The exact-EOS pull observation also agrees under an explicit writer profile. -/
theorem read_emittedWith {limits : Arrow.MixedFlat.Limits} {fields : List Field}
    {batches : List OrderedWriter.BatchInput} {admit : List Field → Bool} {wire : KBytes}
    (emitted : OrderedWriter.emitWith limits fields batches admit = .ok wire) :
    readEvents limits wire = observeSource ⟨fields, batches.map OrderedWriter.BatchInput.observe⟩ :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.read_emittedWith emitted

/-- Source selection and native event selection agree in the common octet model. -/
theorem project_source {positions : List Nat} {wide direct : Observation}
    (projected : project positions wide = some direct) :
    ∃ wideEvents directEvents, observeSource wide = some wideEvents ∧
      observeSource direct = some directEvents ∧ projectEvents positions wideEvents = some directEvents :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.project_source projected

/-- Projection preserves the batch count and the row count at every batch
ordinal, including zero-width and zero-row batches. -/
theorem projectEvents_rowCounts {positions : List Nat} {wide direct : EventObservation}
    (projected : projectEvents positions wide = some direct) :
    direct.batches.map Prod.fst = wide.batches.map Prod.fst :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.projectEvents_rowCounts projected

/-- Independent direct Parquet caps guarantee the composed source read.
If each checked IPC profile admits its own output, the complete native
event traces agree under positional selection. -/
theorem convert_compose_events {originalLimits directLimits : FlatProjection.Limits}
    {wideIpc directIpc : Arrow.MixedFlat.Limits} {input : Bytes} {ordinals positions composed : List Nat}
    {original : Checked} {wide : List OrderedWriter.BatchInput}
    (same : SameColumnPolicy originalLimits directLimits)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (originalRead : original.readAll originalLimits = .ok wide)
    (fileBytes : input.length ≤ directLimits.column.maxFileBytes)
    (rows : original.snapshot.metadata.numRows.toNat ≤ directLimits.maxFileRows)
    (fields : composed.length ≤ directLimits.maxFields) :
    ∃ direct narrow, openFile directLimits input composed = .ok direct ∧
      direct.readAll directLimits = .ok narrow ∧
      ∀ {wideWire directWire : KBytes},
        OrderedWriter.emit wideIpc original.fields wide = .ok wideWire →
        OrderedWriter.emit directIpc direct.fields narrow = .ok directWire →
        convert originalLimits wideIpc input ordinals = .ok wideWire ∧
        convert directLimits directIpc input composed = .ok directWire ∧
        ∃ wideEvents directEvents,
          readEvents wideIpc wideWire = some wideEvents ∧
          readEvents directIpc directWire = some directEvents ∧
          projectEvents positions wideEvents = some directEvents :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.convert_compose_events
    same composition originalOpen originalRead fileBytes rows fields

end Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
