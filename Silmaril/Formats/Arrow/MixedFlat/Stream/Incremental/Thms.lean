module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Laws

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental

open Arrow.Framing.Incremental (Frame Window metadataBytes)

/-- A published record uses the complete mixed metadata and body decoders. Its
batch ordinal and running row, cell, and data-buffer checks have passed. -/
theorem decode_checked {limits : Limits} {fields : List MixedFlat.Field}
    {running : Running} {frame : Frame} {value : Delivered fields}
    (decoded : decode limits fields running frame = .ok value) :
    ∃ metadata,
      MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
        limits.mixed.totalDataBuffers fields (metadataBytes frame.metadata) = .ok metadata ∧
      running.ordinal < limits.mixed.observation.ipc.batches ∧
      value.dataBuffers = metadata.counts.sum ∧
      running.dataBuffers + value.dataBuffers ≤ limits.totalDataBuffers ∧
      Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) = .ok () ∧
      MixedFlat.readParsed limits.mixed fields metadata
        (.leaf frame.body.len (frame.body.read 0 frame.body.len)) = .ok value.record.observed ∧
      value.record.range = frameRange frame :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.decode_checked decoded

/-- A framed publication on a packed reference supplies exactly the original
metadata and body slices for subsequent typed checks. -/
theorem packed_frame {ipc : Arrow.Limits} {len raw : Nat} {frame : Frame}
    (original : frame.InCarrier ipc (.leaf len raw)) (bodyWf : frame.body.wf = true) :
    metadataBytes frame.metadata = (KBytes.leaf len raw).slice (frame.offset + 8) frame.metadata.len ∧
      readBody ipc (.leaf len raw) (frame.offset + 8 + frame.metadata.len) frame.body.len =
        .ok (metadataBytes frame.body) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.packed_frame original bodyWf

/-- A field error has passed the batch, metadata, running budgets and body
layout checks. It retains the exact downstream column cause. -/
theorem decode_field_checked {limits : Limits}
    {fields : List MixedFlat.Field} {running : Running} {frame : Frame}
    {index : Nat} {cause : MixedFlat.ColumnError}
    (failed : decode limits fields running frame = .error (.record (.decode (.field index cause)))) :
    ∃ metadata,
      MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
        limits.mixed.totalDataBuffers fields (metadataBytes frame.metadata) = .ok metadata ∧
      running.ordinal < limits.mixed.observation.ipc.batches ∧
      running.dataBuffers + metadata.counts.sum ≤ limits.totalDataBuffers ∧
      Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) = .ok () ∧
      metadata.bodyLength = frame.body.len ∧
      MixedFlat.readParsed limits.mixed fields metadata (metadataBytes frame.body) = .error (.field index cause) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.decode_field_checked failed

/-- Even if a later typed check rejects the record, a completed framing step
identifies the original record start and complete wire windows. -/
theorem completed_frame_at {size packed : Nat} {cursor : Cursor} {chunk rest : KBytes}
    {frame : Frame} {next : Arrow.Framing.Incremental.State}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (fed : Arrow.Framing.Incremental.feed cursor.limits.mixed.observation.ipc cursor.input chunk =
      .ok (.frame frame next rest)) :
    frame.offset = cursor.messageOffset ∧
      frame.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed) ∧ frame.body.wf = true :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.completed_frame_at held incoming fed

/-- Any ordered, well-formed fragment preserves the original carrier reference
and any publication agrees with the immutable parser at its original offset. -/
theorem feed_refines {size packed : Nat} {cursor : Cursor} {chunk : KBytes} {reply : Progress}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (fed : feed cursor chunk = .ok reply) :
    reply.Refines size packed cursor chunk :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.feed_refines held incoming fed

/-- The published Schema and first record offset agree with the immutable reader
for any ordered fragment cuts from byte zero. -/
theorem open_agrees {size packed : Nat} {fields : List MixedFlat.Field} {limits : Limits}
    {opened : Cursor} (steps : SchemaSteps size packed fields (start limits) opened) :
    SchemaAgreement size packed fields limits opened :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.open_agrees steps

/-- The published batches are the exact immutable pull prefix. This statement
also applies when the next fragment or finalization returns an error. -/
theorem steps_agree {size packed : Nat} {fields : List MixedFlat.Field} {before last : Cursor}
    {batches : List (Delivered fields)} {running : Running}
    (steps : RecordSteps size packed fields before batches last)
    (held : before.input.InCarrier before.limits.mixed.observation.ipc (.leaf size packed))
    (phase : before.phase = .records fields running) :
    RecordAgreement size packed fields before running batches last :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.steps_agree steps held phase

/-- After the final input bytes, successful finish agrees with the immutable
next pull at exact EOS and with the empty eager suffix. -/
theorem finish_agrees {size packed closedAt : Nat} {cursor : Cursor}
    {fields : List MixedFlat.Field} {running : Running}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (phase : cursor.phase = .records fields running) (exhausted : cursor.position = size)
    (finished : finish cursor = .ok closedAt) :
    closedAt = size ∧
      MixedFlat.Stream.Events.readNext cursor.limits.mixed (.leaf size packed) fields
        (cursor.limits.mixed.observation.ipc.batches - running.ordinal) running.ordinal running.rows
        cursor.messageOffset = .ok none ∧
      MixedFlat.Stream.readBatches cursor.limits.mixed (.leaf size packed) fields
        (cursor.limits.mixed.observation.ipc.batches - running.ordinal) running.ordinal running.rows
        cursor.messageOffset = .ok [] :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.finish_agrees held phase exhausted finished

/-- A complete incremental run gives the immutable eager result with the
same fields, original ranges and ordered records. See also `steps_agree`
and `finish_agrees` for the corresponding pull events and termination. -/
theorem complete_agrees {size packed closedAt : Nat} {limits : Limits}
    {fields : List MixedFlat.Field} {opened last : Cursor} {batches : List (Delivered fields)}
    (opening : SchemaSteps size packed fields (start limits) opened)
    (records : RecordSteps size packed fields opened batches last)
    (exhausted : last.position = size) (finished : finish last = .ok closedAt) :
    closedAt = size ∧ MixedFlat.Stream.read limits.mixed (.leaf size packed) =
      .ok ⟨fields, batches.map Delivered.record⟩ :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.complete_agrees opening records exhausted finished

/-- A successful finish gives the exact trace of the immutable pull reader,
including the Schema, event boundaries, and EOS. -/
theorem complete_pull_agrees {size packed closedAt : Nat} {limits : Limits}
    {fields : List MixedFlat.Field} {opened last : Cursor} {batches : List (Delivered fields)}
    (opening : SchemaSteps size packed fields (start limits) opened)
    (records : RecordSteps size packed fields opened batches last)
    (exhausted : last.position = size) (finished : finish last = .ok closedAt) :
    MixedFlat.Stream.Events.readAll limits.mixed (.leaf size packed) =
      .ok ⟨MixedFlat.Events.schema fields, ⟨batches.map Delivered.event, .eos⟩⟩ :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.complete_pull_agrees opening records exhausted finished

/-- A failing fragment retains the first framing cause or the typed record
cause at the current original message and ordinal. -/
theorem feed_late_failure {cursor : Cursor} {fields : List MixedFlat.Field} {running : Running}
    {chunk : KBytes} {cause : Error}
    (phase : cursor.phase = .records fields running) (failed : feed cursor chunk = .error cause) :
    let ipc := cursor.limits.mixed.observation.ipc
    (∃ framing, cause = .framing (some running.ordinal) framing ∧
      Arrow.Framing.Incremental.feed ipc cursor.input chunk = .error framing) ∨
    (∃ frame next rest typed, cause = .batch running.ordinal cursor.messageOffset typed ∧
      Arrow.Framing.Incremental.feed ipc cursor.input chunk = .ok (.frame frame next rest) ∧
      decode cursor.limits fields running frame = .error typed) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.feed_late_failure phase failed

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental
