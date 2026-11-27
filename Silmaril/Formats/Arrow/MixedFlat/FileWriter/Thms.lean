module

public import Silmaril.Formats.Arrow.MixedFlat.FileWriter.Defs
public import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Formats.Arrow.MixedFlat.FileWriter

public section

namespace Silmaril.Formats.Arrow.MixedFlat.FileWriter

open OrderedWriter (BatchInput)

/-- Recover the exact checked footer, schema extent and ordered record observations. -/
theorem emit_index_exact {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ (plan : Assembly) (index : MixedFlat.File.Index wire) (observed : List MixedFlat.Observed),
      assemble limits fields batches = .ok plan ∧ plan.bytes = wire ∧
      MixedFlat.File.readIndex limits.observation.ipc wire = .ok index ∧
      index.footer = plan.footer ∧ index.footer.fields = fields ∧
      16 + index.schemaSize = plan.schemaEnd ∧
      index.span.start = plan.footerStart ∧ index.span.length = plan.footerLength ∧
      plan.footerStart + plan.footerLength + 10 = wire.len ∧
      index.footer.blocks.length = batches.length ∧
      index.footer.blocks.mapM (MixedFlat.File.readRecord limits wire index.footer.fields) = .ok observed ∧
      observed.map observe = batches.map BatchInput.observe :=
  Proofs.Formats.Arrow.MixedFlat.FileWriter.emit_index_exact written

/-- A block starts after the embedded Schema and every preceding original record span. -/
theorem emit_block_offset {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire)
    {index : MixedFlat.File.Index wire}
    (checked : MixedFlat.File.readIndex limits.observation.ipc wire = .ok index)
    {n : Nat} {block : FileBlock} (found : index.footer.blocks[n]? = some block) :
    ∃ plan, assemble limits fields batches = .ok plan ∧
      block.offset = plan.schemaEnd +
        ((index.footer.blocks.take n).map (fun item => item.metadataLength + item.bodyLength)).sum :=
  Proofs.Formats.Arrow.MixedFlat.FileWriter.emit_block_offset written checked found

/-- Indexed reads agree with emitted batch order and preserve absence beyond the index. -/
theorem emit_readAt {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ (index : MixedFlat.File.Index wire) (observed : List MixedFlat.Observed),
      MixedFlat.File.readIndex limits.observation.ipc wire = .ok index ∧
      index.footer.fields = fields ∧ observed.map observe = batches.map BatchInput.observe ∧
      ∀ n, index.readAt limits n = .ok observed[n]? :=
  Proofs.Formats.Arrow.MixedFlat.FileWriter.emit_readAt written

/-- The native file pull reader reaches EOS with aligned events for every emitted batch. -/
theorem emit_events {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ (index : MixedFlat.File.Index wire) (observed : List MixedFlat.Observed)
      (events : List (MixedFlat.Events.Batch (MixedFlat.Events.schema fields))),
      MixedFlat.File.readIndex limits.observation.ipc wire = .ok index ∧ index.footer.fields = fields ∧
      index.footer.blocks.mapM (MixedFlat.File.readRecord limits wire index.footer.fields) = .ok observed ∧
      observed.map observe = batches.map BatchInput.observe ∧
      List.Forall₂ (MixedFlat.Events.Agrees (MixedFlat.Events.schema fields)) observed events ∧
      MixedFlat.File.Events.Pull.readAll limits wire = .ok ⟨MixedFlat.Events.schema fields, ⟨events, .eos⟩⟩ :=
  Proofs.Formats.Arrow.MixedFlat.FileWriter.emit_events written

/-- The embedded Schema and footer retain the exact declared field kinds,
including plain Utf8, and the original EOS precedes the footer. -/
theorem emit_schema_exact {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ index : MixedFlat.File.Index wire,
      MixedFlat.File.readIndex limits.observation.ipc wire = .ok index ∧ index.footer.fields = fields ∧
      MixedFlat.readSchema limits.observation.ipc index.schemaMetadata = .ok fields ∧
      readEnvelope limits.observation.ipc wire (index.span.start - 8) = .ok .eos :=
  Proofs.Formats.Arrow.MixedFlat.FileWriter.emit_schema_exact written

end Silmaril.Formats.Arrow.MixedFlat.FileWriter
