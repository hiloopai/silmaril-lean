module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.Correctness

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts

open Silmaril.Formats Silmaril.Formats.Relational.NamedTable

/-- Exact cuts produce the requested lengths and recover the original slots. -/
theorem split_exact {α : Type} (cuts : List Nat) (slots : List α)
    (extent : cuts.sum = slots.length) :
    (splitSlots cuts slots).flatten = slots ∧ (splitSlots cuts slots).map List.length = cuts :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.split_exact
    cuts slots extent

/-- Each checked column policy obeys its page cap and covers every row exactly. -/
theorem validateColumn_checked {maximum ordinal : Nat} {column : Int32ByteArrayGroup.Selection}
    {rows : Nat} {cuts : List Nat} (checked : validateColumn maximum ordinal column rows cuts = .ok ()) :
    cuts.length ≤ maximum ∧ MixedV1Writer.MultiPage.ValidCuts cuts ∧ cuts.sum = rows :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.validateColumn_checked
    checked

/-- The typed page lists retain both original columns under independent cuts. -/
theorem cutGroup_exact {maximum ordinal : Nat} {cuts : BatchCuts}
    {group : MixedV1Writer.Multi.Group} {output : MixedV1Writer.MultiPage.Group}
    (cut : cutGroup maximum ordinal cuts group = .ok output) :
    groupCuts output = cuts ∧ output.intSlots = group.integers.slots ∧ output.byteSlots = group.octets.slots :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.cutGroup_exact
    cut

/-- The plan has exact field declarations, page cuts and paired nullable slots in batch order. -/
theorem prepare_exact {limits : MixedV1Writer.MultiPage.Limits} {policy : Policy} {observed : MixedIpc.Prepared}
    {plan : MixedV1Writer.MultiPage.Input} (ready : prepare limits policy observed = .ok plan) :
    plan.intField = field observed.descriptor.integer ∧ plan.byteField = field observed.descriptor.binary ∧
    plan.groups.map groupCuts = policy ∧
    plan.groups.map MixedV1Writer.MultiPage.Group.rows = observed.batches.map (List.map toRow) :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.prepare_exact
    ready

/-- Returning grouped bytes requires a successful cut plan and checked emission. -/
theorem convert_groups_checked {source : MixedIpc.Limits} {limits : MixedV1Writer.MultiPage.Limits}
    {policy : Policy} {input : KBytes} {bytes : Bytes} {observed : MixedIpc.Prepared}
    (read : MixedIpc.read source input = .ok observed) (nonempty : observed.batches ≠ [])
    (written : convert source limits policy input = .ok bytes) :
    ∃ plan output, prepare limits policy observed = .ok plan ∧
      MixedV1Writer.MultiPage.emit (physicalOrder observed.descriptor) limits plan = .ok output ∧
      output.bytes = bytes :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.convert_groups_checked read nonempty written

/-- Both physical orders and every admitted policy retain exact native IPC
observations through EOS. Reopening uses the declared footer and group
policies. The reverse IPC and carrier limits apply separately. -/
theorem read_roundTrip {source returned : MixedIpc.Limits} {limits : MixedV1Writer.MultiPage.Limits}
    {policy : Policy} {reverse : Int32ByteArrayGroup.File.Limits} {input output : KBytes}
    {bytes : Bytes} {observed : MixedIpc.Prepared}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convert source limits policy input = .ok bytes)
    (groupLimits : reverse.group = limits.file.writer.readback)
    (footerLimits : reverse.group.snapshot.footer = limits.file.writer.footer)
    (backward : Int32ByteArrayGroup.ToIpc.convertOrdered reverse returned.mixed bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.read_roundTrip
    original forward groupLimits footerLimits backward carrier

/-- Native IPC failure takes priority over all cut, planning and writer checks. -/
theorem convert_source_error {source : MixedIpc.Limits} {limits : MixedV1Writer.MultiPage.Limits}
    {policy : Policy} {input : KBytes} {cause : MixedIpc.Error}
    (failed : MixedIpc.read source input = .error cause) :
    convert source limits policy input = .error (.source cause) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

/-- A true schema-only stream with an empty policy uses the existing footer-only writer. -/
theorem convert_schemaOnly {source : MixedIpc.Limits} {limits : MixedV1Writer.MultiPage.Limits}
    {input : KBytes} {descriptor : MixedIpc.Descriptor}
    (read : MixedIpc.read source input = .ok ⟨descriptor, []⟩) :
    convert source limits [] input =
      ((SchemaOnly.emit limits.file descriptor).mapError Error.schemaOnly).map (·.bytes) := by
  simp [convert, read, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts
