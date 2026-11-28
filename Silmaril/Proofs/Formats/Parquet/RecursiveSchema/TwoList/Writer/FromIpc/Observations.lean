module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc.Conversion

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc

open Silmaril.Formats
open Parquet.RecursiveSchema.TwoList
open Parquet.RecursiveSchema.TwoList.Writer.FromIpc
open Arrow.RecursiveSchema hiding Limits Error
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)

public theorem agrees_events {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} {parquet : Σ sig : Signature, Rows.Events.Trace sig}
    {ipc : Σ sig : Signature, Stream.Events.Trace sig}
    (written : convert limits input checksum = .ok output)
    (direct : Rows.Events.read limits.parquet.schema.snapshot limits.parquet.chunk output.bytes = .ok parquet)
    (original : Stream.Events.read limits.ipc input = .ok ipc) :
    declarations parquet.1 = declarations ipc.1 ∧
    parquet.2.batches.map eraseBatch = ipc.2.batches.map eraseBatch ∧
    parquet.2.termination = .eos ∧ ipc.2.termination = .eos := by
  obtain ⟨source, checked, _, _, readback⟩ := (convert_readback written).original
  obtain ⟨_, events, _, _, _, _, _, _, read, fields, ending, batches, _, _⟩ := readback.original
  obtain ⟨_, eos, _, _⟩ := checked.eos
  obtain ⟨sourceFields, sourceBatches, sourceEnd⟩ :=
    Stream.Events.read_checked_eos checked.checked eos original
  cases Except.ok.inj (direct.symm.trans read)
  exact ⟨fields.trans sourceFields.symm, batches.trans sourceBatches.symm, ending, sourceEnd⟩

private theorem forwardGroups {schemaLimits : Parquet.Snapshot.Limits} {snapshot : Parquet.Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {ordinals : List Nat}
    {groups : List Arrow.RecursiveSchema.Batch.Rows.Observation}
    (read : ordinals.mapM (Rows.readGroup limits schema) = .ok groups) :
    Rows.ToIpc.readGroups limits schema ordinals = .ok groups := by
  induction ordinals generalizing groups with
  | nil =>
    cases Except.ok.inj read
    rfl
  | cons ordinal rest ih =>
    simp only [List.mapM_cons] at read
    cases first : Rows.readGroup limits schema ordinal with
    | error cause => simp [first, bind, Except.bind] at read
    | ok batch =>
      cases tail : rest.mapM (Rows.readGroup limits schema) with
      | error cause => simp [first, tail, bind, Except.bind] at read
      | ok remaining =>
        simp only [first, tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at read
        subst groups
        rw [Rows.ToIpc.readGroups, List.mapM_cons]
        change ((Rows.readGroup limits schema ordinal).mapError (.group ordinal) >>= fun head =>
          Rows.ToIpc.readGroups limits schema rest >>= fun tail => pure (head :: tail)) = _
        rw [first, ih tail]
        rfl

public theorem round_trip {limits : Limits} {input returned : KBytes} {checksum : Bool}
    {output : Writer.Output} {reverse : Arrow.RecursiveSchema.Batch.Limits}
    (written : convert limits input checksum = .ok output)
    (forward : Rows.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.chunk reverse
      output.bytes .field = .ok returned) :
    ∃ source, SourceWire limits.ipc input source ∧
      Stream.Writer.Readback reverse source.schema (source.batches.map Stream.Completed.observed) returned := by
  obtain ⟨source, original, _, _, readback⟩ := (convert_readback written).original
  obtain ⟨opened, _, reopen, _, _, _, fields, _, _, _, _, _, groups, _⟩ := readback.original
  obtain ⟨sameFile, completed, sameOpen, read, _, certificate⟩ := Rows.ToIpc.convert_readback forward
  cases Except.ok.inj (sameOpen.symm.trans reopen)
  have exactGroups := Except.ok.inj (read.symm.trans (forwardGroups groups))
  subst completed
  refine ⟨source, original, ?_⟩
  simpa only [Rows.ToIpc.selectSchema, fields, show Rows.ToIpc.selectBatch .field = id from rfl,
    List.map_id, writerInput] using certificate

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc
