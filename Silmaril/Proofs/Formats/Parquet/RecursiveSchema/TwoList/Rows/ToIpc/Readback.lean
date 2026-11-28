module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer (emit emit_readback Readback)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error => contradiction
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {value : α}
    (accepted : first.mapError wrap = .ok value) : first = .ok value := by
  cases first with
  | error => simp [Except.mapError] at accepted
  | ok => simpa only [Except.mapError, Except.ok.injEq] using accepted

private theorem readGroups_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {ordinals : List Nat} {groups : List Observation}
    (accepted : readGroups limits schema ordinals = .ok groups) :
    List.Forall₂ (Rows.GroupWire limits schema) ordinals groups := by
  induction ordinals generalizing groups with
  | nil =>
    cases Except.ok.inj accepted
    exact .nil
  | cons ordinal rest ih =>
    simp only [readGroups, List.mapM_cons] at accepted
    obtain ⟨batch, first, accepted⟩ := bind_ok accepted
    obtain ⟨remaining, tail, packaged⟩ := bind_ok accepted
    cases Except.ok.inj packaged
    exact .cons (Rows.readGroup_wire (from_mapError first)) (ih tail)

public theorem convertSource_readback {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {schema : Compiled schemaLimits snapshot} {selection : Rows.Events.Selection} {bytes : KBytes}
    (written : convertSource limits ipc schema selection = .ok bytes) :
    ∃ groups, readGroups limits schema (List.range snapshot.groupCount) = .ok groups ∧
      List.Forall₂ (Rows.GroupWire limits schema) (List.range snapshot.groupCount) groups ∧
      Readback ipc (selectSchema selection (Rows.arrowSchema schema.plan))
        (groups.map (selectBatch selection)) bytes := by
  unfold convertSource at written
  obtain ⟨groups, first, emission⟩ := bind_ok written
  exact ⟨groups, from_mapError first, readGroups_wire (from_mapError first),
    emit_readback (from_mapError emission)⟩

public theorem convert_readback {schemaLimits : Snapshot.Limits}
    {limits : Chunk.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : Rows.Events.Selection} {bytes : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok bytes) :
    ∃ opened groups, RecursiveSchema.TwoList.openFile schemaLimits input = .ok opened ∧
      readGroups limits opened.schema (List.range opened.snapshot.groupCount) = .ok groups ∧
      List.Forall₂ (Rows.GroupWire limits opened.schema) (List.range opened.snapshot.groupCount) groups ∧
      Readback ipc (selectSchema selection (Rows.arrowSchema opened.schema.plan))
        (groups.map (selectBatch selection)) bytes := by
  unfold convert at written
  obtain ⟨opened, first, rest⟩ := bind_ok written
  obtain ⟨groups, read, wire, native⟩ := convertSource_readback rest
  exact ⟨opened, groups, from_mapError first, read, wire, native⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc
