module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Defs
import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Thms
import Silmaril.Formats.Parquet.FlatProjection.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp
open Arrow.MixedFlat.Timestamp (Stream Batch)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem placeColumns_exact (offset : Nat) (columns : List ColumnPlan) :
    (placeColumns offset columns).1 = offset + (columns.map (·.page.size)).sum ∧
      List.Forall₂ (fun column index => index.physical = column.index.physical ∧
        index.column.name = column.index.column.name ∧ index.column.optional = column.index.column.optional ∧
        index.column.size = column.page.size) columns (placeColumns offset columns).2 := by
  induction columns generalizing offset with
  | nil => simp [placeColumns]
  | cons column rest ih =>
    have tail := ih (offset + column.page.size)
    refine ⟨?_, .cons ⟨rfl, rfl, rfl, ?_⟩ tail.2⟩
    · simp [placeColumns, tail.1, Nat.add_assoc]
    · simp [FlatInt32Writer.Compact.ColumnIndex.size]

theorem preflight_wire {limits : Limits} {source : Stream} {plan : Plan}
    (prepared : preflight limits source = .ok plan) :
    ∃ leaves indices,
      checkBudget limits source = .ok () ∧
      bindFields limits.primitiveFile.snapshot.footer.compact.maxBinaryBytes source.fields.zipIdx [] = .ok leaves ∧
      (source.batches.zipIdx.mapM fun (batch, group) => planGroup limits leaves batch group) = .ok plan.groups ∧
      placeGroups 4 plan.groups = (plan.dataStop, indices) ∧
      FlatInt32Writer.Compact.encodeGroupsTyped (footerLimit limits plan.dataStop)
        (leaves.map LeafPlan.write) indices = .ok plan.footer ∧
      plan.dataStop + plan.footer.length + 8 ≤ fileLimit limits := by
  unfold preflight at prepared
  obtain ⟨_, admitted, prepared⟩ := bind_ok prepared
  obtain ⟨leaves, bound, prepared⟩ := bind_ok prepared
  obtain ⟨groups, pages, prepared⟩ := bind_ok prepared
  cases placed : placeGroups 4 groups with
  | mk dataStop indices =>
    by_cases dataFits : dataStop + 8 ≤ fileLimit limits
    · simp only [placed, Nat.not_lt.mpr dataFits, ↓reduceIte] at prepared
      obtain ⟨footer, encoded, prepared⟩ := bind_ok prepared
      split at prepared
      · contradiction
      · rename_i footerFits
        cases Except.ok.inj prepared
        have cap := Nat.le_of_not_gt footerFits
        unfold footerLimit at cap
        have bounded := le_trans cap (Nat.min_le_right ..)
        refine ⟨leaves, indices, by simpa using admitted, bound, pages, placed, mapError_ok encoded, ?_⟩
        change dataStop + footer.length + 8 ≤ fileLimit limits
        omega
    · simp [placed, Nat.lt_of_not_ge dataFits] at prepared

private theorem serialize_wire {limits : Limits} {source : Stream} {wire : Bytes}
    (written : serialize limits source = .ok wire) :
    ∃ plan groups, preflight limits source = .ok plan ∧
      (plan.groups.zipIdx.mapM fun (group, ordinal) => emitGroup limits group ordinal) = .ok groups ∧
      4 + (groups.flatten.map Bytes.length).sum = plan.dataStop ∧ wire = assemble plan groups := by
  unfold serialize at written
  obtain ⟨plan, prepared, written⟩ := bind_ok written
  obtain ⟨groups, encoded, written⟩ := bind_ok written
  split at written
  · contradiction
  · rename_i extent
    exact ⟨plan, groups, prepared, encoded, Classical.not_not.mp extent, (Except.ok.inj written).symm⟩

private theorem certify_readback {limits : Limits} {source : Stream} {wire : Bytes}
    (checked : certify limits source wire = .ok ()) :
    ∃ projection : FlatProjection.Events.Checked,
      FlatProjection.Events.openFile limits.readback wire (ordinals source) = .ok projection ∧
      FooterMatches projection source ∧ (projection.trace limits.readback).termination = .eos ∧
      FlatProjection.Events.ToIpc.observation (projection.trace limits.readback) = source := by
  unfold certify at checked
  obtain ⟨projection, opened, checked⟩ := bind_ok checked
  cases eos : (projection.trace limits.readback).termination with
  | readError _ | closeError _ | closed => simp [eos] at checked
  | eos =>
    by_cases matching : FooterMatches projection source ∧
        FlatProjection.Events.ToIpc.observation (projection.trace limits.readback) = source
    · exact ⟨projection, mapError_ok opened, matching.1, eos, matching.2⟩
    · simp [eos, matching] at checked

private theorem emit_checked {limits : Limits} {source : Stream} {wire : Bytes}
    (written : emit limits source = .ok wire) :
    serialize limits source = .ok wire ∧ certify limits source wire = .ok () := by
  unfold emit at written
  obtain ⟨output, serialized, written⟩ := bind_ok written
  obtain ⟨_, certified, written⟩ := bind_ok written
  cases Except.ok.inj written
  exact ⟨serialized, certified⟩

theorem emit_wire {limits : Limits} {source : Stream} {wire : Bytes}
    (written : emit limits source = .ok wire) :
    ∃ plan groups, preflight limits source = .ok plan ∧
      (plan.groups.zipIdx.mapM fun (group, ordinal) => emitGroup limits group ordinal) = .ok groups ∧
      4 + (groups.flatten.map Bytes.length).sum = plan.dataStop ∧ wire = assemble plan groups :=
  serialize_wire (emit_checked written).1

theorem emit_readback {limits : Limits} {source : Stream} {wire : Bytes}
    (written : emit limits source = .ok wire) :
    ∃ projection : FlatProjection.Events.Checked, FooterMatches projection source ∧
      FlatProjection.Events.readAll limits.readback wire (ordinals source) =
        .ok ⟨projection.schema, projection.trace limits.readback⟩ ∧
      (projection.trace limits.readback).termination = .eos ∧
      FlatProjection.Events.ToIpc.observation (projection.trace limits.readback) = source := by
  obtain ⟨projection, opened, footer, eos, same⟩ := certify_readback (emit_checked written).2
  exact ⟨projection, footer, FlatProjection.Events.readAll_opened opened, eos, same⟩

theorem convert_readback {ipc : Arrow.ObservationLimits} {limits : Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ (source : Stream) (projection : FlatProjection.Events.Checked) (start : Nat),
      Arrow.MixedFlat.Timestamp.read ipc input = .ok source ∧
      Arrow.MixedFlat.Timestamp.readSchema ipc.ipc input = .ok (source.fields, start) ∧
      Arrow.MixedFlat.Timestamp.BatchesWire ipc input source.fields ipc.ipc.batches 0 start source.batches ∧
      FooterMatches projection source ∧
      FlatProjection.Events.readAll limits.readback wire (ordinals source) =
        .ok ⟨projection.schema, projection.trace limits.readback⟩ ∧
      (projection.trace limits.readback).termination = .eos ∧
      FlatProjection.Events.ToIpc.observation (projection.trace limits.readback) = source := by
  unfold convert at written
  split at written
  · contradiction
  · obtain ⟨source, accepted, emitted⟩ := bind_ok written
    have read := mapError_ok accepted
    obtain ⟨start, schema, frames⟩ := Arrow.MixedFlat.Timestamp.read_wire read
    obtain ⟨projection, footer, observed, eos, same⟩ := emit_readback emitted
    exact ⟨source, projection, start, read, schema, frames, footer, observed, eos, same⟩

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp
