module

public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered.Defs
import Silmaril.Formats.Parquet.Timestamp.FromIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Thms
import Silmaril.Formats.Arrow.TimestampStream.Ordered.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered

open Silmaril.Formats Parquet Timestamp
open Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered
open Arrow.TimestampStream.Ordered (Stream Batch Field)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem bindFields_exact {nameBytes : Nat} {fields : List (Field × Nat)} {names : List String}
    {leaves : List LeafPlan} (bound : bindFields nameBytes fields names = .ok leaves) :
    List.Forall₂ (fun field leaf => leaf.field = field.1 ∧
      FromIpc.descriptor field.1 = .ok leaf.descriptor ∧
      leaf.descriptor.unit.tickUnit = field.1.metadata.unit ∧
      field.1.metadata.timezone = (if leaf.descriptor.isAdjustedToUTC then some "UTC" else none))
      fields leaves := by
  induction fields generalizing names leaves with
  | nil =>
    simp [bindFields] at bound
    subst leaves
    exact .nil
  | cons item rest ih =>
    obtain ⟨field, position⟩ := item
    simp only [bindFields] at bound
    split at bound
    · contradiction
    · split at bound
      · contradiction
      · obtain ⟨descriptor, chosen, bound⟩ := bind_ok bound
        obtain ⟨tail, later, bound⟩ := bind_ok bound
        cases Except.ok.inj bound
        have exactDescriptor := FromIpc.descriptor_exact (mapError_ok chosen)
        exact .cons ⟨rfl, mapError_ok chosen, exactDescriptor.1, exactDescriptor.2.1⟩ (ih later)

theorem placeColumns_exact (offset : Nat) (columns : List ColumnPlan) :
    (placeColumns offset columns).1 = offset + (columns.map (·.page.size)).sum ∧
      List.Forall₂ (fun column index => index.name = column.index.name ∧
        index.optional = column.index.optional ∧ index.size = column.page.size)
        columns (placeColumns offset columns).2 := by
  induction columns generalizing offset with
  | nil => simp [placeColumns]
  | cons column rest ih =>
    have tail := ih (offset + column.page.size)
    refine ⟨?_, .cons ⟨rfl, rfl, ?_⟩ tail.2⟩
    · simp [placeColumns, tail.1, Nat.add_assoc]
    · simp [FlatInt32Writer.Compact.ColumnIndex.size]

theorem preflight_wire {limits : Limits} {source : Stream} {plan : Plan}
    (prepared : preflight limits source = .ok plan) :
    ∃ leaves indices,
      checkBudget limits source = .ok () ∧
      bindFields limits.writer.snapshot.footer.compact.maxBinaryBytes source.fields.zipIdx [] = .ok leaves ∧
      (source.batches.zipIdx.mapM fun (batch, group) => planGroup limits.writer.leaf leaves batch group) =
        .ok plan.groups ∧
      placeGroups 4 plan.groups = (plan.dataStop, indices) ∧
      FlatInt32Writer.Compact.encodeGroupsWriting 2 (footerLimit limits plan.dataStop)
        (leaves.map fun leaf => FromIpc.Internal.leaf leaf.descriptor leaf.index) indices = .ok plan.footer ∧
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

theorem serialize_wire {limits : Limits} {source : Stream} {wire : Bytes}
    (written : serialize limits source = .ok wire) :
    ∃ plan groups, preflight limits source = .ok plan ∧
      (plan.groups.zipIdx.mapM fun (group, ordinal) => emitGroup group ordinal) = .ok groups ∧
      4 + (groups.flatten.map Bytes.length).sum = plan.dataStop ∧ wire = assemble plan groups := by
  unfold serialize at written
  obtain ⟨plan, prepared, written⟩ := bind_ok written
  obtain ⟨groups, encoded, written⟩ := bind_ok written
  split at written
  · contradiction
  · rename_i extent
    exact ⟨plan, groups, prepared, encoded, Classical.not_not.mp extent, (Except.ok.inj written).symm⟩

theorem certify_readback {limits : Limits} {source : Stream} {wire : Bytes}
    (checked : certify limits source wire = .ok ()) :
    ∃ projection : Leaf.Projection.Checked,
      Leaf.Projection.openFile (readbackLimits limits) wire (ordinals source) = .ok projection ∧
      FooterMatches projection source ∧
      (projection.trace (readbackLimits limits)).termination = .eos ∧
      Leaf.Projection.ToIpc.observation (projection.trace (readbackLimits limits)) = source := by
  unfold certify at checked
  obtain ⟨projection, opened, checked⟩ := bind_ok checked
  cases eos : (projection.trace (readbackLimits limits)).termination with
  | readError _ | closeError _ | closed => simp [eos] at checked
  | eos =>
    by_cases matching : FooterMatches projection source ∧
        Leaf.Projection.ToIpc.observation (projection.trace (readbackLimits limits)) = source
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
      (plan.groups.zipIdx.mapM fun (group, ordinal) => emitGroup group ordinal) = .ok groups ∧
      4 + (groups.flatten.map Bytes.length).sum = plan.dataStop ∧ wire = assemble plan groups :=
  serialize_wire (emit_checked written).1

theorem emit_readback {limits : Limits} {source : Stream} {wire : Bytes}
    (written : emit limits source = .ok wire) :
    ∃ projection : Leaf.Projection.Checked, FooterMatches projection source ∧
      Leaf.Projection.readAll (readbackLimits limits) wire (ordinals source) =
        .ok ⟨projection.schema, projection.trace (readbackLimits limits)⟩ ∧
      (projection.trace (readbackLimits limits)).termination = .eos ∧
      Leaf.Projection.ToIpc.observation (projection.trace (readbackLimits limits)) = source := by
  obtain ⟨projection, opened, footer, eos, same⟩ := certify_readback (emit_checked written).2
  exact ⟨projection, footer, Leaf.Projection.readAll_opened opened, eos, same⟩

theorem convert_source_error {ipc : Arrow.Limits} {limits : Limits} {input : KBytes}
    {cause : Arrow.TimestampStream.Ordered.Error}
    (fits : input.len ≤ limits.writer.maxInputBytes)
    (failed : Arrow.TimestampStream.Ordered.read ipc input = .error cause) :
    convert ipc limits input = .error (.source cause) := by
  simp [convert, Nat.not_lt.mpr fits, failed, Except.mapError, Bind.bind, Except.bind]

theorem convert_readback {ipc : Arrow.Limits} {limits : Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ (source : Stream) (projection : Leaf.Projection.Checked) (start : Nat),
      Arrow.TimestampStream.Ordered.read ipc input = .ok source ∧
      Arrow.TimestampStream.Ordered.readSchema ipc input = .ok (source.fields, start) ∧
      Arrow.TimestampStream.Ordered.BatchesWire ipc input source.fields ipc.batches start source.batches ∧
      FooterMatches projection source ∧
      Leaf.Projection.readAll (readbackLimits limits) wire (ordinals source) =
        .ok ⟨projection.schema, projection.trace (readbackLimits limits)⟩ ∧
      (projection.trace (readbackLimits limits)).termination = .eos ∧
      Leaf.Projection.ToIpc.observation (projection.trace (readbackLimits limits)) = source := by
  unfold convert at written
  split at written
  · contradiction
  · obtain ⟨source, accepted, emitted⟩ := bind_ok written
    have read := mapError_ok accepted
    obtain ⟨_, start, schema, frames⟩ := (Arrow.TimestampStream.Ordered.read_iff _ _ _).mp read
    obtain ⟨projection, footer, observed, eos, same⟩ := emit_readback emitted
    exact ⟨source, projection, start, read, schema, frames, footer, observed, eos, same⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered
