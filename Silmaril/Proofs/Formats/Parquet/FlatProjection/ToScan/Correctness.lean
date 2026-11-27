module

public import Silmaril.Formats.Parquet.FlatProjection.ToScan.Defs
import all Silmaril.Formats.Parquet.FlatProjection.Defs
import Silmaril.Formats.Parquet.FlatProjection.Thms
import Silmaril.Formats.Parquet.FlatProjection.Composition.Thms
import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Thms
import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.Thms
import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatProjection.ToScan

open Silmaril.Relational
open Silmaril.Formats Silmaril.Formats.Parquet FlatProjection FlatProjection.ToScan
open FlatProjection.Composition FlatProjection.Composition.Ipc
open Arrow.MixedFlat

private theorem slots_length (column : OrderedWriter.Column) :
    (observeSlots column.observe).length = column.length := by
  cases column <;> simp [observeSlots, OrderedWriter.Column.observe, OrderedWriter.Column.length,
    Arrow.Writer.ColumnValues.observe]

private theorem right_of_forall₂ {α β : Type} {related : α → β → Prop} {xs : List α}
    {ys : List β} {property : β → Prop} (all : List.Forall₂ related xs ys)
    (step : ∀ a b, related a b → property b) :
    ∀ y ∈ ys, property y := by
  induction all with
  | nil => simp
  | cons head _ ih =>
    intro column member
    rcases List.mem_cons.mp member with rfl | later
    · exact step _ _ head
    · exact ih column later

private theorem observeGroup_aligned {parquet : FlatProjection.Limits} {checked : Checked}
    {index : Nat} {batch : OrderedWriter.BatchInput}
    (read : checked.readGroup parquet index = .ok batch) :
    Rows.BatchAligned checked.fields.length (observeGroup batch) := by
  obtain ⟨_, _, _, fields, columns⟩ := group_exact read
  refine ⟨?_, ?_⟩
  · simpa [observeGroup, OrderedWriter.BatchInput.fields] using congrArg List.length fields
  · intro slots member
    obtain ⟨column, found, rfl⟩ := List.mem_map.mp member
    rw [Function.comp_apply, slots_length]
    exact right_of_forall₂ columns (fun _ _ relation => relation.2) column found

theorem observeGroups_aligned {parquet : FlatProjection.Limits} {checked : Checked}
    {batches : List OrderedWriter.BatchInput} (read : checked.readAll parquet = .ok batches) :
    Rows.Aligned (observeGroups checked batches) := by
  intro observation member
  obtain ⟨batch, found, rfl⟩ := List.mem_map.mp member
  exact right_of_forall₂ (readAll_indexed read)
    (fun _ _ step => observeGroup_aligned step) batch found

theorem observeGroups_exact (checked : Checked) (batches : List OrderedWriter.BatchInput) :
    observeSource (observe checked batches) = some (observeGroups checked batches) := by
  have mapped : (batches.map OrderedWriter.BatchInput.observe).mapM observeSourceBatch =
      some (batches.map observeGroup) := by
    induction batches with
    | nil => rfl
    | cons batch rest ih =>
      simp [List.mapM_cons, observeSourceBatch, OrderedWriter.BatchInput.observe, observeGroup,
        ih, Bind.bind, Option.bind, pure, List.map_map, Function.comp_def]
  simp [observeSource, observe, mapped, observeGroups]

theorem emitted_events {ipc : Arrow.MixedFlat.Limits} {checked : Checked}
    {batches : List OrderedWriter.BatchInput} {wire : KBytes}
    (emitted : OrderedWriter.emit ipc checked.fields batches = .ok wire) :
    readEvents ipc wire = some (observeGroups checked batches) :=
  (read_emitted emitted).1.trans (observeGroups_exact checked batches)

theorem convert_rows {parquet : FlatProjection.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
    {ordinals : List Nat} {wire : KBytes} (written : convert parquet ipc input ordinals = .ok wire) :
    ∃ (checked : Checked) (batches : List OrderedWriter.BatchInput)
        (read : checked.readAll parquet = .ok batches),
      openFile parquet input ordinals = .ok checked ∧ checked.columns.map Bound.ordinal = ordinals ∧
      List.Forall₂ (fun index batch => checked.readGroup parquet index = .ok batch) checked.indices batches ∧
      readEvents ipc wire = some (observeGroups checked batches) ∧
      Rows.readRows ipc wire = some (Rows.materialize (observeGroups checked batches) (observeGroups_aligned read)) := by
  obtain ⟨checked, batches, opened, read, emitted⟩ := convert_ok_iff.mp written
  have events := emitted_events emitted
  exact ⟨checked, batches, read, opened, (open_exact opened).2.1, readAll_indexed read, events,
    Rows.readRows_exact events⟩

theorem convert_compose_rows {wideLimits directLimits : FlatProjection.Limits}
    {wideIpc directIpc : Arrow.MixedFlat.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {wideWire directWire : KBytes}
    (same : SameColumnPolicy wideLimits directLimits)
    (composedOk : composeOrdinals ordinals positions = some composed)
    (wideWritten : convert wideLimits wideIpc input ordinals = .ok wideWire)
    (directWritten : convert directLimits directIpc input composed = .ok directWire) :
    ∃ (wide : Rows.Table) (projection : Scan.Projection wide.schema),
      Rows.readRows wideIpc wideWire = some wide ∧
      wide.schema.width = ordinals.length ∧ Rows.positions projection = positions ∧
      Rows.readRows directIpc directWire = some ⟨projection.schema, projection.project wide.rows⟩ := by
  obtain ⟨original, wide, wideRead, wideOpen, width, _, _, wideTableRead⟩ := convert_rows wideWritten
  obtain ⟨direct, narrow, directRead, directOpen, _, _, _, directTableRead⟩ := convert_rows directWritten
  obtain ⟨selected, selectedRead, projected⟩ :=
    project_compose_success same composedOk wideOpen directOpen wideRead
  have sameBatches : selected = narrow := Except.ok.inj (selectedRead.symm.trans directRead)
  subst selected
  obtain ⟨originalEvents, directEvents, originalNorm, directNorm, eventProjection⟩ := project_source projected
  rw [observeGroups_exact] at originalNorm directNorm
  cases originalNorm
  cases directNorm
  let originalObservation := observeGroups original wide
  let aligned := observeGroups_aligned wideRead
  let wideTable := Rows.materialize originalObservation aligned
  have widthAligned : originalObservation.AlignedWidth := fun b hb => (aligned b hb).1
  have valid : ∀ index ∈ positions, index < originalObservation.fields.length := by
    intro index member
    by_contra! outside
    have refused := (projectEvents_none_iff widthAligned).mpr ⟨index, member, outside⟩
    rw [eventProjection] at refused
    contradiction
  let projection : Scan.Projection (Rows.schema originalObservation.fields) :=
    ⟨positions.length, fun i => ⟨positions[i], valid _ (List.getElem_mem _)⟩⟩
  have positionsExact : Rows.positions projection = positions := List.ofFn_getElem
  obtain ⟨output, _, outputRead, materialized⟩ := Rows.materialize_project originalObservation aligned projection
  rw [positionsExact] at outputRead
  have sameOutput : output = observeGroups direct narrow := Option.some.inj (outputRead.symm.trans eventProjection)
  subst output
  refine ⟨wideTable, projection, wideTableRead, ?_, positionsExact, directTableRead.trans (congrArg some materialized)⟩
  change original.fields.length = ordinals.length
  simpa [Checked.fields] using congrArg List.length width

end Silmaril.Proofs.Formats.Parquet.FlatProjection.ToScan
