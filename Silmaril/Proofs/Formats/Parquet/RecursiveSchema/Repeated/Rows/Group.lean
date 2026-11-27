module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Partition
import Mathlib.Data.List.Forall2

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Compiled Field)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Row Observation)

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {result : β}
    (read : (first >>= next) = .ok result) : ∃ x, first = .ok x ∧ next x = .ok result := by
  cases first with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem unmap_error {α ε δ : Type} {source : Except ε α} {wrap : ε → δ} {result : α}
    (read : source.mapError wrap = .ok result) : source = .ok result := by
  cases source with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

private theorem mapM_ordered {α β ε : Type} {decode : α → Except ε β}
    {input : List α} {output : List β} (accepted : input.mapM decode = .ok output) :
    List.Forall₂ (fun item value => decode item = .ok value) input output := by
  induction input generalizing output with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst output
    exact .nil
  | cons item rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, decoded, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases Except.ok.inj accepted
    exact .cons decoded (ih remaining)

private theorem admitGroup_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {group : Nat} {rowGroup : Footer.RowGroup}
    (admitted : admitGroup limits schema group = .ok rowGroup) :
    snapshot.groupAt group = some rowGroup ∧ rowGroup.columns.length = schema.leaves.size ∧
      slotTotal rowGroup ≤ limits.maxSlots := by
  cases found : snapshot.groupAt group with
  | none => simp [admitGroup, found] at admitted
  | some original =>
    simp only [admitGroup, found] at admitted
    split at admitted
    · contradiction
    · rename_i width
      split at admitted <;> try contradiction
      split at admitted <;> try contradiction
      split at admitted <;> try contradiction
      rename_i slots
      cases Except.ok.inj admitted
      exact ⟨rfl, Classical.not_not.mp width, Nat.le_of_not_gt slots⟩

public theorem readColumn_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Formats.Parquet.RecursiveSchema.Repeated.Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {group column : Nat} {result : Column}
    (accepted : readColumn limits schema group column = .ok result) :
    ColumnWire limits schema group column result := by
  unfold readColumn at accepted
  obtain ⟨binding, bound, accepted⟩ := bind_ok accepted
  obtain ⟨observed, read, accepted⟩ := bind_ok accepted
  obtain ⟨rows, partitioned, packaged⟩ := bind_ok accepted
  have decoded := unmap_error read
  split at packaged
  · rename_i counts
    cases Except.ok.inj packaged
    exact ⟨binding, observed, rows, unmap_error bound, decoded,
      Formats.Parquet.RecursiveSchema.Repeated.Chunk.read_wire decoded, rfl, partition_wire partitioned, counts, rfl⟩
  · contradiction

private theorem addressed_atoms (address : Formats.Parquet.RecursiveSchema.Repeated.Chunk.Address)
    (observed : Formats.Parquet.RecursiveSchema.Repeated.Chunk.Observation) :
    (addressed address observed).map Addressed.atom =
      observed.pages.flatMap (fun page =>
        (page.decoded.levels.zip page.decoded.words).map (fun (levels, word) => ⟨levels, word⟩)) := by
  unfold addressed
  rw [List.map_flatMap]
  apply congrArg (fun visit => observed.pages.flatMap visit)
  funext page
  rw [List.map_map]
  change ((page.decoded.levels.zip page.decoded.words).zipIdx page.start.state.slot).map
    ((fun (levels, word) => Atom.mk levels word) ∘ Prod.fst) = _
  rw [← List.map_map, List.zipIdx_map_fst]

public theorem original_atoms {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Formats.Parquet.RecursiveSchema.Repeated.Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {group column : Nat} {result : Column} (wire : ColumnWire limits schema group column result) :
    ∃ (binding : Formats.Parquet.RecursiveSchema.Repeated.Chunk.Binding schema group column)
      (observed : Formats.Parquet.RecursiveSchema.Repeated.Chunk.Observation),
      Formats.Parquet.RecursiveSchema.Repeated.Chunk.Wire limits binding observed ∧
      (result.rows.toList.flatMap (·.toList)).map Addressed.atom =
        observed.pages.flatMap (fun page =>
          (page.decoded.levels.zip page.decoded.words).map (fun (levels, word) => ⟨levels, word⟩)) := by
  obtain ⟨binding, observed, rows, _, _, source, _, partition, _, output⟩ := wire
  refine ⟨binding, observed, source, ?_⟩
  rw [output]
  simp only [List.flatMap_map, List.flatMap_id']
  rw [partition.exact, addressed_atoms]

public theorem readAt_wire {depth group row : Nat} {fields : List Field}
    {columns : List Column} {output : Row} (accepted : readAt depth group row fields columns = .ok output) :
    RowWire depth ⟨group, row, none⟩ fields columns output := by
  unfold readAt at accepted
  obtain ⟨input, fromColumns, accepted⟩ := bind_ok accepted
  obtain ⟨assembled, _, packaged⟩ := bind_ok accepted
  cases Except.ok.inj packaged
  exact ⟨input, mapM_ordered fromColumns, assembled.typed, assembled.projection⟩

private theorem witness_of_mem {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (paired : List.Forall₂ relation left right)
    {item : β} (member : item ∈ right) : ∃ source, relation source item := by
  induction paired with
  | nil => simp at member
  | cons head _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨_, head⟩
    · exact ih tail

public theorem readGroup_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {group : Nat} {output : Observation}
    (accepted : readGroup limits schema group = .ok output) : GroupWire limits schema group output := by
  unfold readGroup at accepted
  obtain ⟨rowGroup, declared, accepted⟩ := bind_ok accepted
  obtain ⟨columns, decoded, accepted⟩ := bind_ok accepted
  obtain ⟨rows, assembled, packaged⟩ := bind_ok accepted
  cases Except.ok.inj packaged
  obtain ⟨groupAt, width, slots⟩ := admitGroup_wire declared
  have columnWire : List.Forall₂ (ColumnWire limits.chunk schema group)
      (List.range schema.leaves.size) columns :=
    List.Forall₂.imp (fun _ _ => readColumn_wire) (mapM_ordered decoded)
  have rowWire : List.Forall₂ (fun row result =>
      RowWire (schemaLimits.maxSchemaDepth - 1) ⟨group, row, none⟩ schema.fields columns result)
      (List.range rowGroup.numRows.toNat) rows :=
    List.Forall₂.imp (fun _ _ => readAt_wire) (mapM_ordered assembled)
  refine ⟨⟨rowGroup, columns, groupAt, width, slots, rfl, columnWire, rowWire⟩, ?_, ?_⟩
  · simpa only [List.length_range] using rowWire.length_eq.symm
  · intro row member
    obtain ⟨_, _, _, typed, _⟩ := witness_of_mem rowWire member
    exact typed

public theorem readAll_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {output : List Observation}
    (accepted : readAll limits schema = .ok output) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) output :=
  List.Forall₂.imp (fun _ _ => readGroup_wire) (mapM_ordered accepted)

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows
