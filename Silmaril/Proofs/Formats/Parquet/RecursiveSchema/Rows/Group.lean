module

public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
import Mathlib.Data.List.Forall2

@[expose] public section

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema (Compiled bindChunk)
open Silmaril.Formats.Parquet.RecursiveSchema.Rows
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
    snapshot.groupAt group = some rowGroup ∧ rowGroup.columns.length = schema.leaves.size := by
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
      cases Except.ok.inj admitted
      exact ⟨rfl, Classical.not_not.mp width⟩

theorem evidence_wire {group row : Nat} {columns : List Column} {input : List Evidence}
    (accepted : evidenceAt group row columns = .ok input) :
    List.Forall₂ (fun column (evidence : Evidence) =>
      evidence.column = column.location ∧ column.slots[row]? = some evidence.slot) columns input := by
  refine List.Forall₂.imp ?_ (mapM_ordered accepted)
  intro column item accepted
  cases found : column.slots[row]? <;> simp only [found] at accepted
  · contradiction
  · cases Except.ok.inj accepted
    exact ⟨rfl, rfl⟩

theorem readColumn_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Formats.Parquet.RecursiveSchema.Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {group column : Nat} {result : Column} (accepted : readColumn limits schema group column = .ok result) :
    ColumnWire limits schema group column result := by
  unfold readColumn at accepted
  obtain ⟨binding, bound, accepted⟩ := bind_ok accepted
  obtain ⟨output, read, packaged⟩ := bind_ok accepted
  have decoded := unmap_error read
  cases Except.ok.inj packaged
  exact ⟨binding, output, unmap_error bound, decoded,
    Formats.Parquet.RecursiveSchema.Chunk.read_wire decoded, rfl, rfl⟩

private theorem readAt_wire {depth group row : Nat} {fields : List Formats.Parquet.RecursiveSchema.Field}
    {columns : List Column} {output : Row} (accepted : readAt depth group row fields columns = .ok output) :
    RowWire group row fields columns output := by
  unfold readAt at accepted
  obtain ⟨input, fromColumns, accepted⟩ := bind_ok accepted
  obtain ⟨assembled, _, packaged⟩ := bind_ok accepted
  cases Except.ok.inj packaged
  exact ⟨input, fromColumns, assembled.projection, assembled.fits⟩

private theorem witness_of_mem {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (paired : List.Forall₂ relation left right)
    {item : β} (member : item ∈ right) : ∃ source, relation source item := by
  induction paired with
  | nil => simp at member
  | cons head _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨_, head⟩
    · exact ih tail

theorem readGroup_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {group : Nat}
    {output : Observation} (accepted : readGroup limits schema group = .ok output) :
    GroupWire limits schema group output := by
  unfold readGroup at accepted
  obtain ⟨rowGroup, declared, accepted⟩ := bind_ok accepted
  obtain ⟨columns, decoded, accepted⟩ := bind_ok accepted
  obtain ⟨rows, assembled, packaged⟩ := bind_ok accepted
  cases Except.ok.inj packaged
  obtain ⟨groupAt, width⟩ := admitGroup_wire declared
  have columnWire : List.Forall₂ (ColumnWire limits.chunk schema group)
      (List.range schema.leaves.size) columns :=
    List.Forall₂.imp (fun _ _ => readColumn_wire) (mapM_ordered decoded)
  have rowWire : List.Forall₂ (fun row result => RowWire group row schema.fields columns result)
      (List.range rowGroup.numRows.toNat) rows :=
    List.Forall₂.imp (fun _ _ => readAt_wire) (mapM_ordered assembled)
  refine ⟨⟨rowGroup, columns, groupAt, width, rfl, columnWire, rowWire⟩, ?_, ?_⟩
  · simpa only [List.length_range] using rowWire.length_eq.symm
  · intro row member
    obtain ⟨_, _, _, _, fits⟩ := witness_of_mem rowWire member
    exact fits

theorem readAll_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {output : List Observation}
    (accepted : readAll limits schema = .ok output) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) output :=
  List.Forall₂.imp (fun _ _ => readGroup_wire) (mapM_ordered accepted)

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows
