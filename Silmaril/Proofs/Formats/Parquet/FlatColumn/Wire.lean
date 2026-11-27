module

public import Silmaril.Formats.Parquet.FlatColumn.Defs
import all Silmaril.Formats.Parquet.FlatColumn.Defs
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatColumn

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatColumn

private theorem bind_ok {ε α β : Type} {input : Except ε α} {f : α → Except ε β} {out : β}
    (success : (input >>= f) = .ok out) : ∃ a, input = .ok a ∧ f a = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => exact ⟨a, rfl, success⟩

private theorem mapError_ok {ε δ α : Type} {input : Except ε α} {f : ε → δ} {out : α}
    (success : input.mapError f = .ok out) : input = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => cases success; rfl

private theorem mapM_order {ε α β : Type} (f : α → Except ε β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      List.Forall₂ (fun x y => f x = .ok y) xs ys
  | [], _, read => by cases read; exact .nil
  | _ :: _, _, read => by
    rw [List.mapM_cons] at read
    obtain ⟨_, head, read⟩ := bind_ok read
    obtain ⟨_, tail, read⟩ := bind_ok read
    cases read
    exact .cons head (mapM_order f tail)

private theorem runPage_wire {α ε : Type} {codec : CodecProfile} {limits : Limits}
    {decode : DecodePage α ε} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {source : Bytes} {frame : Page.Frame} {slots : List (Option α)}
    (read : runPage codec limits decode leaf metadata source frame = .ok slots) :
    CheckedCallbackWire codec limits decode leaf metadata source frame slots := by
  unfold runPage at read
  obtain ⟨status, checksum, read⟩ := bind_ok read
  obtain ⟨_, decoded, read⟩ := bind_ok read
  split at read <;> try contradiction
  rename_i count
  split at read <;> try contradiction
  cases read
  exact ⟨⟨status, mapError_ok checksum⟩, mapError_ok decoded, not_not.mp count⟩

private theorem locateChunk_wire {profile : CodecProfile} {limits : Limits} {policy : Policy} {selection : Selection}
    {leaf : Footer.SchemaElement} {group : Footer.RowGroup} {metadata : Footer.ColumnMetadata}
    {footerStart : Nat} {chunk : Footer.Span}
    (read : locateChunk profile limits policy selection leaf group metadata footerStart = .ok chunk) :
    metadata.pathInSchema = [leaf.name] ∧ metadata.physicalType = selection.physical ∧
    metadata.numValues = group.numRows ∧ metadata.codec = profile.id ∧
    Page.columnSpan footerStart metadata = some chunk := by
  unfold locateChunk at read
  split at read <;> try contradiction
  rename_i associated
  split at read <;> try contradiction
  rename_i codec
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  rename_i span
  cases read
  obtain ⟨path, type, values⟩ := not_not.mp associated
  exact ⟨path, type, values, not_not.mp codec, span⟩

theorem readColumnFor_checked_wire {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy} {decode : DecodePage α ε}
    {codec : CodecProfile} {index : Nat} {slots : List (Option α)}
    (read : readColumnFor codec binding limits policy decode index = .ok slots) :
    ∃ group, ColumnWireWith codec binding limits (CheckedCallbackWire codec limits decode binding.leaf)
      index group slots := by
  unfold readColumnFor at read
  split at read <;> try contradiction
  rename_i group groupAt
  dsimp only at read
  split at read <;> try contradiction
  split at read <;> try contradiction
  rename_i column columnAt
  obtain ⟨chunk, located, read⟩ := bind_ok read
  obtain ⟨frames, framed, read⟩ := bind_ok read
  obtain ⟨_, _, read⟩ := bind_ok read
  split at read <;> try contradiction
  rename_i declared
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  split at read <;> try contradiction
  rename_i count
  cases read
  obtain ⟨path, type, values, codec, span⟩ := locateChunk_wire (mapError_ok located)
  refine ⟨group, column, chunk, frames, pages, groupAt, columnAt, path, type, values, codec,
    span, mapError_ok framed, not_not.mp declared, ?_, rfl, count⟩
  rw [← List.zipIdx_map_fst 0 frames, List.forall₂_map_left_iff]
  exact (mapM_order _ decoded).imp (fun _ _ h => runPage_wire (mapError_ok h))

theorem readColumnFor_wire {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy} {decode : DecodePage α ε}
    {codec : CodecProfile} {index : Nat} {slots : List (Option α)}
    (read : readColumnFor codec binding limits policy decode index = .ok slots) :
    ∃ group, ColumnWireFor codec binding limits decode index group slots := by
  obtain ⟨group, column, chunk, frames, pages, groupAt, columnAt, path, physical, count,
    codecAt, span, framed, declared, callbacks, output, rows⟩ := readColumnFor_checked_wire read
  exact ⟨group, column, chunk, frames, pages, groupAt, columnAt, path, physical, count,
    codecAt, span, framed, declared, callbacks.imp (fun _ _ wire => wire.2), output, rows⟩

end Silmaril.Proofs.Formats.Parquet.FlatColumn
