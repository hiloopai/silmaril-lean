module

public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs
import all Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.File

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Plain.ByteArray.File

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

theorem openFile_wire {limits : Limits} {source : Bytes} {name : String} {layout : FlatColumn.Layout}
    {checked : Checked name layout} (opened : openFile limits source name layout = .ok checked) :
    Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.snapshot ∧
    source.length ≤ limits.maxFileBytes ∧ checked.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows ∧
    checked.snapshot.metadata.schema[checked.binding.leafOrdinal]? = some checked.binding.leaf ∧
    checked.binding.leaf.name = name ∧ checked.binding.leaf.physicalType = some .byteArray ∧
    checked.binding.leaf.repetition = some layout.repetition := by
  unfold openFile at opened
  split at opened <;> try contradiction
  rename_i fileCap
  obtain ⟨snapshot, checkedSnapshot, opened⟩ := bind_ok opened
  dsimp only at opened
  split at opened <;> try contradiction
  rename_i rowCap
  cases selected : FlatColumn.bindColumn snapshot ⟨name, .byteArray, layout⟩ with
  | error reason => simp [selected, Except.map, Except.mapError] at opened
  | ok binding =>
    simp [selected, Except.map, Except.mapError] at opened
    cases opened
    exact ⟨mapError_ok checkedSnapshot, Nat.le_of_not_gt fileCap, Nat.le_of_not_gt rowCap,
      FlatColumn.binding_leaf binding⟩

theorem decodePage_wire {limits : Limits} {layout : FlatColumn.Layout}
    {leaf : Footer.SchemaElement} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)}
    (decoded : decodePage limits layout leaf metadata frame.value (FlatColumn.frameBody source frame) = .ok slots) :
    PageWire limits layout metadata source frame slots := by
  unfold decodePage at decoded
  split at decoded <;> try contradiction
  rename_i params projected
  have decodedBody := mapError_ok decoded
  obtain ⟨page, values, prepared, plain, mask, ordered, _, _⟩ := ScalarPage.decode_sound decodedBody
  obtain ⟨levels, valid, wire⟩ := ScalarPage.prepare_sound prepared
  have raw : Plain.ByteArray.decode limits.values (page.mask.count true) page.scalars = .ok values := plain
  obtain ⟨cap, suffix, length, widths⟩ := Plain.ByteArray.decode_ok_iff.mp raw
  exact ⟨params, levels, page, values, projected, valid, wire, mask, ordered,
    (ScalarPage.decode_counts decodedBody).1, suffix, length, cap, widths⟩

theorem readGroup_wire {name : String} {layout : FlatColumn.Layout} {checked : Checked name layout}
    {limits : Limits} {index : Nat} {slots : List (Option Bytes)}
    (read : checked.readGroup limits index = .ok slots) : ∃ group, GroupWire checked limits index group slots := by
  obtain ⟨group, column, chunk, frames, pages, groupAt, columnAt, path, physical, count, codec,
    span, framed, declared, callbacks, output, rows⟩ := FlatColumn.readColumn_wire read
  exact ⟨group, column, chunk, frames, pages, groupAt, columnAt, path, physical, count, codec, span, framed, declared,
    callbacks.imp (fun _ _ callback => decodePage_wire callback.1), output, rows⟩

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.File
