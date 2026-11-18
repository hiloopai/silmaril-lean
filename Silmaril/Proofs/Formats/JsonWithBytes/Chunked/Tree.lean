module

public import Silmaril.Formats.JsonWithBytes.Chunked.Tree.Defs
import Silmaril.Prelude.ChunkSeq.Balanced.Thms

public section
namespace Silmaril.Proofs.Formats.JsonWithBytes.Chunked

open Silmaril.Formats Silmaril.Formats.JsonWithBytes Silmaril.Formats.JsonWithBytes.Chunked
open Silmaril.ChunkSeq.Balanced TreeValue

variable {Number : Type}

theorem toSimple_list [SizeOf Number] (items : Chunks (TreeValue Number)) :
    (TreeValue.list items).toSimple = .list (RawSyn.ofList (items.toList.map toSimple)) := by
  simpa using (toSimple.eq_2 items)

theorem toSimple_map [SizeOf Number] (entries : Chunks (String × TreeValue Number)) :
    (TreeValue.map entries).toSimple = .map (RawSyn.ofEntries (entries.toList.map fun (key, item) => (key, item.toSimple))) := by
  rw [toSimple]
  change (RawSyn.ofEntries (entries.toList.attach.map ((fun entry : String × TreeValue Number =>
    (entry.1, entry.2.toSimple)) ∘ Subtype.val))).map = _
  rw [← List.map_map, List.attach_map_subtype_val]

private def RoundTrip [SizeOf Number] : {index : JsonIx} → RawSyn String (Scalar Number) index → Prop
  | .val, value => (pack value).toSimple = value
  | .arr, items => ∀ acc, (pack items acc).toList.map toSimple = acc.toList.map toSimple ++ items.toList
  | .obj, entries => ∀ acc, (pack entries acc).toList.map (fun entry => (entry.1, entry.2.toSimple)) =
      acc.toList.map (fun entry => (entry.1, entry.2.toSimple)) ++ entries.toEntries

private theorem roundTrip [SizeOf Number] {index : JsonIx} (value : RawSyn String (Scalar Number) index) :
    RoundTrip value := by
  induction value with
  | scalar value => simp [RoundTrip, pack, toSimple]
  | list items ih =>
    change (TreeValue.list (pack items .empty)).toSimple = _
    rw [toSimple_list, ih (Chunks.empty : Chunks (TreeValue Number))]
    simp [Chunks.empty, Chunks.toList, Tree.toList, Tree.toListAcc]
  | map entries ih =>
    change (TreeValue.map (pack entries .empty)).toSimple = _
    rw [toSimple_map, ih (Chunks.empty : Chunks (String × TreeValue Number))]
    simp [Chunks.empty, Chunks.toList, Tree.toList, Tree.toListAcc]
  | nil => simp [RoundTrip, pack]
  | cons item rest itemIH restIH =>
    intro acc
    change (pack rest (acc.push 31 (pack item))).toList.map toSimple = _
    rw [restIH (acc.push 31 (pack item)), Chunks.toList_push, List.map_append]
    simp [(show (pack item).toSimple = item from itemIH)]
  | objNil => simp [RoundTrip, pack]
  | objCons key item rest itemIH restIH =>
    intro acc
    change (pack rest (acc.push 31 (key, pack item))).toList.map (fun entry => (entry.1, entry.2.toSimple)) = _
    rw [restIH (acc.push 31 (key, pack item)), Chunks.toList_push, List.map_append]
    simp [(show (pack item).toSimple = item from itemIH)]

theorem toSimple_ofSimple [SizeOf Number] (value : Ordered Number) : (ofSimple value).toSimple = value :=
  roundTrip value

private def PackedShape : {index : JsonIx} → RawSyn String (Scalar Number) index → Prop
  | .val, _ => True
  | .arr, items => ∀ prefixItems, pack items (Chunks.ofList 31 prefixItems) =
      Chunks.ofList 31 (prefixItems ++ items.toList.map ofSimple)
  | .obj, entries => ∀ prefixEntries, pack entries (Chunks.ofList 31 prefixEntries) =
      Chunks.ofList 31 (prefixEntries ++ entries.toEntries.map (fun entry => (entry.1, ofSimple entry.2)))

private theorem packedShape {index : JsonIx} (value : RawSyn String (Scalar Number) index) :
    PackedShape value := by
  induction value with
  | scalar | list | map => trivial
  | nil => simp [PackedShape, pack]
  | objNil => simp [PackedShape, pack]
  | cons item rest _ restIH =>
    intro prefixItems
    change pack rest ((Chunks.ofList 31 prefixItems).push 31 (ofSimple item)) = _
    rw [← Chunks.ofList_append, restIH (prefixItems ++ [ofSimple item])]
    simp [List.append_assoc]
  | objCons key item rest _ restIH =>
    intro prefixEntries
    change pack rest ((Chunks.ofList 31 prefixEntries).push 31 (key, ofSimple item)) = _
    rw [← Chunks.ofList_append, restIH (prefixEntries ++ [(key, ofSimple item)])]
    simp [List.append_assoc]

theorem ofSimple_list (items : RawSyn String (Scalar Number) .arr) :
    ofSimple (.list items) = .list (Chunks.ofList 31 (items.toList.map ofSimple)) := by
  change TreeValue.list (pack items (Chunks.ofList 31 [])) = _
  rw [show _ = _ from packedShape items []]; rfl

theorem ofSimple_map (entries : RawSyn String (Scalar Number) .obj) :
    ofSimple (.map entries) = .map (Chunks.ofList 31 (entries.toEntries.map (fun entry => (entry.1, ofSimple entry.2)))) := by
  change TreeValue.map (pack entries (Chunks.ofList 31 [])) = _
  rw [show _ = _ from packedShape entries []]; rfl


theorem packed_array_canonical [SizeOf Number] (items : List (Canonical Number)) :
    let value := TreeValue.list (Chunks.ofList 31 (items.map Subtype.val))
    TreeValue.ofSimple value.toSimple = value := by
  dsimp only
  rw [toSimple_list, Chunks.toList_ofList, ofSimple_list, RawSyn.toList_ofList]
  simp only [List.map_map]
  congr 2
  exact List.map_congr_left fun item _ => item.property

theorem packed_object_canonical [SizeOf Number] (entries : List (String × Canonical Number)) :
    let value := TreeValue.map (Chunks.ofList 31 (entries.map (fun entry => (entry.1, entry.2.val))))
    TreeValue.ofSimple value.toSimple = value := by
  dsimp only
  rw [toSimple_map, Chunks.toList_ofList, ofSimple_map, RawSyn.toEntries_ofEntries]
  simp only [List.map_map]
  congr 2
  exact List.map_congr_left fun entry _ => congrArg (entry.1, ·) entry.2.property

end Silmaril.Proofs.Formats.JsonWithBytes.Chunked
