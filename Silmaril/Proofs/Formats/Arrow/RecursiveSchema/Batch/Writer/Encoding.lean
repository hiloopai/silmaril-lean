module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Init.Data.List.Scan.Lemmas

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer

private theorem part_extent (part : Part) : part.encode.len = part.size := by
  cases part with
  | validity => exact Writer.emitBitmap_length _
  | words => exact Writer.emitWords_length _ _

private theorem part_wf (part : Part) : part.encode.wf = true := by
  cases part with
  | validity => exact Writer.emitWords_wf _ _
  | words => exact Writer.emitWords_wf _ _

theorem offset_at (sizes : List Nat) {index : Nat} (bound : index ≤ sizes.length) :
    (listOffsets sizes)[index]? = some (sizes.take index).sum := by
  simp [listOffsets, List.getElem?_scanl, bound, List.sum_eq_foldl_nat]

theorem encode_wire (rowCount : Nat) (planned : Plan) :
    EncodingWire rowCount planned (encode rowCount planned) := by
  let pieces := planned.parts.toList.map Part.encode
  refine ⟨rfl, rfl, ?_, ?_, Writer.packBuffers_aligned 0 pieces, ?_⟩
  · change (Writer.packBuffers 0 pieces).1.length = planned.parts.size
    rw [Writer.packBuffers_count]
    simp [pieces]
  · change (Writer.packBuffers 0 pieces).2.len = planned.bodyBytes
    rw [Writer.packBuffers_length, planned.bodyExtent]
    simp [pieces, partsExtent, List.map_map, Function.comp_def, part_extent, padded]
  · apply Writer.packBuffers_exact
    intro piece member
    obtain ⟨part, _, rfl⟩ := List.mem_map.mp member
    exact part_wf part

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer
