module

public import Silmaril.Wasm.Cfg.Block.Defs
public import Silmaril.Wasm.Cfg.Examples.Defs
import Silmaril.Proofs.Wasm.Cfg.Block

@[expose] public section

/-!
# The canonical segmentation: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Wasm/Cfg/Block.lean`):

* `segment_isSegmentation`: `segment` computes a segmentation;
* `isSegmentation_unique`: two segmentations of a sequence are equal;
* `existsUnique_segmentation`: every instruction sequence has **exactly one** segmentation into
  basic blocks, so blocks are identified by their sequence and position, independently of how a
  tool computes them.
-/

namespace Silmaril.Wasm.Cfg

theorem segment_isSegmentation (is : List Instr) : IsSegmentation is (segment is) :=
  Silmaril.Proofs.Wasm.Cfg.segment_isSegmentation is

theorem isSegmentation_unique {is : List Instr} {a b : List Segment}
    (ha : IsSegmentation is a) (hb : IsSegmentation is b) : a = b :=
  Silmaril.Proofs.Wasm.Cfg.isSegmentation_unique ha hb

theorem existsUnique_segmentation (is : List Instr) : ∃! segs, IsSegmentation is segs :=
  ⟨segment is, segment_isSegmentation is, fun _ h => isSegmentation_unique h (segment_isSegmentation is)⟩

/-- Any segmentation is the computed one. -/
theorem eq_segment {is : List Instr} {segs : List Segment} (h : IsSegmentation is segs) :
    segs = segment is :=
  isSegmentation_unique h (segment_isSegmentation is)

/-! The loop body of `sum` (`Examples.Verified.prog`): `br_if` ends the first block, `br` the
second. -/

example : (segment (match Examples.sum with
    | [.block _ [.loop _ body], _] => body | _ => [])).map (fun s => (s.body.length, s.term.isSome)) =
    [(3, true), (8, true)] := by decide +kernel

end Silmaril.Wasm.Cfg
