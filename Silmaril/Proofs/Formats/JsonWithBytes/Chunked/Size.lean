module

public import Silmaril.Prelude.ChunkSeq.Balanced.Defs

public section
namespace Silmaril.Proofs.Formats.JsonWithBytes.Chunked

open Silmaril.ChunkSeq.Balanced
variable {Elem : Type}

private theorem tree_mem_lt [SizeOf Elem] {item : Elem} {tree : Tree Elem} :
    item ∈ tree.toList → sizeOf item < sizeOf tree := by
  have step (suffix : List Elem) (tree : Tree Elem) (member : item ∈ tree.toListAcc suffix) :
      sizeOf item < sizeOf tree ∨ item ∈ suffix := by
    induction tree generalizing suffix with
    | empty => exact .inr member
    | node count left value right ihLeft ihRight =>
      rcases ihLeft _ member with leftBound | rest
      · left; rw [Tree.node.sizeOf_spec]; omega
      · rcases List.mem_cons.mp rest with rfl | rightMem
        · left; simp +arith [Tree.node.sizeOf_spec]
        · rcases ihRight _ rightMem with rightBound | suffixMem
          · left; rw [Tree.node.sizeOf_spec]; omega
          · exact .inr suffixMem
  intro member
  simpa using step [] tree member

theorem chunks_mem_lt [SizeOf Elem] {item : Elem} {chunks : Chunks Elem}
    (member : item ∈ chunks.toList) : sizeOf item < sizeOf chunks := by
  rcases List.mem_append.mp member with fullMem | tailMem
  · obtain ⟨block, blockMem, itemMem⟩ := List.mem_flatMap.mp fullMem
    have blockBound := tree_mem_lt blockMem
    have itemBound := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp itemMem)
    cases chunks
    simp_all [Chunks.mk.sizeOf_spec]
    omega
  · have itemBound := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp tailMem)
    cases chunks
    simp_all [Chunks.mk.sizeOf_spec]
    omega

end Silmaril.Proofs.Formats.JsonWithBytes.Chunked
