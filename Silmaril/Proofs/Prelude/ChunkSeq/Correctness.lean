module

public import Silmaril.Prelude.ChunkSeq.Defs
import Init.Data.Array.Lemmas
import Init.Data.List.Impl
import Init.Omega

public section
namespace Silmaril.Proofs.ChunkSeq

open Silmaril

universe u v
variable {α : Type u} {β : Type v}

theorem get?_eq (tree : ChunkSeq α) (wellSized : tree.WellSized) (i : Nat) :
    tree.get? i = tree.toList[i]? := by
  induction tree generalizing i with
  | leaf items => simp [ChunkSeq.get?, ChunkSeq.toList]
  | branch size left right leftIH rightIH =>
    rcases wellSized with ⟨rfl, hleft, hright⟩
    simp only [ChunkSeq.get?, ChunkSeq.toList, List.getElem?_append]
    split
    · exact leftIH hleft i
    · exact rightIH hright _

private theorem splitExtract (items : Array α) (start mid stop : Nat)
    (ordered : start ≤ mid ∧ mid ≤ stop ∧ stop ≤ items.size) :
    (items.extract start mid).toList ++ (items.extract mid stop).toList =
      (items.extract start stop).toList := by
  apply List.ext_getElem?
  intro i
  have hmid : mid ≤ items.size := by omega
  simp only [List.getElem?_append, Array.length_toList, Array.getElem?_toList, Array.getElem?_extract,
    Array.size_extract, Nat.min_eq_left hmid, Nat.min_eq_left ordered.2.2]
  split <;> split <;> (try split) <;> (try omega) <;> try rfl
  congr 1
  omega

theorem ofRange_spec (items : Array α) (fuel start count : Nat) (bounds : start + count ≤ items.size) :
    (ChunkSeq.ofRange items fuel start count).toList = (items.extract start (start + count)).toList ∧
      (ChunkSeq.ofRange items fuel start count).WellSized := by
  induction fuel generalizing start count with
  | zero => exact ⟨rfl, trivial⟩
  | succ fuel ih =>
    rw [ChunkSeq.ofRange]
    split
    · exact ⟨rfl, trivial⟩
    · have midBound : count / 2 ≤ count := Nat.div_le_self ..
      have hleft := ih start (count / 2) (by omega)
      have hright := ih (start + count / 2) (count - count / 2) (by omega)
      have hstop : start + count / 2 + (count - count / 2) = start + count := by omega
      simp only [ChunkSeq.toList, ChunkSeq.WellSized, hleft.1, hright.1, hstop]
      refine ⟨splitExtract items _ _ _ (by omega), ?_, hleft.2, hright.2⟩
      rw [Array.length_toList, Array.size_extract, Nat.min_eq_left (by omega : start + count / 2 ≤ items.size)]
      omega

theorem findSome?_eq (tree : ChunkSeq α) (f : α → Option β) :
    tree.findSome? f = tree.toList.findSome? f := by
  induction tree with
  | leaf items => cases items; simp [ChunkSeq.findSome?, ChunkSeq.toList]
  | branch size left right leftIH rightIH =>
    simp only [ChunkSeq.findSome?, ChunkSeq.toList, List.findSome?_append, leftIH, rightIH]
    cases left.toList.findSome? f <;> rfl

end Silmaril.Proofs.ChunkSeq
