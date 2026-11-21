module

public import Silmaril.Prelude.ChunkSeq.Balanced.Defs
import Init.Data.Array.Lemmas
import Init.Omega

public section
namespace Silmaril.Proofs.ChunkSeq.Balanced

open Silmaril.ChunkSeq.Balanced

universe u
variable {α : Type u}

private theorem acc_append (tree : Tree α) (suffix : List α) :
    tree.toListAcc suffix = tree.toListAcc [] ++ suffix := by
  induction tree generalizing suffix with
  | empty => rfl
  | node count left value right leftIH rightIH =>
    simp only [Tree.toListAcc]
    rw [leftIH (value :: right.toListAcc suffix), rightIH suffix, leftIH (value :: right.toListAcc [])]
    simp only [List.cons_append, List.append_assoc]

theorem list_node (count : Nat) (left right : Tree α) (value : α) :
    (Tree.node count left value right).toList = left.toList ++ value :: right.toList :=
  acc_append left _

theorem tree_list_push (tree : Tree α) (item : α) :
    (tree.push item).toList = tree.toList ++ [item] := by
  induction tree with
  | empty => rfl
  | node count left value right _ rightIH =>
    simp only [Tree.push]
    split
    · simp only [list_node]; rfl
    · simp only [list_node, rightIH, List.append_assoc, List.cons_append]

private theorem foldl_view {β : Type u} (step : β → α → β) (view : β → List α)
    (spec : ∀ state item, view (step state item) = view state ++ [item]) (items : List α) (state : β) :
    view (items.foldl step state) = view state ++ items := by
  induction items generalizing state with
  | nil => simp
  | cons item items ih => simp [ih, spec, List.append_assoc]

theorem tree_list_ofList (items : List α) : (Tree.ofList items).toList = items :=
  foldl_view Tree.push Tree.toList tree_list_push items .empty

theorem tree_ofList_append (items : List α) (item : α) :
    Tree.ofList (items ++ [item]) = (Tree.ofList items).push item := by
  simp [Tree.ofList, List.foldl_append]

theorem tree_size_push (tree : Tree α) (item : α) : (tree.push item).size = tree.size + 1 := by
  cases tree with
  | empty => rfl
  | node => simp only [Tree.push]; split <;> rfl

private theorem sized_push {tree : Tree α} (ok : tree.WellSized) (item : α) :
    (tree.push item).WellSized := by
  induction tree with
  | empty => exact ⟨rfl, trivial, trivial⟩
  | node count left value right _ rightIH =>
    simp only [Tree.push]
    split
    · exact ⟨by simp [Tree.size], ok, trivial⟩
    · obtain ⟨hcount, hleft, hright⟩ := ok
      exact ⟨by rw [tree_size_push, hcount]; omega, hleft, rightIH hright⟩

private theorem foldl_invariant {β : Type u} {step : β → α → β} {invariant : β → Prop}
    (preserve : ∀ {state}, invariant state → ∀ item, invariant (step state item))
    (items : List α) {state : β} (ok : invariant state) : invariant (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact ok
  | cons item items ih => exact ih (preserve ok item)

theorem tree_sized {tree : Tree α} (canonical : tree.Canonical) : tree.WellSized := by
  rw [canonical]
  exact foldl_invariant sized_push _ (state := Tree.empty) trivial

theorem tree_size_eq {tree : Tree α} (ok : tree.WellSized) : tree.size = tree.toList.length := by
  induction tree with
  | empty => rfl
  | node count left value right leftIH rightIH =>
    obtain ⟨hcount, hleft, hright⟩ := ok
    simp only [list_node, Tree.size, List.length_append, List.length_cons]
    rw [hcount, leftIH hleft, rightIH hright]
    omega

theorem tree_get {tree : Tree α} (ok : tree.WellSized) (index : Nat) :
    tree.get? index = tree.toList[index]? := by
  induction tree generalizing index with
  | empty => rfl
  | node count left value right leftIH rightIH =>
    obtain ⟨_, hleft, hright⟩ := ok
    simp only [Tree.get?, list_node, tree_size_eq hleft, List.getElem?_append]
    split
    · simpa using leftIH hleft index
    · rw [List.getElem?_cons]
      split <;> split <;> simp_all [rightIH hright, beq_iff_eq] <;> omega

theorem chunks_list_push (width : Nat) (chunks : Chunks α) (item : α) :
    (chunks.push width item).toList = chunks.toList ++ [item] := by
  simp only [Chunks.push, Chunks.toList]
  split <;> simp [tree_list_push, Array.toList_push, List.append_assoc]

theorem chunks_list_ofList (width : Nat) (items : List α) : (Chunks.ofList width items).toList = items :=
  foldl_view (Chunks.push width) Chunks.toList (chunks_list_push width) items Chunks.empty

theorem chunks_ofList_append (width : Nat) (items : List α) (item : α) :
    Chunks.ofList width (items ++ [item]) = (Chunks.ofList width items).push width item := by
  simp [Chunks.ofList, List.foldl_append]

private theorem formed_push (width : Nat) {chunks : Chunks α} (ok : chunks.WellFormed width)
    (item : α) : (chunks.push width item).WellFormed width := by
  obtain ⟨hsized, hfull, htail⟩ := ok
  simp only [Chunks.push]
  split
  · rename_i complete
    refine ⟨sized_push hsized _, ?_, by simp⟩
    intro items member
    simp only [tree_list_push, List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · exact hfull items previous
    · exact beq_iff_eq.mp complete
  · rename_i incomplete
    refine ⟨hsized, hfull, ?_⟩
    have different := mt beq_iff_eq.mpr incomplete
    simp only [Array.size_push] at different ⊢
    omega

theorem chunks_formed {width : Nat} {chunks : Chunks α} (canonical : chunks.Canonical width) :
    chunks.WellFormed width := by
  rw [canonical]
  exact foldl_invariant (formed_push width) _ (state := Chunks.empty) (by simp [Chunks.WellFormed,
    Chunks.empty, Tree.WellSized, Tree.toList, Tree.toListAcc])

private theorem flat_length (width : Nat) (items : List (Array α))
    (full : ∀ chunk ∈ items, chunk.size = width) :
    (items.flatMap Array.toList).length = items.length * width := by
  induction items with
  | nil => simp
  | cons chunk rest ih =>
    simp [ih (fun item mem => full item (by simp [mem])), full chunk (by simp), Nat.succ_mul, Nat.add_comm]

theorem chunks_size_eq {width : Nat} {chunks : Chunks α} (ok : chunks.WellFormed width) :
    chunks.size width = chunks.toList.length := by
  simp [Chunks.size, Chunks.toList, tree_size_eq ok.1, flat_length _ _ ok.2.1]

private theorem flat_get (width : Nat) (positive : 0 < width) (items : List (Array α)) (tail : Array α)
    (full : ∀ chunk ∈ items, chunk.size = width) (small : tail.size < width) (index : Nat) :
    (if index / width = items.length then tail[index % width]?
      else items[index / width]?.bind (fun chunk => chunk[index % width]?)) =
      (items.flatMap Array.toList ++ tail.toList)[index]? := by
  induction items generalizing index with
  | nil =>
    by_cases within : index < width
    · simp [Nat.div_eq_of_lt within, Nat.mod_eq_of_lt within]
    · have outside : tail.size ≤ index := by omega
      simp [Nat.div_eq_zero_iff_lt positive, within, Array.getElem?_eq_none outside]
  | cons head rest ih =>
    have sizeHead := full head (by simp)
    have sizeRest : ∀ chunk ∈ rest, chunk.size = width := fun chunk mem => full chunk (by simp [mem])
    by_cases within : index < width
    · simp [List.getElem?_append, Nat.div_eq_of_lt within, Nat.mod_eq_of_lt within, sizeHead, within]
    · have after : width ≤ index := by omega
      have quotient : 0 < index / width := Nat.div_pos after positive
      have divStep : (index - width) / width = index / width - 1 := by
        simpa only [Nat.mul_one] using Nat.sub_mul_div index width 1
      have modStep : (index - width) % width = index % width := by
        simpa only [Nat.mul_one] using (Nat.sub_mul_mod (k := 1) (by simpa only [Nat.mul_one] using after))
      have lenStep : index / width = rest.length + 1 ↔ index / width - 1 = rest.length := by omega
      simpa [List.getElem?_append, sizeHead, within, divStep, modStep, List.getElem?_cons,
        show index / width ≠ 0 by omega, lenStep] using ih sizeRest (index - width)

theorem chunks_get {width : Nat} {chunks : Chunks α} (ok : chunks.WellFormed width) (index : Nat) :
    chunks.get? width index = chunks.toList[index]? := by
  simp only [Chunks.get?, Chunks.toList, tree_size_eq ok.1, beq_iff_eq, tree_get ok.1]
  exact flat_get (width + 1) (by omega) _ _ ok.2.1 ok.2.2 index

theorem orient_get (side : Side) (items : List α) (index : Nat) :
    (match side.index? items.length index with | none => none | some index => items[index]?) =
      (side.orient items)[index]? := by
  by_cases inside : index < items.length <;> cases side <;> simp [Side.index?, Side.orient, inside]

theorem seq_get {side : Side} (seq : Seq side α) (index : Nat) : seq.get? index = seq.toList[index]? := by
  unfold Seq.get? Seq.size Seq.toList
  rw [tree_size_eq (tree_sized seq.property)]
  have oriented := orient_get side seq.val.toList index
  generalize side.index? seq.val.toList.length index = routed at oriented ⊢
  cases routed with
  | none => exact oriented
  | some offset => exact (tree_get (tree_sized seq.property) offset).trans oriented

theorem chunked_get {side : Side} {width : Nat} (seq : Chunked side width α) (index : Nat) :
    seq.get? index = seq.toList[index]? := by
  unfold Chunked.get? Chunked.size Chunked.toList
  rw [chunks_size_eq (chunks_formed seq.property)]
  have oriented := orient_get side seq.val.toList index
  generalize side.index? seq.val.toList.length index = routed at oriented ⊢
  cases routed with
  | none => exact oriented
  | some offset => exact (chunks_get (chunks_formed seq.property) offset).trans oriented

end Silmaril.Proofs.ChunkSeq.Balanced
