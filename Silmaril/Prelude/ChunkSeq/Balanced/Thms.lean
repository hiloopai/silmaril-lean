module

public import Silmaril.Prelude.ChunkSeq.Balanced.Defs
import Silmaril.Proofs.Prelude.ChunkSeq.Balanced
import Init.Data.List.Lemmas

@[expose] public section
namespace Silmaril.ChunkSeq.Balanced

universe u
variable {α : Type u} {side : Side} {width : Nat}

open Silmaril.Proofs.ChunkSeq.Balanced

namespace Tree

theorem toList_ofList (items : List α) : (ofList items).toList = items := tree_list_ofList items

theorem toList_push (tree : Tree α) (item : α) : (tree.push item).toList = tree.toList ++ [item] :=
  tree_list_push tree item

theorem ofList_append (items : List α) (item : α) : ofList (items ++ [item]) = (ofList items).push item :=
  tree_ofList_append items item

theorem wellSized {tree : Tree α} (canonical : tree.Canonical) : tree.WellSized := tree_sized canonical

theorem size_eq {tree : Tree α} (canonical : tree.Canonical) : tree.size = tree.toList.length :=
  tree_size_eq (wellSized canonical)

theorem get?_eq {tree : Tree α} (canonical : tree.Canonical) (index : Nat) :
    tree.get? index = tree.toList[index]? := tree_get (wellSized canonical) index

end Tree

namespace Chunks

theorem toList_ofList (width : Nat) (items : List α) : (ofList width items).toList = items :=
  chunks_list_ofList width items

theorem toList_push (width : Nat) (chunks : Chunks α) (item : α) :
    (chunks.push width item).toList = chunks.toList ++ [item] := chunks_list_push width chunks item

theorem ofList_append (width : Nat) (items : List α) (item : α) :
    ofList width (items ++ [item]) = (ofList width items).push width item := chunks_ofList_append width items item

theorem wellFormed {chunks : Chunks α} (canonical : chunks.Canonical width) : chunks.WellFormed width :=
  chunks_formed canonical

theorem size_eq {chunks : Chunks α} (canonical : chunks.Canonical width) :
    chunks.size width = chunks.toList.length := chunks_size_eq (wellFormed canonical)

theorem get?_eq {chunks : Chunks α} (canonical : chunks.Canonical width) (index : Nat) :
    chunks.get? width index = chunks.toList[index]? := chunks_get (wellFormed canonical) index

end Chunks

theorem Side.orient_orient (side : Side) (items : List α) : side.orient (side.orient items) = items := by
  cases side <;> simp [Side.orient]

theorem Side.orient_snoc (side : Side) (items : List α) (item : α) :
    side.orient (items ++ [item]) =
      match side with | .left => side.orient items ++ [item] | .right => item :: side.orient items := by
  cases side <;> simp [Side.orient]

namespace Seq

theorem ext {first second : Seq side α} (same : first.val = second.val) : first = second := by
  cases first; cases second; cases same; rfl

def ofList (side : Side) (items : List α) : Seq side α :=
  ⟨Tree.ofList (side.orient items), by rw [Tree.Canonical, Tree.toList_ofList]⟩

/-- Insert at the right of a left-packed sequence, or at the left of a right-packed one. -/
def insert (seq : Seq side α) (item : α) : Seq side α :=
  ⟨seq.val.push item, by
    rw [Tree.Canonical, Tree.toList_push, Tree.ofList_append]
    exact congrArg (·.push item) seq.property⟩

theorem toList_ofList (items : List α) : (ofList side items).toList = items := by
  simp [toList, ofList, Tree.toList_ofList, Side.orient_orient]

theorem ofList_toList (seq : Seq side α) : ofList side seq.toList = seq := by
  apply ext
  simpa [toList, ofList, Side.orient_orient] using seq.property.symm

theorem toList_insert (seq : Seq side α) (item : α) : (seq.insert item).toList =
    match side with | .left => seq.toList ++ [item] | .right => item :: seq.toList := by
  cases side <;> simp [toList, insert, Tree.toList_push, Side.orient]

theorem get?_eq (seq : Seq side α) (index : Nat) : seq.get? index = seq.toList[index]? := seq_get seq index

end Seq

namespace Chunked

theorem ext {first second : Chunked side width α} (same : first.val = second.val) : first = second := by
  cases first; cases second; cases same; rfl

def ofList (side : Side) (width : Nat) (items : List α) : Chunked side width α :=
  ⟨Chunks.ofList width (side.orient items), by rw [Chunks.Canonical, Chunks.toList_ofList]⟩

/-- Insert at the partial-chunk end, pushing a newly filled chunk into the tree if needed. -/
def insert (seq : Chunked side width α) (item : α) : Chunked side width α :=
  ⟨seq.val.push width item, by
    rw [Chunks.Canonical, Chunks.toList_push, Chunks.ofList_append]
    exact congrArg (Chunks.push width · item) seq.property⟩

theorem toList_ofList (items : List α) : (ofList side width items).toList = items := by
  simp [toList, ofList, Chunks.toList_ofList, Side.orient_orient]

theorem ofList_toList (seq : Chunked side width α) : ofList side width seq.toList = seq := by
  apply ext
  simpa [toList, ofList, Side.orient_orient] using seq.property.symm

theorem toList_insert (seq : Chunked side width α) (item : α) : (seq.insert item).toList =
    match side with | .left => seq.toList ++ [item] | .right => item :: seq.toList := by
  cases side <;> simp [toList, insert, Chunks.toList_push, Side.orient]

theorem get?_eq (seq : Chunked side width α) (index : Nat) : seq.get? index = seq.toList[index]? :=
  chunked_get seq index

end Chunked
end Silmaril.ChunkSeq.Balanced
