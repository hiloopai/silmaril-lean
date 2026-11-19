module

public import Silmaril.Prelude.ChunkSeq.Defs
import Silmaril.Proofs.Prelude.ChunkSeq.Correctness
import Init.Data.Array.Lemmas

public section
namespace Silmaril.ChunkSeq

universe u v
variable {α : Type u} {β : Type v}

theorem get?_eq (tree : ChunkSeq α) (wellSized : tree.WellSized) (i : Nat) :
    tree.get? i = tree.toList[i]? := Proofs.ChunkSeq.get?_eq tree wellSized i

theorem toList_ofArray (items : Array α) : (ofArray items).toList = items.toList := by
  simpa [ofArray] using (Proofs.ChunkSeq.ofRange_spec items items.size 0 items.size (by simp)).1

theorem wellSized_ofArray (items : Array α) : (ofArray items).WellSized :=
  (Proofs.ChunkSeq.ofRange_spec items items.size 0 items.size (by simp)).2

theorem findSome?_eq (tree : ChunkSeq α) (f : α → Option β) :
    tree.findSome? f = tree.toList.findSome? f := Proofs.ChunkSeq.findSome?_eq tree f

end Silmaril.ChunkSeq
