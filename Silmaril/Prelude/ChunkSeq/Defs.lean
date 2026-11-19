module

public import Init.Data.Array.Basic

/-! A sequence with short array leaves and a length-cached routing tree. As with `KBytes`,
written-out constructor terms let the kernel inspect a small part without building the whole
sequence. `ofArray` splits at the midpoint above 32 elements. -/

@[expose] public section
namespace Silmaril

universe u v

inductive ChunkSeq (α : Type u) where
  | leaf (items : Array α)
  | branch (leftSize : Nat) (left right : ChunkSeq α)

namespace ChunkSeq

variable {α : Type u} {β : Type v}

def toList : ChunkSeq α → List α
  | .leaf items => items.toList
  | .branch _ left right => left.toList ++ right.toList

def get? : ChunkSeq α → Nat → Option α
  | .leaf items, i => items[i]?
  | .branch leftSize left right, i =>
    if i < leftSize then left.get? i else right.get? (i - leftSize)

def findSome? (f : α → Option β) : ChunkSeq α → Option β
  | .leaf items => items.findSome? f
  | .branch _ left right => (left.findSome? f).orElse fun _ => right.findSome? f

def WellSized : ChunkSeq α → Prop
  | .leaf _ => True
  | .branch leftSize left right =>
    leftSize = left.toList.length ∧ left.WellSized ∧ right.WellSized

def ofRange (items : Array α) : Nat → Nat → Nat → ChunkSeq α
  | 0, start, count => .leaf (items.extract start (start + count))
  | fuel + 1, start, count =>
    if count ≤ 32 then .leaf (items.extract start (start + count))
    else
      let mid := count / 2
      .branch mid (ofRange items fuel start mid) (ofRange items fuel (start + mid) (count - mid))

def ofArray (items : Array α) : ChunkSeq α := ofRange items items.size 0 items.size

end ChunkSeq
end Silmaril
