module

public import Init.Data.Array.Basic

/-! Canonical left-packed binary trees, with either one value per node or one full array per
node plus a partial tail. Right-packed sequences store the same trees in reverse order. -/

@[expose] public section
namespace Silmaril.ChunkSeq.Balanced

universe u
variable {α : Type u}

inductive Tree (α : Type u) where
  | empty
  | node (size : Nat) (left : Tree α) (value : α) (right : Tree α)

namespace Tree

def size : Tree α → Nat
  | .empty => 0
  | .node count _ _ _ => count

def toListAcc : Tree α → List α → List α
  | .empty, suffix => suffix
  | .node _ left value right, suffix => left.toListAcc (value :: right.toListAcc suffix)

def toList (tree : Tree α) : List α := tree.toListAcc []

/-- A perfect tree becomes the new left child. Otherwise the left child is already full
and insertion follows only the right spine. -/
def push : Tree α → α → Tree α
  | .empty, item => .node 1 .empty item .empty
  | .node count left value right, item =>
    if left.size == right.size then .node (count + 1) (.node count left value right) item .empty
    else .node (count + 1) left value (right.push item)

def ofList (items : List α) : Tree α := items.foldl push .empty

def get? : Tree α → Nat → Option α
  | .empty, _ => none
  | .node _ left value right, index =>
    if index < left.size then left.get? index
    else if index == left.size then some value
    else right.get? (index - left.size - 1)

/-- Exact normal form, not merely local balance or validity of the cached size. -/
def Canonical (tree : Tree α) : Prop := tree = ofList tree.toList

def WellSized : Tree α → Prop
  | .empty => True
  | .node count left _ right =>
    count = left.size + 1 + right.size ∧ left.WellSized ∧ right.WellSized

end Tree

inductive Side where
  | left
  | right

def Side.orient (side : Side) (items : List α) : List α :=
  match side with
  | .left => items
  | .right => items.reverse

def Side.index? (side : Side) (size index : Nat) : Option Nat :=
  if index < size then
    some (match side with | .left => index | .right => size - 1 - index)
  else none

/-- Element-per-node sequence, packed on the chosen side and extended at the other end. -/
structure Seq (_side : Side) (α : Type u) where
  val : Tree α
  property : val.Canonical

namespace Seq

variable {side : Side}

def toList (seq : Seq side α) : List α := side.orient seq.val.toList

def size (seq : Seq side α) : Nat := seq.val.size

def get? (seq : Seq side α) (index : Nat) : Option α :=
  match side.index? seq.size index with
  | none => none
  | some index => seq.val.get? index

end Seq

structure Chunks (α : Type u) where
  full : Tree (Array α)
  tail : Array α

namespace Chunks

def empty : Chunks α := ⟨.empty, #[]⟩

def toList (chunks : Chunks α) : List α :=
  (chunks.full.toList.flatMap Array.toList) ++ chunks.tail.toList

/-- `width` represents the positive chunk size `width + 1`. Full arrays enter the tree;
only the tail (empty when the length is a multiple of the chunk size) can be partial. -/
def push (width : Nat) (chunks : Chunks α) (item : α) : Chunks α :=
  let tail := chunks.tail.push item
  if tail.size == width + 1 then ⟨chunks.full.push tail, #[]⟩ else ⟨chunks.full, tail⟩

def ofList (width : Nat) (items : List α) : Chunks α := items.foldl (push width) empty

def size (width : Nat) (chunks : Chunks α) : Nat :=
  chunks.full.size * (width + 1) + chunks.tail.size

def get? (width : Nat) (chunks : Chunks α) (index : Nat) : Option α := do
  let chunkIndex := index / (width + 1)
  let localIndex := index % (width + 1)
  if chunkIndex == chunks.full.size then chunks.tail[localIndex]?
  else (← chunks.full.get? chunkIndex)[localIndex]?

def Canonical (width : Nat) (chunks : Chunks α) : Prop := chunks = ofList width chunks.toList

def WellFormed (width : Nat) (chunks : Chunks α) : Prop :=
  chunks.full.WellSized ∧ (∀ items ∈ chunks.full.toList, items.size = width + 1) ∧
    chunks.tail.size < width + 1

end Chunks

/-- Fixed-size-chunk sequence. On the right-packed variant the partial tail in storage is
the first chunk in logical order. -/
structure Chunked (_side : Side) (width : Nat) (α : Type u) where
  val : Chunks α
  property : val.Canonical width

namespace Chunked

variable {side : Side} {width : Nat}

def toList (seq : Chunked side width α) : List α := side.orient seq.val.toList

def size (seq : Chunked side width α) : Nat := seq.val.size width

def get? (seq : Chunked side width α) (index : Nat) : Option α :=
  match side.index? seq.size index with
  | none => none
  | some index => seq.val.get? width index

end Chunked

end Silmaril.ChunkSeq.Balanced
