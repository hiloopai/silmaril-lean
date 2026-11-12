module

public import Silmaril.Data.Cells.Defs

/-!
# Runs of blocks with headers and boundary tags

A heap tiled by adjacent blocks, each with a size header that also carries a "previous block
free" flag, and a boundary tag (a copy of the size at the end) on each free block: the
Knuth/dlmalloc/ptmalloc scheme. Generic over the header layout (`Tag`).
-/

@[expose] public section

namespace Silmaril.Data.BoundaryTag

open Silmaril.Data

/-- **The header layout**: offset of the size word from the block's address, word width, the
"previous block in use" flag value (added to the size when the previous block is in use), and
the offset of the boundary tag from the next block's address (glibc: `prev_size` at offset 0 of
the next chunk). -/
structure Tag where
  sizeOff : Nat
  ws : Nat := 8
  prevInuse : Nat := 1
  tagOff : Nat := 0
  deriving DecidableEq, Repr

/-- A block of a run: address, size, free (carries a boundary tag, clears its successor's
flag). -/
structure Blk where
  addr : Nat
  size : Nat
  free : Bool
  deriving DecidableEq, Repr

/-- **A run of blocks**: each block's header (`size + prevInuse` unless the previous block is
free, `pf` for the first) and a boundary tag after each free block. -/
def run (T : Tag) : Bool → List Blk → Frag
  | _, [] => []
  | pf, b :: bs =>
    ⟨b.addr + T.sizeOff, T.ws, b.size + if pf then 0 else T.prevInuse⟩ ::
      ((if b.free then [⟨b.addr + b.size + T.tagOff, T.ws, b.size⟩] else []) ++ run T b.free bs)

/-- The blocks of an adjacent run from `a` with sizes and free flags. -/
def tile : Nat → List (Nat × Bool) → List Blk
  | _, [] => []
  | a, (s, f) :: rest => ⟨a, s, f⟩ :: tile (a + s) rest

/-- The free flag of the last block of `bs` (`pf` when empty): the flag the next block's header
sees. -/
def lastFree (pf : Bool) (bs : List Blk) : Bool := (bs.getLast?.map (·.free)).getD pf

/-! ## Obligations (owned by `seplist`; discharged in `Silmaril.Data.BoundaryTag.Thms`)

Revised by `seplist`: each now assumes a word width > 0, a separated old fragment (plus the fresh
cell a split or relabel creates), and sizes that fit a word with the flag added. -/

/-- **`Task.seplist.tagSplit`**: splitting a block `b` of a run into an in-use block of `s₁`
bytes and a remainder that keeps `b`'s free flag writes the two size words (and the remainder's
boundary tag when free). -/
def Task.seplist.tagSplit : Prop :=
  ∀ (T : Tag) (v : MemView) (pf : Bool) (pre post : List Blk) (b : Blk) (s₁ : Nat), 0 < T.ws →
    (run T pf (pre ++ b :: post)).Holds v → 0 < s₁ → s₁ < b.size →
    b.size + T.prevInuse < 256 ^ T.ws →
    (∀ i < T.ws, v.writable (b.addr + s₁ + T.sizeOff + i) = true) →
    Frag.Sep (run T pf (pre ++ b :: post) ++ [⟨b.addr + s₁ + T.sizeOff, T.ws, 0⟩]) →
    let pf' := lastFree pf pre
    (run T pf (pre ++ ⟨b.addr, s₁, false⟩ :: ⟨b.addr + s₁, b.size - s₁, b.free⟩ :: post)).Holds
      (v.storeAll ([⟨b.addr + T.sizeOff, T.ws, s₁ + if pf' then 0 else T.prevInuse⟩,
        ⟨b.addr + s₁ + T.sizeOff, T.ws, b.size - s₁ + T.prevInuse⟩] ++
        (if b.free then [⟨b.addr + b.size + T.tagOff, T.ws, b.size - s₁⟩] else [])))

/-- **`Task.seplist.tagMerge`**: merging two adjacent blocks into one with free flag `f` (equal
to the second's, so the successor's flag stays right) writes the first's size word and, when
free, the merged boundary tag (where the second's was). -/
def Task.seplist.tagMerge : Prop :=
  ∀ (T : Tag) (v : MemView) (pf : Bool) (pre post : List Blk) (b₁ b₂ : Blk) (f : Bool), 0 < T.ws →
    (run T pf (pre ++ b₁ :: b₂ :: post)).Holds v → b₂.addr = b₁.addr + b₁.size → f = b₂.free →
    b₁.size + b₂.size + T.prevInuse < 256 ^ T.ws →
    (run T pf (pre ++ b₁ :: b₂ :: post)).Sep →
    let pf' := lastFree pf pre
    (run T pf (pre ++ ⟨b₁.addr, b₁.size + b₂.size, f⟩ :: post)).Holds
      (v.storeAll ([⟨b₁.addr + T.sizeOff, T.ws, b₁.size + b₂.size + if pf' then 0 else T.prevInuse⟩] ++
        (if f then [⟨b₁.addr + b₁.size + b₂.size + T.tagOff, T.ws, b₁.size + b₂.size⟩] else [])))

/-- **`Task.seplist.tagRelabel`**: flipping a block's free flag to `f` writes its successor's
header (the flag) and, when `f`, its boundary tag. -/
def Task.seplist.tagRelabel : Prop :=
  ∀ (T : Tag) (v : MemView) (pf : Bool) (pre post : List Blk) (b : Blk) (f : Bool), 0 < T.ws →
    (run T pf (pre ++ b :: post)).Holds v → (∀ n ∈ post.head?, n.addr = b.addr + b.size) →
    (∀ n ∈ post.head?, n.size + T.prevInuse < 256 ^ T.ws) → b.size < 256 ^ T.ws →
    (∀ i < T.ws, v.writable (b.addr + b.size + T.tagOff + i) = true) →
    Frag.Sep (run T pf (pre ++ b :: post) ++
      (if b.free then [] else [⟨b.addr + b.size + T.tagOff, T.ws, 0⟩])) →
    (run T pf (pre ++ { b with free := f } :: post)).Holds (v.storeAll
      ((match post.head? with
        | some n => [⟨n.addr + T.sizeOff, T.ws, n.size + if f then 0 else T.prevInuse⟩]
        | none => []) ++
       (if f then [⟨b.addr + b.size + T.tagOff, T.ws, b.size⟩] else [])))

end Silmaril.Data.BoundaryTag
