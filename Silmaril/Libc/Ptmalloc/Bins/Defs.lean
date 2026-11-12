module

public import Silmaril.Libc.Ptmalloc.Chunk.Defs

/-!
# ptmalloc component: small and large bins with the binmap (per arena)

State `BinsSt` (bins `2 … C.lastBin`, head first; large bins sorted by decreasing size; the
`binmap` as one bit per bin), invariant `BinsWF` against the **sorted view**
(`Chunk.view Use.isSorted`), operations `pushFront`, `insertSorted`, `remove`, `mark`, `unmark`,
`scan`. Bin 1 (unsorted) is its own component (`Silmaril.Libc.Ptmalloc.Unsorted`); bin 127 is
only a sentinel (W17/M1, a representation fact).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- **The small and large bins** and the binmap. -/
structure BinsSt where
  lists : Nat → List Nat
  binmap : Nat → Bool

namespace BinsSt

variable (bs : BinsSt)

/-- Insert chunk `a` at the head of bin `i` (small bins: `_int_malloc`'s sorting step). -/
def pushFront (a i : Nat) : BinsSt :=
  { bs with lists := fun j => if j = i then a :: bs.lists j else bs.lists j }

/-- Insert chunk `a` of size `sz a` into large bin `i` at glibc's position (`_int_malloc`'s
sorting step): a chunk of a size already in the bin goes **second** in that size's group
("always insert in the second position", so the group leader keeps its `nextsize` links); a new
size goes before the first smaller chunk (at the end if it is the smallest). The order stays
non-increasing. -/
def insertSorted (sz : Nat → Nat) (a i : Nat) : BinsSt :=
  let l := bs.lists i
  let pre := l.takeWhile fun b => sz a < sz b
  let rest := l.drop pre.length
  let l' := match rest with
    | b :: rest' => if sz b = sz a then pre ++ b :: a :: rest' else pre ++ a :: rest
    | [] => pre ++ [a]
  { bs with lists := fun j => if j = i then l' else bs.lists j }

/-- Remove chunk `a` from bin `i` (`unlink_chunk`). -/
def remove (a i : Nat) : BinsSt :=
  { bs with lists := fun j => if j = i then (bs.lists j).erase a else bs.lists j }

/-- The last chunk of bin `i` (`last (bin)`: the victim of the small-bin and bin-map paths). -/
def last? (i : Nat) : Option Nat := (bs.lists i).getLast?

/-- `mark_bin`. -/
def mark (i : Nat) : BinsSt := { bs with binmap := fun j => if j = i then true else bs.binmap j }

/-- `unmark_bin` (the binmap scan clears the bit of an empty bin). -/
def unmark (i : Nat) : BinsSt := { bs with binmap := fun j => if j = i then false else bs.binmap j }

/-- The binmap scan from bin `i`: the first marked bin below `n`. -/
def scan (i n : Nat) : Option Nat := ((List.range (n - i)).map (· + i)).find? bs.binmap

end BinsSt

/-- **The bins' invariant** against the sorted view `cs` (chunks in bins `2 …`). -/
structure BinsWF (C : Config) (bs : BinsSt) (cs : List Chunk) (sz : Nat → Nat) : Prop where
  exact : ∀ i, 2 ≤ i → ListExact (bs.lists i) cs (.bin i)
  outside : ∀ i, (i < 2 ∨ C.lastBin < i) → bs.lists i = []
  nodup : ∀ i, (bs.lists i).Nodup
  size : ∀ c ∈ cs, ∀ i, c.use = .bin i → 2 ≤ i ∧ i ≤ C.lastBin ∧ C.binIndex c.size = i
  /-- Large bins are sorted by decreasing size (`sz` is the arena's size lookup). -/
  sorted : ∀ i, C.nSmallBins ≤ i → (bs.lists i).Pairwise fun a b => sz b ≤ sz a
  /-- A non-empty bin is marked (a marked bin may be empty: glibc clears lazily). -/
  binmap : ∀ i, bs.lists i ≠ [] → bs.binmap i = true

end Silmaril.Libc.Ptmalloc
