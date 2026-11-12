module

/-! # `malloc`/`free`/`calloc`/`realloc`: a loose functional spec

The client-visible allocator state is a `Heap`: for each address, the requested size of the
live block that starts there. A call is an `ACall`; its outcome `AOut` is a new heap and a
returned word (`0` is a null pointer; `free` returns `0`), or `ub`, a **safety violation**: a
client is safe when no run reaches `ub`.

**`allocLoose`** is the weakest behaviour C17 7.22.3 allows:

* every allocation **may fail** (`0`, heap unchanged);
* a fresh block is anywhere free: nonzero, its footprint (`max n 1` bytes, so that two live
  blocks never share an address) disjoint from every live one and below `2 ^ 64`; addresses of
  freed blocks may be reused;
* `free 0` does nothing; `free p` of a live block removes it; `free p` of anything else,
  including a block already freed (**double free**), is `ub`;
* `calloc k m` with `2 ^ 64 ≤ k * m` must fail (C17 7.22.3.2); otherwise it is `malloc (k * m)`
  (contents are not modelled, so "zeroed" is not stated here);
* `realloc 0 n` is `malloc n`; `realloc p n` of a live block either fails, keeping the block
  (`n ≠ 0`), or moves it to a fresh block (the old address may be reused); `realloc p 0` frees
  the block and returns `0` or a fresh block (glibc returns `0`; C23 makes it undefined, which
  `allocStrict` would turn into `ub`); `realloc p n` of a non-live `p ≠ 0` is `ub`;
* `access p` (a load or store of the byte at `p`, by the client) is `ub` unless `p` is inside
  a live block: so a **use after free** is `ub` (`Silmaril.Libc.Alloc.Thms`).

This is the functional shadow of `Silmaril.X86.Sep.Alloc.Iface` (the separation-logic
interface): `Heap` plays the tokens `tok p n`, and "failure is
always allowed", "contents unknown" and "address reuse allowed" are the same choices. The bridge
(an `Iface` allocator implements `allocLoose` on the heap its tokens describe) is not proved.

`allocNever` (every allocation fails: `Iface.never`) is
the smallest level used here, a non-vacuity witness.
-/

@[expose] public section

namespace Silmaril.Libc

/-- The live blocks: start address ↦ requested size. -/
abbrev Heap := Nat → Option Nat

/-- The empty heap. -/
def Heap.empty : Heap := fun _ => none

/-- `p` is inside a live block. -/
def Heap.Owns (h : Heap) (p : Nat) : Prop := ∃ a n, h a = some n ∧ a ≤ p ∧ p < a + n

/-- A live block may be placed at `p` with size `n`: nonzero, its footprint below `2 ^ 64`
and disjoint from every live footprint. -/
def Heap.Fresh (h : Heap) (p n : Nat) : Prop :=
  p ≠ 0 ∧ p + max n 1 ≤ 2 ^ 64 ∧ ∀ a m, h a = some m → p + max n 1 ≤ a ∨ a + max m 1 ≤ p

/-- Add the block `(p, n)`. -/
def Heap.add (h : Heap) (p n : Nat) : Heap := fun a => if a = p then some n else h a

/-- Remove the block at `p`. -/
def Heap.remove (h : Heap) (p : Nat) : Heap := fun a => if a = p then none else h a

/-- Live footprints are pairwise disjoint and no block is at `0`. -/
def Heap.WF (h : Heap) : Prop :=
  h 0 = none ∧ ∀ a b m n, h a = some m → h b = some n → a ≠ b →
    a + max m 1 ≤ b ∨ b + max n 1 ≤ a

/-- An allocator call, or a client access. -/
inductive ACall
  | malloc (n : Nat)
  | calloc (k m : Nat)
  | realloc (p n : Nat)
  | free (p : Nat)
  | access (p : Nat)

/-- The outcome of a call: the new heap and the returned word, or a safety violation. -/
inductive AOut
  | ok (h : Heap) (ret : Nat)
  | ub

/-- An allocator behaviour: heap, call, allowed outcome. -/
abbrev AllocRel := Heap → ACall → AOut → Prop

/-- `R ⊑ T`. -/
def AllocRel.Le (R T : AllocRel) : Prop := ∀ h c o, R h c o → T h c o

/-- Some outcome everywhere. -/
def AllocRel.Progress (R : AllocRel) : Prop := ∀ h c, ∃ o, R h c o

/-- An allocator of level `T`. -/
def AllocRel.Admissible (T R : AllocRel) : Prop := R.Le T ∧ R.Progress

/-- A fresh allocation of `n` bytes, or failure. -/
def allocate (h : Heap) (n : Nat) (o : AOut) : Prop :=
  o = .ok h 0 ∨ ∃ p, h.Fresh p n ∧ o = .ok (h.add p n) p

/-- **The loose allocator.** -/
def allocLoose : AllocRel := fun h c o =>
  match c with
  | .malloc n => allocate h n o
  | .calloc k m => if 2 ^ 64 ≤ k * m then o = .ok h 0 else allocate h (k * m) o
  | .realloc p n =>
    if p = 0 then allocate h n o
    else if (h p).isSome then
      if n = 0 then allocate (h.remove p) 0 o
      else o = .ok h 0 ∨ ∃ q, (h.remove p).Fresh q n ∧ o = .ok ((h.remove p).add q n) q
    else o = .ub
  | .free p =>
    if p = 0 then o = .ok h 0
    else if (h p).isSome then o = .ok (h.remove p) 0
    else o = .ub
  | .access p => (h.Owns p ∧ o = .ok h 0) ∨ (¬ h.Owns p ∧ o = .ub)

/-- **The allocator that never allocates** (`Iface.never`): every allocation fails; `free`,
`realloc p 0` and `access` are as in `allocLoose`. -/
def allocNever : AllocRel := fun h c o =>
  match c with
  | .malloc _ | .calloc _ _ => o = .ok h 0
  | .realloc p n =>
    if p = 0 then o = .ok h 0
    else if (h p).isSome then (if n = 0 then o = .ok (h.remove p) 0 else o = .ok h 0)
    else o = .ub
  | .free p => allocLoose h (.free p) o
  | .access p => allocLoose h (.access p) o

end Silmaril.Libc
