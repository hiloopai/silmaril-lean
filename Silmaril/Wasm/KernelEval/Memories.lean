module

public import Silmaril.Wasm.KernelEval.Defs

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: memory representations

More implementations of the memory interface `MemOps`, besides the list reference `ListMem` and
the packed `NatMem` of `Silmaril.Wasm.KernelEval.Defs`. Each is related to `ListMem` by an
abstraction function and a **simulation with a validity condition** (`MemSimOn`), so a run on
any of them is a run on the reference (`Silmaril.Wasm.KernelEval.MemThms`).

* `Overlay`: an immutable packed base (a snapshot, an initial image) and a **log of byte
  writes**, newest first. A store prepends `k` entries; a load looks each byte up in the log,
  then in the base. Many memories that differ from one base in a few writes share the base.
  Validity: none.
* `PageMem`: a **persistent complete binary tree of pages**, each page packed into one number
  (`2 ^ pbits` bytes). A store copies one path and rewrites one page; untouched subtrees, and
  all pages of a memory that has not been written, are shared. An access within a page is one
  page read or write; an access crossing pages goes byte by byte. Validity: the tree is
  complete of its depth and every page is below `256 ^ pageSize`.

Both are stated through a **byte view** (`size`, `byte`): `memSimOn_ofView` reduces a
simulation to pointwise facts about bytes, the form new representations (for instance the
kernel-byte type of the core work, once it exists) can be plugged in with.

A Silmaril addition.
-/

namespace Silmaril.Wasm.KernelEval

/-- Byte `j` of the little-endian encoding of `v`. -/
def encByte (v j : Nat) : BitVec 8 := BitVec.ofNat 8 (v / 256 ^ j)

/-- Little-endian decoding of the `k` bytes of `f` from `a`. -/
def loadBytes (f : Nat → BitVec 8) (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (f a).toNat + 256 * loadBytes f (a + 1) k

/-- The list memory with the given size and bytes. -/
def ListMem.ofView (n : Nat) (f : Nat → BitVec 8) : ListMem := ⟨(List.range n).map f⟩

/-! ## Overlays: a packed base and a byte log -/

/-- The newest logged value of byte `i`. -/
def logGet : List (Nat × BitVec 8) → Nat → Option (BitVec 8)
  | [], _ => none
  | (j, b) :: l, i => if j = i then some b else logGet l i

/-- An immutable packed base with byte writes logged on top, newest first. -/
structure Overlay where
  base : NatMem
  log : List (Nat × BitVec 8)
  deriving Repr

/-- Byte `i` of an overlay. -/
def Overlay.byte (o : Overlay) (i : Nat) : BitVec 8 :=
  match logGet o.log i with
  | some b => b
  | none => BitVec.ofNat 8 (o.base.read i 1)

/-- The log entries of storing the `k` bytes of `v` at `a`. -/
def writesOf (a : Nat) : Nat → Nat → List (Nat × BitVec 8)
  | 0, _ => []
  | k + 1, v => (a, BitVec.ofNat 8 v) :: writesOf (a + 1) k (v / 256)

instance : MemOps Overlay where
  load o a k := if a + k ≤ o.base.size then some (loadBytes o.byte a k) else none
  store o a k v := if a + k ≤ o.base.size then some ⟨o.base, writesOf a k v ++ o.log⟩ else none

/-- An overlay without writes. -/
def Overlay.ofBase (m : NatMem) : Overlay := ⟨m, []⟩

/-! ## Persistent page trees -/

/-- A binary tree of pages; each page is packed into one number. -/
inductive PTree where
  | leaf (bits : Nat)
  | node (l r : PTree)
  deriving Repr

/-- Page `i` of a tree of depth `d` (`0` off the tree). -/
def PTree.get : Nat → PTree → Nat → Nat
  | 0, .leaf b, _ => b
  | d + 1, .node l r, i => if i < 2 ^ d then get d l i else get d r (i - 2 ^ d)
  | _, _, _ => 0

/-- Replace page `i` of a tree of depth `d` by `g` of it, copying one path. -/
def PTree.modify : Nat → PTree → Nat → (Nat → Nat) → PTree
  | 0, .leaf b, _, g => .leaf (g b)
  | d + 1, .node l r, i, g =>
    if i < 2 ^ d then .node (modify d l i g) r else .node l (modify d r (i - 2 ^ d) g)
  | _, t, _, _ => t

/-- The tree of depth `d` with every page `0`, its two halves shared. -/
def PTree.zeros : Nat → PTree
  | 0 => .leaf 0
  | d + 1 => let t := zeros d; .node t t

/-- A memory of `2 ^ depth` pages of `2 ^ pbits` bytes. -/
structure PageMem where
  pbits : Nat
  depth : Nat
  tree : PTree
  deriving Repr

/-- Bytes per page. -/
def PageMem.pageSize (m : PageMem) : Nat := 2 ^ m.pbits

/-- Bytes in the memory. -/
def PageMem.size (m : PageMem) : Nat := 2 ^ m.depth * m.pageSize

/-- The packed page holding byte `a`. -/
def PageMem.page (m : PageMem) (a : Nat) : Nat := m.tree.get m.depth (a / m.pageSize)

/-- Byte `a`. -/
def PageMem.byte (m : PageMem) (a : Nat) : BitVec 8 :=
  encByte (m.page a) (a % m.pageSize)

/-- Write the `k` bytes of `v` at offset `o` of a packed page (`NatMem.write`). -/
def pageWrite (b o k v : Nat) : Nat := (NatMem.write ⟨b, 0⟩ o k v).bits

/-- Store one byte, without bounds check. -/
def PageMem.set1 (m : PageMem) (a v : Nat) : PageMem :=
  { m with tree :=
      m.tree.modify m.depth (a / m.pageSize) (fun b => pageWrite b (a % m.pageSize) 1 v) }

/-- Store the `k` bytes of `v` at `a` one byte at a time, without bounds check. -/
def PageMem.setBytes (m : PageMem) (a v : Nat) : Nat → PageMem
  | 0 => m
  | k + 1 => (m.set1 a v).setBytes (a + 1) (v / 256) k

instance : MemOps PageMem where
  load m a k :=
    if a + k ≤ m.size then
      if a % m.pageSize + k ≤ m.pageSize then
        some (NatMem.read ⟨m.page a, 0⟩ (a % m.pageSize) k)
      else some (loadBytes m.byte a k)
    else none
  store m a k v :=
    if a + k ≤ m.size then
      if a % m.pageSize + k ≤ m.pageSize then
        some { m with tree :=
          m.tree.modify m.depth (a / m.pageSize) (fun b => pageWrite b (a % m.pageSize) k v) }
      else some (m.setBytes a v k)
    else none

/-- The zero memory of `2 ^ depth` pages of `2 ^ pbits` bytes. -/
def PageMem.zeros (pbits depth : Nat) : PageMem := ⟨pbits, depth, PTree.zeros depth⟩

/-- The tree is complete of depth `d` and its pages are below `256 ^ P`. -/
def PTree.Wf (P : Nat) : Nat → PTree → Prop
  | 0, .leaf b => b < 256 ^ P
  | d + 1, .node l r => Wf P d l ∧ Wf P d r
  | _, _ => False

/-- Validity of a page memory. -/
def PageMem.Wf (m : PageMem) : Prop := m.tree.Wf m.pageSize m.depth

/-! ## Simulations with a validity condition -/

variable {M : Type} [MemOps M]

/-- `g` simulates on memories satisfying `inv`, which stores preserve. -/
structure MemSimOn {N : Type} [MemOps N] (inv : M → Prop) (g : M → N) : Prop where
  load : ∀ m, inv m → ∀ a k, MemOps.load (g m) a k = MemOps.load m a k
  store : ∀ m, inv m → ∀ a k v, MemOps.store (g m) a k v = (MemOps.store m a k v).map g
  store_inv : ∀ m, inv m → ∀ a k v m', MemOps.store m a k v = some m' → inv m'

/-- The list memory an overlay denotes. -/
def Overlay.toList (o : Overlay) : ListMem := .ofView o.base.size o.byte

/-- The list memory a page memory denotes. -/
def PageMem.toList (m : PageMem) : ListMem := .ofView m.size m.byte

end Silmaril.Wasm.KernelEval
