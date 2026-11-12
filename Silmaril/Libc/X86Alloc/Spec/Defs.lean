module

public import Silmaril.X86.Sep.AllocS.Defs

/-!
# Allocator specifications at three strengths

silmaril's `Silmaril.X86.Sep.Alloc.Iface` is the **loose** (safety) interface: `malloc` may
always fail, and its abstract state is hidden. `Silmaril.X86.Sep.Alloc.IfaceS` adds an
availability promise for one call, but its postcondition forgets the state, so a client cannot
chain it. This module adds the two stronger layers the allocator shapes need; both keep the
`FnSpec` template and the `Iface` representation (`mm`, `tok`, `align`, `stack`), so every
stronger spec refines the loose one (`Silmaril.Libc.X86Alloc.Spec.Thms`).

**Liveness (`CapModel`, `IfaceL`).** A *capacity model* `C` is an abstract state space `C.St`
with

* `C.avail s n`: in state `s` a request of `n` bytes **must** succeed;
* `C.alloc s n v`: the state after `malloc(n)` returned `v ≠ 0`;
* `C.dealloc s p n`: the state after `free(p)` of a block of requested size `n`.

`IfaceL C` describes the allocator's memory at each abstract state (`mmS`). `mallocSpecL`
threads the state: either `v = 0`, the request was not available and the state is unchanged,
or `v` is a fresh block and the state is `C.alloc s n v`. So "`malloc` succeeds whenever enough
memory is available" is exactly `¬ C.avail s n` on the failure branch, and it chains across
calls. The standard models (`CapModel.bump`, `CapModel.pool`, `CapModel.reuse`) are below; a
model is part of the *problem*, so a row fixes it together with the initial state, and the
initial image must establish `mmS s0` (an allocator cannot claim liveness by choosing a model
with nothing available).

**Functional (`RefModel`, `IfaceF`).** A *reference model* `R` is a deterministic allocator on
abstract states: `R.malloc s n` is the address returned (`0` for failure), `R.alloc`,
`R.dealloc` the next states. `mallocSpecF` pins the returned address to `R.malloc s n`, so a
row of this strength says *which* block is returned (first fit, LIFO reuse, bump order).
`RefModel.toCap` is its capacity model (`avail s n ↔ R.malloc s n ≠ 0`).

Sizes are `Nat` (the request register read as a natural number) and every entry point has the
one stack budget `stack`, as in `Iface`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc

/-! ## Capacity models and liveness -/

/-- **A capacity model**: abstract allocator states, when a request must succeed, and the state
after each call. -/
structure CapModel where
  /-- Abstract allocator state. -/
  St : Type
  /-- `avail s n`: in state `s`, `malloc(n)` must succeed. -/
  avail : St → Nat → Prop
  /-- The state after `malloc(n)` returned the block `v ≠ 0`. -/
  alloc : St → Nat → Word → St
  /-- The state after `free(p)` of a block of requested size `n`. -/
  dealloc : St → Word → Nat → St

/-- **An allocator meeting the capacity model `C`**: its memory at each abstract state. -/
structure IfaceL (C : CapModel) where
  /-- The allocator's state, at the abstract state `s`. -/
  mmS : C.St → SProp
  /-- `tok p n`, as in `Iface`. -/
  tok : Word → Nat → SProp
  /-- Every non-null result is a multiple of `align`. -/
  align : Nat
  /-- Stack budget of every entry point. -/
  stack : Nat

/-- Forget the abstract state. -/
def IfaceL.toIface {C : CapModel} (B : IfaceL C) : Iface where
  mm := sexists B.mmS
  tok := B.tok
  align := B.align
  stack := B.stack

/-- **`malloc` with liveness**: failure leaves the state unchanged and is allowed only when the
request is not available; success moves the state to `C.alloc s n v`. -/
def mallocSpecL {C : CapModel} (B : IfaceL C) : FnSpec where
  Arg := C.St × Word
  args x := [x.2]
  stack := B.stack
  pre x := B.mmS x.1
  post x v := sor (⌜v = 0 ∧ ¬ C.avail x.1 x.2.toNat⌝ ∗ B.mmS x.1)
    (B.toIface.Fresh v x.2.toNat ∗ B.mmS (C.alloc x.1 x.2.toNat v))

/-- The logical arguments of `free`: the abstract state, the pointer, and the requested size of
the block (`none` for `free(NULL)`). -/
structure FreeArg (St : Type) where
  s : St
  p : Word
  n : Option Nat

/-- **`free` with state**: `free(NULL)` keeps the state; freeing a live block moves it to
`C.dealloc s p n`. -/
def freeSpecL {C : CapModel} (B : IfaceL C) : FnSpec where
  Arg := FreeArg C.St
  args x := [x.p]
  stack := B.stack
  pre
    | ⟨s, p, none⟩ => B.mmS s ∗ ⌜p = 0⌝
    | ⟨s, p, some n⟩ => B.mmS s ∗ B.tok p n ∗ blockAny p.toNat n
  post
    | ⟨s, _, none⟩, _ => B.mmS s
    | ⟨s, p, some n⟩, _ => B.mmS (C.dealloc s p n)

/-- **Bump capacity**: the state is the number of bytes left; a request costs `cost n` bytes
and must succeed when they are left; `free` returns nothing. -/
def CapModel.bump (cost : Nat → Nat) : CapModel where
  St := Nat
  avail r n := cost n ≤ r
  alloc r n _ := r - cost n
  dealloc r _ _ := r

/-- **Reusing capacity**: as `bump`, but `free` gives the cost of the block back (an ideal
allocator without fragmentation). -/
def CapModel.reuse (cost : Nat → Nat) : CapModel where
  St := Nat
  avail r n := cost n ≤ r
  alloc r n _ := r - cost n
  dealloc r _ n := r + cost n

/-- **Pool capacity**: the state is the number of free blocks of `bs` bytes; a request of at most
`bs` bytes must succeed when a block is free; `free` returns the block. -/
def CapModel.pool (bs : Nat) : CapModel where
  St := Nat
  avail k n := n ≤ bs ∧ 0 < k
  alloc k _ _ := k - 1
  dealloc k _ _ := k + 1

/-- Round `n` up to a multiple of `a`. -/
def roundUp (a n : Nat) : Nat := (n + a - 1) / a * a

/-! ## Reference models and functional correctness -/

/-- **A reference model**: a deterministic allocator on abstract states. -/
structure RefModel where
  /-- Abstract allocator state. -/
  St : Type
  /-- The address `malloc(n)` returns in state `s` (`0`: failure). -/
  malloc : St → Nat → Word
  /-- The state after a successful `malloc(n)`. -/
  alloc : St → Nat → St
  /-- The state after `free(p)` of a block of requested size `n`. -/
  dealloc : St → Word → Nat → St

/-- The capacity model of a reference model: a request is available iff the model serves it. -/
def RefModel.toCap (R : RefModel) : CapModel where
  St := R.St
  avail s n := R.malloc s n ≠ 0
  alloc s n _ := R.alloc s n
  dealloc := R.dealloc

/-- **`malloc` against a reference model**: the result is `R.malloc s n`; at `0` the state is
unchanged, otherwise the block is fresh and the state is `R.alloc s n`. -/
def mallocSpecF {R : RefModel} (B : IfaceL R.toCap) : FnSpec where
  Arg := R.St × Word
  args x := [x.2]
  stack := B.stack
  pre x := B.mmS x.1
  post x v := ⌜v = R.malloc x.1 x.2.toNat⌝ ∗ sor (⌜v = 0⌝ ∗ B.mmS x.1)
    (B.toIface.Fresh v x.2.toNat ∗ B.mmS (R.alloc x.1 x.2.toNat))

/-- `free` against a reference model is `freeSpecL` of its capacity model. -/
abbrev freeSpecF {R : RefModel} (B : IfaceL R.toCap) : FnSpec := freeSpecL B

/-- **A simulation** of the capacity model `C` by the reference model `R` along `α`, on the
states satisfying the invariant `Inv`: every available request is served, the invariant is kept,
and the states move together. Freed pointers are non-null (the interface along `α` adds
`p ≠ 0` to the token). -/
structure RefModel.Sim (R : RefModel) (C : CapModel) (α : R.St → C.St) (Inv : R.St → Prop) :
    Prop where
  avail : ∀ s n, Inv s → C.avail (α s) n → R.malloc s n ≠ 0
  alloc : ∀ s n, Inv s → R.malloc s n ≠ 0 →
    Inv (R.alloc s n) ∧ α (R.alloc s n) = C.alloc (α s) n (R.malloc s n)
  dealloc : ∀ s p n, Inv s → p ≠ 0 → Inv (R.dealloc s p n) ∧ α (R.dealloc s p n) = C.dealloc (α s) p n

/-- An allocator against `R`, seen against `C` through `α`: the memory at `c` is the memory at
some `s` with `α s = c` and `Inv s`; a token also records that the block is non-null. -/
def IfaceL.along {R : RefModel} {C : CapModel} (B : IfaceL R.toCap) (α : R.St → C.St)
    (Inv : R.St → Prop) : IfaceL C where
  mmS c := sexists fun s => ⌜α s = c ∧ Inv s⌝ ∗ B.mmS s
  tok p n := ⌜p ≠ 0⌝ ∗ B.tok p n
  align := B.align
  stack := B.stack

end Silmaril.Libc.X86Alloc

namespace Silmaril.Libc.X86Alloc

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-! ## Where an allocator lives in an executable -/

/-- **The layout of an allocator in an executable**: its code region (holding `malloc` and
`free`), their entry addresses, and its static state with the bytes the loader puts there. -/
structure Layout where
  codeAddr : Nat
  code : List Byte
  malloc : Nat
  free : Nat
  dataAddr : Nat
  data : List Byte

/-- The code assertion of the allocator. -/
def Layout.C (lay : Layout) : SProp := codePt lay.codeAddr lay.code

/-- The allocator's static state as loaded. -/
def Layout.Init (lay : Layout) : SProp := bytesPt lay.dataAddr lay.data

/-- `malloc`'s entry as a word. -/
def Layout.mallocAt (lay : Layout) : Word := BitVec.ofNat 64 lay.malloc

/-- `free`'s entry as a word. -/
def Layout.freeAt (lay : Layout) : Word := BitVec.ofNat 64 lay.free

end Silmaril.Libc.X86Alloc

namespace Silmaril.Libc.X86Alloc

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc

/-! ## Functional strength with a relational `free`

For allocators whose blocks carry their real size in a header held by the client's token, a
deterministic `dealloc` cannot be met without ghost state (see `Silmaril.Libc.Shapes.Alloc.Defs`).
`RelModel` keeps `malloc` deterministic (the returned address is a function of the state) and lets
`free` relate the state to any state the model admits, e.g. one that pushes the block with the size
its header actually holds. -/

/-- **A reference model with a relational `free`.** -/
structure RelModel where
  St : Type
  malloc : St → Nat → Word
  alloc : St → Nat → St
  dealloc : St → Word → Nat → St → Prop

/-- Its capacity-style view, for the shared `IfaceL` record. -/
def RelModel.toCap (R : RelModel) : CapModel where
  St := R.St
  avail s n := R.malloc s n ≠ 0
  alloc s n _ := R.alloc s n
  dealloc s _ _ := s

/-- `malloc` against a relational model: as `mallocSpecF`. -/
def mallocSpecR {R : RelModel} (B : IfaceL R.toCap) : FnSpec where
  Arg := R.St × Word
  args x := [x.2]
  stack := B.stack
  pre x := B.mmS x.1
  post x v := ⌜v = R.malloc x.1 x.2.toNat⌝ ∗ sor (⌜v = 0⌝ ∗ B.mmS x.1)
    (B.toIface.Fresh v x.2.toNat ∗ B.mmS (R.alloc x.1 x.2.toNat))

/-- `free` against a relational model: some admitted next state. -/
def freeSpecR {R : RelModel} (B : IfaceL R.toCap) : FnSpec where
  Arg := FreeArg R.St
  args x := [x.p]
  stack := B.stack
  pre
    | ⟨s, p, none⟩ => B.mmS s ∗ ⌜p = 0⌝
    | ⟨s, p, some n⟩ => B.mmS s ∗ B.tok p n ∗ blockAny p.toNat n
  post
    | ⟨s, _, none⟩, _ => B.mmS s
    | ⟨s, p, some n⟩, _ => sexists fun s' => ⌜R.dealloc s p n s'⌝ ∗ B.mmS s'

end Silmaril.Libc.X86Alloc

/-! ## An explicit heap model (the authoritative live set) -/

@[expose] public section

namespace Silmaril.Libc.X86Alloc

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc

/-- **An allocator's explicit heap model**, in the style of CompCert's and VST's memory
managers: abstract heaps `Heap`, the representation `rep H` (everything the allocator owns,
including the header of every block, live or free), and the live payloads `live H`
(address, usable size). Unlike `Iface`, the allocator state *knows* the live blocks, so `free`
may require its pointer to be live and may read the tags of allocated blocks: no tokens. -/
structure HeapModel where
  Heap : Type
  rep : Heap → SProp
  live : Heap → List (Nat × Nat)

/-- **`malloc` against a heap model**: null with the live set unchanged (always allowed), or
a fresh `align`-aligned payload of `u ≥ n` bytes, added to the live set, whose bytes the client
now owns. -/
def mallocSpecH (HM : HeapModel) (align stack : Nat) : FnSpec where
  Arg := HM.Heap × Word
  args x := [x.2]
  stack := stack
  pre x := HM.rep x.1
  post x v := sexists fun H' : HM.Heap => HM.rep H' ∗
    sor ⌜v = 0 ∧ (HM.live H').Perm (HM.live x.1)⌝
      (sexists fun u : Nat => ⌜v ≠ 0 ∧ v.toNat % align = 0 ∧ x.2.toNat ≤ u ∧
        (HM.live H').Perm ((v.toNat, u) :: HM.live x.1)⌝ ∗ blockAny v.toNat u)

/-- **`free` against a heap model**: `free(NULL)` (`none`) changes nothing; `free(p)` of a
live payload `(p, u)` (`some u`, the client giving its bytes back) removes it from the live
set. -/
def freeSpecH (HM : HeapModel) (stack : Nat) : FnSpec where
  Arg := HM.Heap × Word × Option Nat
  args x := [x.2.1]
  stack := stack
  pre
    | (H, p, none) => HM.rep H ∗ ⌜p = 0⌝
    | (H, p, some u) => HM.rep H ∗ ⌜(p.toNat, u) ∈ HM.live H⌝ ∗ blockAny p.toNat u
  post
    | (H, _, none), _ => sexists fun H' => HM.rep H' ∗ ⌜(HM.live H').Perm (HM.live H)⌝
    | (H, p, some u), _ => sexists fun H' => HM.rep H' ∗
        ⌜(HM.live H').Perm ((HM.live H).erase (p.toNat, u))⌝

end Silmaril.Libc.X86Alloc

end
