module

public import Silmaril.X86.Sep.SysV.Defs
public import Silmaril.X86.Sep.Extra.Defs

/-!
# The allocator interface, as clients see it

`Iface` is an **abstraction record** for a `malloc`/`free` implementation at the `FnSpec`
level:

* `mm : SProp`: the allocator's whole state (globals, free memory, metadata, ghost authority),
  threaded through every call that may allocate, as VST's `mem_mgr`;
* `tok p n : SProp`: the deallocation token of the live block at `p` of requested size `n`, as
  VST's `malloc_token`;
* `align`: every non-null result is a multiple of it;
* `stack`: one stack budget for every entry point, callees included.

Clients are proved `∀ A : Iface`; no laws about `Iface` are assumed, so a client cannot depend
on how an allocator represents its state.

The specs are **loose** on purpose:

* **failure is always allowed**: `mallocSpec`, `callocSpec` and `reallocSpec` may return `0`
  for every request (`Iface.never` and `never_malloc_sat` show that the trivial allocator
  meets the interface);
* **contents are unknown**: a fresh block is `blockAny` (readable and writable, contents
  unknown, possibly unbacked), so a client cannot read before writing;
* **address reuse is allowed**: nothing is said about freshness of an address.

`calloc` is the exception to "failure only": its zeroed block is `bytesPt … (replicate _ 0)`,
and an overflowing product must fail (C17 7.22.3.2). `realloc(p, 0)` with `p ≠ 0` loses the
block either way (`strue`); the spec gives nothing back, so a client may not rely on glibc's
or C23's choice. `usableSpec` (`malloc_usable_size`, SQLite `xSize`) is an optional extension.

`int`/`unsigned` arguments are not used here: every size is a full `size_t` register word.

The laws (`Iface.weaken`, `mallocSpec_sub_weaken`, `fresh_split`, …) and the non-vacuity
witnesses (`never_malloc_sat`, `never_free_sat`, on `Open.isa`) are in `Sep/Alloc/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Alloc

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-- **An allocator abstraction, as clients see it.** -/
structure Iface where
  /-- The allocator's state: globals, free memory, metadata, ghost authority. -/
  mm : SProp
  /-- `tok p n`: the block at `p` of requested size `n` is live and may be freed by its
  holder. -/
  tok : Word → Nat → SProp
  /-- Every non-null result is a multiple of `align` (glibc on x86-64: 16). -/
  align : Nat
  /-- Stack budget of every entry point, including its callees. -/
  stack : Nat

/-- A fresh block: non-null, aligned, its token, and `n` writable bytes of unknown contents.
`blockAny` already gives `p + n ≤ 2 ^ 64` (every byte atom is below `addressLimit`). -/
def Iface.Fresh (A : Iface) (p : Word) (n : Nat) : SProp :=
  ⌜p ≠ 0 ∧ p.toNat % A.align = 0⌝ ∗ A.tok p n ∗ blockAny p.toNat n

/-- The same allocator with a weaker alignment promise (`d ∣ A.align` in the laws). -/
def Iface.weaken (A : Iface) (d : Nat) : Iface := { A with align := d }

/-- `void *malloc(size_t n)`. Failure is always allowed; `n = 0` may return either. -/
def mallocSpec (A : Iface) : FnSpec where
  Arg := Word
  args n := [n]
  stack := A.stack
  pre _ := A.mm
  post n v := A.mm ∗ sor ⌜v = 0⌝ (A.Fresh v n.toNat)

/-- `void free(void *p)`: `NULL` (`(p, none)`), or a live block of requested size `n` given
back with its token (`(p, some n)`). -/
def freeSpec (A : Iface) : FnSpec where
  Arg := Word × Option Nat
  args x := [x.1]
  stack := A.stack
  pre
    | (p, none) => A.mm ∗ ⌜p = 0⌝
    | (p, some n) => A.mm ∗ A.tok p n ∗ blockAny p.toNat n
  post _ _ := A.mm

/-- `void *calloc(size_t k, size_t m)`: zeroed contents; an overflowing product **must**
fail (C17 7.22.3.2). -/
def callocSpec (A : Iface) : FnSpec where
  Arg := Word × Word
  args x := [x.1, x.2]
  stack := A.stack
  pre _ := A.mm
  post x v := A.mm ∗ ⌜2 ^ 64 ≤ x.1.toNat * x.2.toNat → v = 0⌝ ∗
    sor ⌜v = 0⌝ (⌜v ≠ 0 ∧ v.toNat % A.align = 0⌝ ∗ A.tok v (x.1.toNat * x.2.toNat) ∗
      bytesPt v.toNat (List.replicate (x.1.toNat * x.2.toNat) 0))

/-- The logical arguments of `realloc`: `old = some (m, bs)` iff `p ≠ 0`, with the block's
requested size `m` and its (initialised) contents `bs`. -/
structure ReallocArg where
  p : Word
  n : Word
  old : Option (Nat × List Byte)

/-- `void *realloc(void *p, size_t n)` on an initialised block. With `p = 0` it is `malloc`.
With `p ≠ 0` and `n = 0` the block is lost (`strue`) whatever happens. Otherwise failure keeps
the old block and success moves the common prefix into a fresh block whose tail is unknown. -/
def reallocSpec (A : Iface) : FnSpec where
  Arg := ReallocArg
  args x := [x.p, x.n]
  stack := A.stack
  pre
    | ⟨p, _, none⟩ => A.mm ∗ ⌜p = 0⌝
    | ⟨p, _, some (m, bs)⟩ => A.mm ∗ ⌜bs.length = m⌝ ∗ A.tok p m ∗ bytesPt p.toNat bs
  post
    | ⟨_, n, none⟩, v => A.mm ∗ sor ⌜v = 0⌝ (A.Fresh v n.toNat)
    | ⟨p, n, some (m, bs)⟩, v => A.mm ∗
        if n = 0 then strue
        else sor (⌜v = 0⌝ ∗ A.tok p m ∗ bytesPt p.toNat bs)
          (⌜v ≠ 0 ∧ v.toNat % A.align = 0⌝ ∗ A.tok v n.toNat ∗
            bytesPt v.toNat (bs.take n.toNat) ∗
            blockAny (v.toNat + min m n.toNat) (n.toNat - min m n.toNat))

/-- Optional extension (`malloc_usable_size`, SQLite `xSize`): widen a token to the usable
size. -/
def usableSpec (A : Iface) : FnSpec where
  Arg := Word × Nat
  args x := [x.1]
  stack := A.stack
  pre x := A.tok x.1 x.2 ∗ blockAny x.1.toNat x.2
  post x v := ⌜x.2 ≤ v.toNat⌝ ∗ A.tok x.1 v.toNat ∗ blockAny x.1.toNat v.toNat

/-! ## The allocator that never allocates (non-vacuity of the interface) -/

/-- The allocator that never allocates: its state `mm` absorbs anything, its tokens are
empty. Alignment `2 ^ 63` is vacuous, since no block is ever returned. -/
def Iface.never : Iface where
  mm := strue
  tok _ _ := emp
  align := 1 <<< 63
  stack := 0

/-- Its `malloc`: `xor rax, rax; ret` (`48 31 c0 c3`; the base ISA's `xor` is the REX.W
form). -/
def neverMallocBytes : List Byte := [0x48, 0x31, 0xc0, 0xc3]

/-- Its `free`: `ret`. -/
def neverFreeBytes : List Byte := [0xc3]

end Silmaril.X86.Sep.Alloc
