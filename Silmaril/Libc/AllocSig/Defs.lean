module

public import Silmaril.Libc.Alloc.Defs

/-!
# The allocator signature hierarchy and its POSIX-safe abstract contract

The abstract half of the allocator rows over real ELF files (`Silmaril.Libc.AllocElf`,
`silmaril.shapes.alloc.elf.posix_safe`).

**Signatures** (`Sig`), ordered by inclusion of their functions (`Op`):

    mf   = {malloc, free}
    mfc  = mf  ∪ {calloc}
    mfcr = mfc ∪ {realloc}
    full = mfcr ∪ {aligned_alloc, posix_memalign, malloc_usable_size}

`Sig.ops s` lists the functions of `s`; `s ≤ s'` is the rank order, and `Thms.ops_mono` says it
is inclusion. Every contract below is a conjunction over `s.ops`, so a contract at `s'` gives the
contract at every `s ≤ s'` (the **reduct**, `Thms.SafeOn.reduct`, `AllocElf.Thms.reduct`).

**Calls** (`Call`): the arguments of a call as numbers (the System V argument registers).

**Valid POSIX use** (`Valid h c`, on the live blocks `h : Heap` the client holds): `free`,
`realloc` and `malloc_usable_size` get `NULL` or the start of a live block (so no double free,
no free of a non-block); `aligned_alloc` gets a power-of-two alignment, `posix_memalign` a power
of two that is a multiple of `sizeof (void *) = 8`. The other conditions of valid use (no use
after free, client writes within the requested sizes) are about the client's memory accesses and
are stated at the machine level (`AllocElf`: client steps may not touch the allocator's memory).

**The POSIX-safe relation** (`loose h c h' r q`: from the live blocks `h`, the call `c` may
return `r` in `rax`, hand out the block `q` (`0`: none) and leave the live blocks `h'`) is the
weakest behaviour C17 7.22.3 and POSIX.1-2024 allow; in particular **`NULL` (or `ENOMEM`) is
always allowed** and leaves the heap unchanged:

| call | success | other outcomes |
|---|---|---|
| `malloc n` | a fresh block of `n` bytes (`Heap.Fresh`: nonzero, disjoint from every live block, `max n 1` bytes so that `malloc (0)` blocks are distinct) | `NULL` |
| `calloc k m` | `malloc (k * m)` | `NULL`; `NULL` is required when `2 ^ 64 ≤ k * m` |
| `free p` | `NULL`: nothing; else the block is released | — |
| `realloc p n` | `p = NULL`: `malloc n`; else the block moves to a fresh block of `n` bytes in the heap without it (in place is allowed) | `NULL`, the block kept; for `n = 0`, `NULL` with the block released (glibc) |
| `aligned_alloc al n` | a fresh block at a multiple of `al` | `NULL` |
| `posix_memalign al n` | `0`, a fresh block at a multiple of `al` | an error number `≠ 0`, nothing allocated; for `n = 0`, `0` with no block |
| `malloc_usable_size p` | `NULL`: `0`; else at least the requested size; the heap unchanged | — |

Contents (zeroing, copying) are not abstract: they are stated at the machine level.

**Models** (`Model`): a hidden state, its live blocks, the load-time state and the outcomes of a
call, as for `AllocInst.AbsAlloc`. `Model.SafeOn s T` (the **POSIX-safe with invariant** strength
at signature `s` and relation `T`): some invariant holds of the load-time state, which shows no
live block, and from every state of the invariant every **valid** call of `s` has an outcome, and
every outcome is one `T` allows and keeps the invariant. After an invalid call nothing is
promised. Stronger strengths are stronger relations `T ≤ loose` (`Rel.Le`; for example a
functional relation fixing the returned address), so the strength order is the relation order.

**Non-vacuity** (`Thms`): `bottom` (every allocation fails) is `SafeOn` at every signature
(`bottom_safe`), and the success branch of `loose` is satisfiable (`loose_malloc_success`).

Mapping to the contract institution (`Silmaril.Libc.Contract`): `Sig` is a signature, `Sig.ops_mono` the signature morphisms, `loose` the sentence of
each function, `Model` the models, `SafeOn` satisfaction and `SafeOn.reduct` the satisfaction
condition along the inclusions. `AllocInst.Frag` covers `mf` and `mfcr` without the three
extensions; `AllocInst.AbsAlloc.SafeOn` is `SafeOn` with `ACall` in place of `Call`.
-/

@[expose] public section

namespace Silmaril.Libc.AllocSig

open Silmaril.Libc (Heap)

/-! ## Signatures -/

/-- The allocator functions. -/
inductive Op where
  | malloc | free | calloc | realloc | alignedAlloc | posixMemalign | usableSize
  deriving DecidableEq, Repr

/-- The C name of a function (the symbol an unprefixed allocator exports). -/
def Op.cname : Op → String
  | .malloc => "malloc"
  | .free => "free"
  | .calloc => "calloc"
  | .realloc => "realloc"
  | .alignedAlloc => "aligned_alloc"
  | .posixMemalign => "posix_memalign"
  | .usableSize => "malloc_usable_size"

/-- **The signature levels.** -/
inductive Sig where
  /-- `malloc`, `free`. -/
  | mf
  /-- and `calloc`. -/
  | mfc
  /-- and `realloc`. -/
  | mfcr
  /-- and `aligned_alloc`, `posix_memalign`, `malloc_usable_size`. -/
  | full
  deriving DecidableEq, Repr

/-- The rank of a level. -/
def Sig.rank : Sig → Nat
  | .mf => 0
  | .mfc => 1
  | .mfcr => 2
  | .full => 3

instance : LE Sig := ⟨fun a b => a.rank ≤ b.rank⟩

instance (a b : Sig) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))

/-- **The functions of a level.** -/
def Sig.ops : Sig → List Op
  | .mf => [.malloc, .free]
  | .mfc => [.malloc, .free, .calloc]
  | .mfcr => [.malloc, .free, .calloc, .realloc]
  | .full => [.malloc, .free, .calloc, .realloc, .alignedAlloc, .posixMemalign, .usableSize]

/-- The least level of a function. -/
def Op.level : Op → Sig
  | .malloc | .free => .mf
  | .calloc => .mfc
  | .realloc => .mfcr
  | .alignedAlloc | .posixMemalign | .usableSize => .full

/-- The four levels, bottom first. -/
def Sig.all : List Sig := [.mf, .mfc, .mfcr, .full]

/-! ## Calls and valid use -/

/-- **An allocator call**, its arguments as numbers. -/
inductive Call where
  | malloc (n : Nat)
  | free (p : Nat)
  | calloc (k m : Nat)
  | realloc (p n : Nat)
  | alignedAlloc (al n : Nat)
  | posixMemalign (al n : Nat)
  | usableSize (p : Nat)

/-- The function a call calls. -/
def Call.op : Call → Op
  | .malloc _ => .malloc
  | .free _ => .free
  | .calloc _ _ => .calloc
  | .realloc _ _ => .realloc
  | .alignedAlloc _ _ => .alignedAlloc
  | .posixMemalign _ _ => .posixMemalign
  | .usableSize _ => .usableSize

/-- `p` is `NULL` or the start of a live block. -/
def NullOrLive (h : Heap) (p : Nat) : Prop := p = 0 ∨ (h p).isSome

/-- `a` is a power of two. -/
def Pow2 (a : Nat) : Prop := ∃ k, a = 2 ^ k

/-- **Valid POSIX use** of a call on the live blocks `h` (module doc). -/
def Valid (h : Heap) : Call → Prop
  | .malloc _ | .calloc _ _ => True
  | .free p | .realloc p _ | .usableSize p => NullOrLive h p
  | .alignedAlloc al _ => Pow2 al
  | .posixMemalign al _ => Pow2 al ∧ 8 ∣ al

/-! ## Abstract relations -/

/-- **An abstract allocator relation**: from the live blocks `h`, the call `c` returns `r` and
the block `q` (`0`: none), leaving the live blocks `h'`. -/
abbrev Rel := Heap → Call → Heap → Nat → Nat → Prop

/-- `R` is stronger than `T` (fewer outcomes). -/
def Rel.Le (R T : Rel) : Prop := ∀ h c h' r q, R h c h' r q → T h c h' r q

/-- Failure: no block, the heap unchanged. -/
def Fails (h h' : Heap) (q : Nat) : Prop := q = 0 ∧ h' = h

/-- A fresh block `q` of `n` bytes, aligned to `al` (`al = 1`: unaligned), added to `h`. -/
def Grants (h h' : Heap) (q n al : Nat) : Prop := h.Fresh q n ∧ q % al = 0 ∧ h' = h.add q n

/-- **The POSIX-safe relation** (module doc). -/
def loose : Rel := fun h c h' r q =>
  match c with
  | .malloc n => r = q ∧ (Fails h h' q ∨ Grants h h' q n 1)
  | .calloc k m => r = q ∧ (Fails h h' q ∨ (k * m < 2 ^ 64 ∧ Grants h h' q (k * m) 1))
  | .free p => q = 0 ∧ h' = (if p = 0 then h else h.remove p)
  | .realloc p n =>
    r = q ∧ if p = 0 then Fails h h' q ∨ Grants h h' q n 1
      else Fails h h' q ∨ (n = 0 ∧ q = 0 ∧ h' = h.remove p) ∨ Grants (h.remove p) h' q n 1
  | .alignedAlloc al n => r = q ∧ (Fails h h' q ∨ Grants h h' q n al)
  | .posixMemalign al n =>
    (r ≠ 0 ∧ Fails h h' q) ∨ (r = 0 ∧ n = 0 ∧ Fails h h' q) ∨ (r = 0 ∧ Grants h h' q n al)
  | .usableSize p => q = 0 ∧ h' = h ∧ (p = 0 → r = 0) ∧ ∀ n, p ≠ 0 → h p = some n → n ≤ r

/-- **The bottom relation**: every allocation fails (`posix_memalign` with `ENOMEM`, 12),
`free` and `realloc (p, 0)` release, `malloc_usable_size` returns the requested size. -/
def never : Rel := fun h c h' r q =>
  match c with
  | .malloc _ | .calloc _ _ | .alignedAlloc _ _ => r = 0 ∧ Fails h h' q
  | .free p => q = 0 ∧ h' = (if p = 0 then h else h.remove p)
  | .realloc p n => r = 0 ∧ q = 0 ∧ h' = (if p ≠ 0 ∧ n = 0 then h.remove p else h)
  | .posixMemalign _ _ => r = 12 ∧ Fails h h' q
  | .usableSize p => q = 0 ∧ h' = h ∧ r = (if p = 0 then 0 else (h p).getD 0)

/-! ## Models and the POSIX-safe strength -/

/-- **An abstract allocator** (module doc). -/
structure Model where
  St : Type
  heap : St → Heap
  init : St
  step : St → Call → St → Nat → Nat → Prop

namespace Model

variable (A : Model)

/-- **POSIX-safe with invariant `Inv`**, at signature `s` and relation `T` (module doc). -/
structure SafeWith (s : Sig) (T : Rel) (Inv : A.St → Prop) : Prop where
  init : Inv A.init
  empty : A.heap A.init = Heap.empty
  progress : ∀ x c, Inv x → c.op ∈ s.ops → Valid (A.heap x) c → ∃ y r q, A.step x c y r q
  rel : ∀ x c y r q, Inv x → c.op ∈ s.ops → Valid (A.heap x) c → A.step x c y r q →
    T (A.heap x) c (A.heap y) r q
  inv : ∀ x c y r q, Inv x → c.op ∈ s.ops → Valid (A.heap x) c → A.step x c y r q → Inv y

/-- **POSIX-safe**: under some invariant. -/
def SafeOn (s : Sig) (T : Rel := loose) : Prop := ∃ Inv, A.SafeWith s T Inv

end Model

/-- **The bottom allocator**: its state is its live blocks; it steps as `never`. -/
def bottom : Model where
  St := Heap
  heap h := h
  init := Heap.empty
  step h c h' r q := never h c h' r q

end Silmaril.Libc.AllocSig
