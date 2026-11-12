module

public import Silmaril.Libc.Ptmalloc.Config.Defs

/-!
# ptmalloc component: the kernel

The break, the anonymous mappings, and the **kernel's answers as data** (`KOracle`): the
algorithm model is a deterministic, executable function of the state, and every theorem
quantifies over the oracle (every refusal pattern). `ask` consumes one answer.

The requests (`sbrk`, `shrink`, `mmap`, `munmap`, `mremap`, `mprotect`) are **validity-checked**:
an answer the real kernel could not give (a mapping that overlaps another one or the break
area, a misaligned or null address, an address space beyond `userTop` bytes) counts as a
refusal. So the theorems need no assumption on the oracle, and a difftest replay of real
answers never hits the check. One modelling restriction: nothing but the allocator moves the
break (no foreign `sbrk`), so a granted `sbrk` returns the current break.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- One kernel answer to a memory request. -/
inductive KAns where
  /-- Granted (for `mmap`/`mremap`: at this address). -/
  | ok (addr : Nat)
  /-- Refused (`ENOMEM`). -/
  | refuse
  deriving DecidableEq, Repr

/-- **The kernel's answers**, consulted in order. -/
structure KOracle where
  answer : Nat → KAns

/-- **The kernel part.** -/
structure KernelSt where
  brkStart : Nat
  brk : Nat
  /-- The anonymous mappings (address, length). -/
  maps : List (Nat × Nat) := []
  asked : Nat := 0
  oracle : KOracle

namespace KernelSt

/-- The size of the user address space (x86-64 and riscv64 Sv48, arm64 48-bit VA: `2 ^ 47`). -/
def userTop : Nat := 2 ^ 47

variable (k : KernelSt)

/-- Consume the next answer. -/
def ask : KAns × KernelSt := (k.oracle.answer k.asked, { k with asked := k.asked + 1 })

/-- The bytes the process has from the kernel: the break area and the mappings. -/
def total : Nat := (k.brk - k.brkStart) + (k.maps.map (·.2)).sum

/-- `[a, a + n)` overlaps no mapping. -/
def Free (a n : Nat) : Prop := ∀ m ∈ k.maps, a + n ≤ m.1 ∨ m.1 + m.2 ≤ a

instance (a n : Nat) : Decidable (k.Free a n) := by unfold Free; exact inferInstance

/-- **`sbrk (incr)`**, `incr ≥ 0`: the old break, or `none` (refused). `sbrk (0)` asks nothing. -/
def sbrk (incr : Nat) : Option Nat × KernelSt :=
  if incr = 0 then (some k.brk, k) else
  match k.ask with
  | (.refuse, k) => (none, k)
  | (.ok _, k) =>
    if k.brk + incr ≤ userTop ∧ k.Free k.brk incr ∧ k.total + incr ≤ userTop then
      (some k.brk, { k with brk := k.brk + incr })
    else (none, k)

/-- **`sbrk (-dec)`**: shrink the break (`systrim`); `none` if refused. -/
def shrink (dec : Nat) : Option Unit × KernelSt :=
  match k.ask with
  | (.refuse, k) => (none, k)
  | (.ok _, k) =>
    if k.brkStart + dec ≤ k.brk then (some (), { k with brk := k.brk - dec }) else (none, k)

/-- `[a, a + n)` is a place the kernel may map `n` bytes at, aligned to `al`. -/
def Placeable (al a n : Nat) : Prop :=
  a ≠ 0 ∧ a % al = 0 ∧ a + n ≤ userTop ∧ k.Free a n ∧ (a + n ≤ k.brkStart ∨ k.brk ≤ a) ∧
    k.total + n ≤ userTop

instance (al a n : Nat) : Decidable (k.Placeable al a n) := by unfold Placeable; exact inferInstance

/-- **`mmap (0, n, …)`** of `n` bytes aligned to `al` (a page, or `HEAP_MAX_SIZE` for a
non-main arena's heap): the address, or `none`. -/
def mmap (al n : Nat) : Option Nat × KernelSt :=
  match k.ask with
  | (.refuse, k) => (none, k)
  | (.ok a, k) =>
    if k.Placeable al a n then (some a, { k with maps := (a, n) :: k.maps }) else (none, k)

/-- **`munmap (a, n)`**. -/
def munmap (a n : Nat) : KernelSt := { k with maps := k.maps.erase (a, n) }

/-- **`mremap (a, n, n', MREMAP_MAYMOVE)`**: the new address, or `none`. -/
def mremap (al a n n' : Nat) : Option Nat × KernelSt :=
  match k.ask with
  | (.refuse, k) => (none, k)
  | (.ok a', k) =>
    let k₀ := k.munmap a n
    if k₀.Placeable al a' n' then (some a', { k with maps := (a', n') :: k₀.maps }) else (none, k)

/-- **`mprotect`** of more of a reserved mapping (a non-main heap's `grow_heap`): granted or not. -/
def mprotect : Bool × KernelSt :=
  match k.ask with
  | (.refuse, k) => (false, k)
  | (.ok _, k) => (true, k)

end KernelSt

/-- Byte `x` is the process's memory: in the break area or in a mapping. -/
def KernelSt.Has (k : KernelSt) (x : Nat) : Prop :=
  (k.brkStart ≤ x ∧ x < k.brk) ∨ ∃ m ∈ k.maps, m.1 ≤ x ∧ x < m.1 + m.2

/-- Every byte of the range `r = (start, length)` is the process's memory. -/
def KernelSt.Covers (k : KernelSt) (r : Nat × Nat) : Prop :=
  ∀ x, r.1 ≤ x → x < r.1 + r.2 → k.Has x

/-- **The kernel's invariant**: the break area and the mappings are inside the user address
space and pairwise apart. -/
structure KernelWF (k : KernelSt) : Prop where
  brk : k.brkStart ≤ k.brk
  total : k.total ≤ KernelSt.userTop
  apart : k.maps.Pairwise fun m m' => m.1 + m.2 ≤ m'.1 ∨ m'.1 + m'.2 ≤ m.1
  brkApart : ∀ m ∈ k.maps, m.1 + m.2 ≤ k.brkStart ∨ k.brk ≤ m.1

end Silmaril.Libc.Ptmalloc
