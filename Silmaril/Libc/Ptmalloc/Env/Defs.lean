module

public import Silmaril.Libc.Ptmalloc.Rep.Defs

/-!
# ptmalloc: the surroundings

Everything the allocator's code reads or writes that is **not** heap state: `__curbrk`, the
process flags (`__libc_single_threaded`, `__libc_initial`, `__always_fail_morecore`),
`prctl_supported`, `mp_`'s constants (an untuned process: the `Config` defaults), the arena
list's locks and `narenas_limit` (W17/M6), and the stack-protector canary. No arch is assumed:
the single-thread flag's cell and the canary's address are data (`EnvAddrs`). They form one small
invariant `SurrInv` over their own fragment `envFrag`, disjoint from the heap's.

**Why separate**: a model fix in the surroundings (M4's tunable write width, M8's vDSO post,
W12's `__curbrk`, W13's `prctl_supported`) changes `Surr`/`envFrag`/`SurrInv` or a callee
contract in `Silmaril.Libc.Ptmalloc.Sim`, and no heap proof: heap proofs see the surroundings only
through `envFrag_frame` and `surrInv_step` (both proved here).

Callee contracts (`memset`, `memcpy`, `__tunable_get_val`, the vDSO `clock_gettime`) are x86
facts and live in `Silmaril.Libc.Ptmalloc.Sim` (`Callee`), parametric in their write sets, so
M4/M8-style changes stay there too.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

open Silmaril.Data

/-- **The surroundings' state.** -/
structure Surr where
  /-- `__curbrk` (W12: 0 before the first `sbrk`, then the break). -/
  curbrk : Nat
  singleThreaded : Bool
  libcInitial : Bool := true
  alwaysFailMorecore : Bool := false
  /-- `prctl_supported` (W13; 2.39+). -/
  prctlSupported : Nat := 1
  /-- `narenas_limit` (M6: 0, not yet computed). -/
  narenasLimit : Nat := 0
  /-- `free_list_lock`, `list_lock` (M6: free between calls). -/
  freeListLock : Nat := 0
  listLock : Nat := 0
  /-- The stack-protector canary's value (its address is per arch: x86-64 `%fs:0x28`,
  riscv64/arm64 ld.so's `__stack_chk_guard`). -/
  canary : Nat
  deriving DecidableEq, Repr

/-- **The surroundings' addresses** (relocated statics, and the canary at `%fs:0x28`). -/
structure EnvAddrs where
  curbrk : Nat
  /-- The single-thread flag's cell: address, width, and its value when single-threaded and when
  not (x86-64: `__libc_single_threaded`, 1 byte, 1/0; riscv64: `THREAD_SELF->header.multiple_threads`
  at `tp - 0x760`, 4 bytes, 0/1). -/
  singleAddr : Nat
  singleWidth : Nat := 1
  singleVal : Nat := 1
  multiVal : Nat := 0
  libcInitial : Nat
  alwaysFailMorecore : Nat
  prctlSupported : Option Nat
  narenasLimit : Nat
  freeListLock : Nat
  listLock : Nat
  canary : Nat
  mp : Nat
  deriving DecidableEq, Repr

section
variable (C : Config) (L : Layout) (E : EnvAddrs)

/-- **`mp_`'s constants** in an untuned process (the `Config` defaults). -/
def mpConstFrag : Frag :=
  let f := fun o => E.mp + o
  [Cell.w (f L.mpTopPad) C.topPad, Cell.w (f L.mpArenaTest) C.arenaTest, Cell.w (f L.mpArenaMax) 0,
   ⟨f L.mpNMmapsMax, 4, C.mmapMax⟩,
   Cell.w (f L.mpTcacheBins) C.tcacheBins, Cell.w (f L.mpTcacheMaxBytes) C.tcacheMaxBytes,
   Cell.w (f L.mpTcacheCount) C.tcacheCount, Cell.w (f L.mpTcacheUnsortedLimit) C.tcacheUnsortedLimit]

/-- **The surroundings' fragment.** -/
def envFrag (s : Surr) : Frag :=
  [Cell.w E.curbrk s.curbrk,
   ⟨E.singleAddr, E.singleWidth, if s.singleThreaded then E.singleVal else E.multiVal⟩,
   ⟨E.libcInitial, 1, if s.libcInitial then 1 else 0⟩,
   ⟨E.alwaysFailMorecore, 1, if s.alwaysFailMorecore then 1 else 0⟩,
   Cell.w E.narenasLimit s.narenasLimit, ⟨E.freeListLock, 4, s.freeListLock⟩,
   ⟨E.listLock, 4, s.listLock⟩, Cell.w E.canary s.canary] ++
  (match E.prctlSupported with
   | some a => [⟨a, 4, s.prctlSupported⟩]
   | none => []) ++
  mpConstFrag C L E

/-- **The surroundings' invariant**, relative to the kernel and the shared heap state: `__curbrk`
is 0 before the first `sbrk` and the break after (W12); an untuned, initial libc whose `brk`
works; the arena-list locks free and `narenas_limit` unset (M6). -/
def SurrInv (s : Surr) (k : KernelSt) (sh : SharedSt) : Prop :=
  (s.curbrk = 0 ∨ s.curbrk = k.brk) ∧ (sh.mm.mp.sbrkBase ≠ 0 → s.curbrk = k.brk) ∧
  s.libcInitial = true ∧ s.alwaysFailMorecore = false ∧
  s.freeListLock = 0 ∧ s.listLock = 0 ∧ s.narenasLimit = 0

instance (s : Surr) (k : KernelSt) (sh : SharedSt) : Decidable (SurrInv s k sh) := by
  unfold SurrInv; exact inferInstance

/-- **The surroundings' frame rule**: a run that writes outside `envFrag`'s bytes keeps it. -/
theorem envFrag_frame {s : Surr} {v v' : MemView} (h : (envFrag C L E s).Holds v)
    (hag : v.AgreeOn v' (envFrag C L E s).bytes) : (envFrag C L E s).Holds v' :=
  Frag.holds_frame h hag

end

/-- **The surroundings follow the kernel**: after a body moved the break, setting `__curbrk` to
the new break keeps `SurrInv` (W12). -/
theorem surrInv_step {s : Surr} {k k' : KernelSt} {sh sh' : SharedSt} (h : SurrInv s k sh) :
    SurrInv { s with curbrk := k'.brk } k' sh' :=
  ⟨.inr rfl, fun _ => rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end Silmaril.Libc.Ptmalloc
