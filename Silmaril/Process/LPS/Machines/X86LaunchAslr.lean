module

public import Silmaril.Process.LPS.Machines.X86Launch
public import Silmaril.Process.LPS.RunHelpers

/-! # The x86 launch windows contain Linux x86-64 ASLR placements

`X86Launch.ValidEntry` restricts the initial stack pointer, program break and mmap base
to windows (`x86LaunchBounds`, `ValidBrk`). A universal statement over valid entries
covers a real launch only if the real placement lies in these windows. This module states
the placements Linux x86-64 v6.13-v6.18 can produce for a static `ET_EXEC` executable, as
sets parameterised by the kernel configuration (`LinuxAslrConfig`), and proves each
window contains them:

* `linuxSp_mem_window`: initial `rsp` (the 16 GiB `randomize_stack_top` range, the
  `arch_align_stack` shifts, and an upper bound on the entry block's size);
* `linuxBrk_mem_window`: initial `brk` (`ELF_PAGEALIGN(elf_brk)`, plus the one-page gap
  and `randomize_page(brk, SZ_1G)` when `randomize_va_space >= 2`);
* `linuxMmapBase_mem_window`: `mm->mmap_base`, top-down (`mmap_base`) or legacy
  (`mmap_legacy_base`), for `mmap_rnd_bits <= 32`, every stack rlimit and every
  `stack_guard_gap`.

`linuxEntry_valid` assembles them: a Linux placement is a valid x86 entry whenever the
non-window conditions of `ValidEntry` hold (the entry block fits below `TASK_SIZE`; the
image lies below the 8 MiB stack reservation).

The stack window was too narrow before this check: it was riscv64's 2 GiB below the
stack top, but x86-64's `STACK_RND_MASK` is `0x3fffff` pages (16 GiB), so most x86-64
stack placements fell outside it (`old_sp_window_excluded_linux`). It is widened in
`x86LaunchBounds` (`Architecture.lean`). The brk and mmap windows already contained the
Linux ranges. The brk window's top is a Linux brk (`linuxBrk_top_attained`): it cannot be narrowed
there.

Source references are to Linux v6.18 (the v6.13 sources agree on every quantity used
here; the only edits in this range are the `clamp` spelling in `mmap_base` and the
`MMF_TOPDOWN` flag in `arch_pick_mmap_layout`).

Scope. `randomize_va_space` is the snapshot that `load_elf_binary` reads
(fs/binfmt_elf.c:1020-1022); `arch_align_stack` reads the live sysctl
(arch/x86/kernel/process.c:1021), so a concurrent write can decouple the two. The window
theorems are proved for every shift in the randomized range regardless of the
configuration (`stackTop_mem_window`), so they cover that race too. The sysctl is a
plain `proc_dointvec` (mm/memory.c:129-135): any integer is accepted, nonzero values
randomize and values above 1 also randomize brk. Four-level paging and a 64-bit task
(not `TIF_ADDR32`) are fixed by the x86 profile. The entry-block size bound covers the
direct `execve` of an ELF executable (no `binfmt_script` interpreter strings).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86Launch.Aslr

open Silmaril.Process.LPS

/-! ## Kernel configuration -/

/-- The kernel inputs that determine x86-64 launch placement. -/
structure LinuxAslrConfig where
  /-- `kernel.randomize_va_space` as snapshotted by `load_elf_binary`
  (fs/binfmt_elf.c:1020). Default 2, or 1 with `CONFIG_COMPAT_BRK` (mm/memory.c:121-126);
  `norandmaps` sets it to 0 (mm/memory.c:160). -/
  randomizeVaSpace : Int
  /-- The `ADDR_NO_RANDOMIZE` personality bit (fs/binfmt_elf.c:1021). -/
  addrNoRandomize : Bool
  /-- `vm.mmap_rnd_bits` (default `ARCH_MMAP_RND_BITS_MIN = 28`, at most
  `ARCH_MMAP_RND_BITS_MAX = 32` on 64-bit x86, arch/x86/Kconfig:354-360). -/
  mmapRndBits : Nat
  /-- `RLIMIT_STACK` soft limit at exec. -/
  rlimStack : Nat
  /-- `stack_guard_gap` in bytes (default `256 << PAGE_SHIFT`, boot parameter
  `stack_guard_gap=`, mm/mmap.c:941-954). -/
  stackGuardGap : Nat
  /-- `mmap_is_legacy()`: the `ADDR_COMPAT_LAYOUT` personality or
  `vm.legacy_va_layout` (arch/x86/mm/mmap.c:62-68). -/
  legacyLayout : Bool

/-- `PF_RANDOMIZE` (fs/binfmt_elf.c:1021-1022). -/
def LinuxAslrConfig.randomized (c : LinuxAslrConfig) : Prop :=
  c.randomizeVaSpace ≠ 0 ∧ c.addrNoRandomize = false

instance (c : LinuxAslrConfig) : Decidable c.randomized := by
  unfold LinuxAslrConfig.randomized; infer_instance

/-- brk randomization: `PF_RANDOMIZE` and `randomize_va_space > 1`
(fs/binfmt_elf.c:1332). -/
def LinuxAslrConfig.brkRandomized (c : LinuxAslrConfig) : Prop :=
  c.randomized ∧ 1 < c.randomizeVaSpace

instance (c : LinuxAslrConfig) : Decidable c.brkRandomized := by
  unfold LinuxAslrConfig.brkRandomized; infer_instance

/-- A default x86-64 distribution kernel: full randomization, 28 mmap bits, 8 MiB stack
rlimit, one-MiB guard gap, top-down layout. -/
def defaultConfig : LinuxAslrConfig := ⟨2, false, 28, 8 * 1024 * 1024, 256 * 4096, false⟩

/-- `randomize_va_space = 0` (or `ADDR_NO_RANDOMIZE`) for an otherwise given configuration. -/
def LinuxAslrConfig.unrandomized (c : LinuxAslrConfig) : LinuxAslrConfig :=
  { c with randomizeVaSpace := 0 }

/-- `STACK_TOP = TASK_SIZE_LOW = DEFAULT_MAP_WINDOW = (1 << 47) - PAGE_SIZE` for a 64-bit
task (arch/x86/include/asm/page_64_types.h:54,69); page-aligned, so `PAGE_ALIGN` in
`randomize_stack_top` is the identity. -/
def stackTop : Int := x86AddressSpace.taskSize

/-- x86-64 `STACK_RND_MASK` (arch/x86/include/asm/elf.h:328-329). -/
def stackRndMask : Nat := 0x3fffff

/-! ## The Linux placements -/

/-- The stack VMA top after `setup_arg_pages`: `randomize_stack_top(STACK_TOP)` subtracts
`r <= STACK_RND_MASK` pages (mm/util.c:341-355); `arch_align_stack` subtracts less than
8192 bytes and aligns down to 16 (arch/x86/kernel/process.c:1019-1023), and `PAGE_ALIGN`
rounds back up (fs/exec.c:635-636), a further `a <= 2` pages. Without randomization both
shifts are zero. -/
def linuxStackTops (c : LinuxAslrConfig) : Set Int :=
  {t | ∃ r a : Nat, r ≤ (if c.randomized then stackRndMask else 0) ∧
    a ≤ (if c.randomized then 2 else 0) ∧ t = stackTop - r * 4096 - a * 4096}

/-- `AT_VECTOR_SIZE = 2 * (AT_VECTOR_SIZE_ARCH + AT_VECTOR_SIZE_BASE + 1)` with
`AT_VECTOR_SIZE_ARCH <= 3` and `AT_VECTOR_SIZE_BASE = 22`
(arch/x86/include/uapi/asm/auxvec.h:15-17, include/linux/auxvec.h:7): the auxv words
`create_elf_tables` can push. -/
def atVectorWords : Nat := 2 * (3 + 22 + 1)

/-- An upper bound on the distance from the stack VMA top down to the initial `rsp`.
From the top: the pointer slot (mm/vma_exec.c:150), the `execfn` string
(fs/exec.c:1831), the environment and argument strings (fs/exec.c:1836-1840), the
`arch_align_stack` offset in `create_elf_tables` (< 8192 and 16-byte alignment,
fs/binfmt_elf.c:192), the platform string `"x86_64"` (fs/binfmt_elf.c:196-204,
arch/x86/include/asm/elf.h:221; no base platform), 16 random bytes
(fs/binfmt_elf.c:226-228), the auxv, the argv/envp/argc words and the final 16-byte
`STACK_ROUND` (fs/binfmt_elf.c:149-150, 300-303). -/
def linuxEntryReach (argv envp : List (List Byte)) (execfnLen : Nat) : Int :=
  8 + execfnLen + totalArgBytes argv + totalArgBytes envp + 8192 + 16 + 16 +
    8 * (atVectorWords + argv.length + envp.length + 3) + 16

/-- Initial `rsp` values: 16-byte aligned, below a stack top and within `reach` of it. -/
def linuxSps (c : LinuxAslrConfig) (reach : Int) : Set Int :=
  {sp | ∃ t ∈ linuxStackTops c, t - reach ≤ sp ∧ sp < t ∧ sp % 16 = 0}

/-- `elf_brk`: the maximum `p_vaddr + p_memsz` over the PT_LOAD segments, from 0
(fs/binfmt_elf.c:1033, 1240-1242; `load_bias = 0` for `ET_EXEC`). -/
def linuxElfBrk (segs : List Segment) : Int :=
  segs.foldr (fun s m => max ((s.base : Int) + s.size) m) 0

/-- `ELF_PAGEALIGN(elf_brk)` (fs/binfmt_elf.c:93, 1330; `ELF_MIN_ALIGN = PAGE_SIZE`). -/
def linuxBrkStart (segs : List Segment) : Int := pageRoundUp (linuxElfBrk segs)

/-- The initial brk. With brk randomization: the one-page gap after the bss
(fs/binfmt_elf.c:1337-1338, not taken for `ET_EXEC`'s moved-brk case) and
`randomize_page(brk, SZ_1G)` (arch/x86/kernel/process.c:1026-1032), which returns
`start + k * PAGE_SIZE` for `k < SZ_1G / PAGE_SIZE` (mm/util.c:371-387; `start` is
page-aligned and far from `ULONG_MAX`, so neither adjustment applies). -/
def linuxBrks (c : LinuxAslrConfig) (segs : List Segment) : Set Int :=
  {b | if c.brkRandomized then
      ∃ k : Nat, k < 2 ^ 30 / 4096 ∧ b = linuxBrkStart segs + 4096 + k * 4096
    else b = linuxBrkStart segs}

/-- The top-down gap of `mmap_base` (arch/x86/mm/mmap.c:82-96): the stack rlimit plus
`stack_maxrandom_size + stack_guard_gap` unless that wraps, clamped to
`[SIZE_128M, task_size / 6 * 5]`. Arithmetic is on 64-bit unsigned values. -/
def linuxGap (c : LinuxAslrConfig) : Int :=
  let pad : Int := (((if c.randomized then stackRndMask * 4096 else 0) + c.stackGuardGap) %
    2 ^ 64 : Nat)
  let rlim : Int := (c.rlimStack % 2 ^ 64 : Nat)
  let gap : Int := if rlim + pad < 2 ^ 64 then rlim + pad else rlim
  min (max gap (128 * 1024 * 1024)) (stackTop / 6 * 5)

/-- `mm->mmap_base` (arch/x86/mm/mmap.c:111-131): `arch_rnd` draws `k < 2 ^ mmap_rnd_bits`
pages when randomized (arch/x86/mm/mmap.c:70-75); the legacy base is
`__TASK_UNMAPPED_BASE(task_size) + rnd = PAGE_ALIGN(task_size / 3) + rnd`
(arch/x86/include/asm/processor.h:677, arch/x86/mm/mmap.c:101-105); the top-down base is
`PAGE_ALIGN(task_size - gap - rnd)` (arch/x86/mm/mmap.c:98), with
`task_size = task_size_64bit(0) = DEFAULT_MAP_WINDOW`. -/
def linuxMmapBases (c : LinuxAslrConfig) : Set Int :=
  {m | ∃ k : Nat, k < 2 ^ c.mmapRndBits ∧ (c.randomized ∨ k = 0) ∧
    m = if c.legacyLayout then pageRoundUp (stackTop / 3) + k * 4096
      else pageRoundUp (stackTop - linuxGap c - k * 4096)}

/-! ## The model windows -/

/-- The stack conjuncts of `X86Launch.ValidEntry`. -/
def spWindow : Set Int :=
  {sp | x86LaunchBounds.spWindowLo ≤ sp ∧ sp ≤ x86LaunchBounds.spWindowHi ∧ sp % 16 = 0}

/-- `ValidBrk`, on unsigned values: LPS's riscv64 `brk_aslr_max` window, unchanged. -/
def brkWindow (segs : List Segment) : Set Int :=
  {b | reservedTop (segmentsReserved segs) ≤ b ∧
    b ≤ reservedTop (segmentsReserved segs) + brkAslrMax ∧ b % pageSize = 0}

/-- The mmap-base conjuncts of `X86Launch.ValidEntry`. -/
def mmapBaseWindow : Set Int :=
  {m | x86LaunchBounds.mmapBaseMin ≤ m ∧ m ≤ x86LaunchBounds.mmapBaseMax ∧ m % pageSize = 0}

/-- `ValidEntry` is the snapshot check, the three windows and the two non-window
conditions. -/
theorem validEntry_iff_windows (isa : UserIsa) (snapshot : Snapshot) (en : ExecEntry)
    (inp : ProcInput) :
    ValidEntry isa snapshot en inp ↔
      ValidSnapshot isa snapshot ∧ uns en.sp ∈ spWindow ∧
        uns en.brk ∈ brkWindow snapshot.image.segments ∧ uns en.mmapBase ∈ mmapBaseWindow ∧
        entryPageTop en.sp (stackBytes snapshot.image en inp) ≤ x86AddressSpace.taskSize ∧
        (∀ segment ∈ snapshot.image.segments,
          (segment.base : Int) + segment.size ≤ uns en.sp - stackMaxSize) := by
  simp only [ValidEntry, ValidBrk, spWindow, brkWindow, mmapBaseWindow, Set.mem_ofPred_eq,
    and_assoc]

/-! ## Containment -/

/-- Every stack top shifted by at most `STACK_RND_MASK + 2` pages, with at most 2 GiB of
entry block, is in the stack window: this covers every configuration, including an
`arch_align_stack` that disagrees with the snapshotted `randomize_va_space`. -/
theorem stackTop_mem_window {r a : Nat} (hr : r ≤ stackRndMask) (ha : a ≤ 2) {reach sp : Int}
    (hreach : reach ≤ 2 * 1024 * 1024 * 1024)
    (lo : stackTop - r * 4096 - a * 4096 - reach ≤ sp)
    (hi : sp < stackTop - r * 4096 - a * 4096) (aligned : sp % 16 = 0) : sp ∈ spWindow := by
  simp only [spWindow, x86LaunchBounds, x86StackTopShiftMax, x86AddressSpace, stackTop,
    stackRndMask, Set.mem_ofPred_eq] at *
  omega

theorem linuxStackTop_bounds {c : LinuxAslrConfig} {t : Int} (h : t ∈ linuxStackTops c) :
    stackTop - x86StackTopShiftMax ≤ t ∧ t ≤ stackTop ∧ t % 4096 = 0 := by
  obtain ⟨r, a, hr, ha, rfl⟩ := h
  have hr' : r ≤ stackRndMask := by split at hr <;> omega
  have ha' : a ≤ 2 := by split at ha <;> omega
  simp only [x86StackTopShiftMax, stackTop, x86AddressSpace, stackRndMask] at *
  omega

/-- **Stack.** Every Linux initial `rsp` within 2 GiB of its stack top is in the window. -/
theorem linuxSp_mem_window (c : LinuxAslrConfig) {reach : Int}
    (hreach : reach ≤ 2 * 1024 * 1024 * 1024) : linuxSps c reach ⊆ spWindow := by
  rintro sp ⟨t, ht, lo, hi, aligned⟩
  have := linuxStackTop_bounds ht
  simp only [spWindow, x86LaunchBounds, x86AddressSpace, stackTop, x86StackTopShiftMax,
    Set.mem_ofPred_eq] at this ⊢
  omega

/-- The entry block of a valid input is far below 2 GiB (here: `PATH_MAX`-bounded
`execfn`). -/
theorem linuxEntryReach_le {argv envp : List (List Byte)} {execfnLen : Nat}
    (hargv : ValidArgv argv) (henvp : ValidEnvp envp) (hexec : execfnLen ≤ 4096) :
    linuxEntryReach argv envp execfnLen ≤ 2 * 1024 * 1024 * 1024 := by
  obtain ⟨-, argc, argBytes, -⟩ := hargv
  obtain ⟨envc, envBytes, -⟩ := henvp
  simp only [linuxEntryReach, atVectorWords]
  omega

/-- The model's reserved top is Linux's `ELF_PAGEALIGN(elf_brk)` for segments below
`TASK_SIZE`. -/
theorem reservedTop_eq_linuxBrkStart (segs : List Segment)
    (bounded : ∀ s ∈ segs, (s.base : Int) + s.size ≤ x86AddressSpace.taskSize) :
    reservedTop (segmentsReserved segs) = linuxBrkStart segs := by
  induction segs with
  | nil => rfl
  | cons s rest ih =>
    have hs := bounded s (List.mem_cons_self ..)
    have ihr := ih (fun s' m => bounded s' (List.mem_cons_of_mem _ m))
    simp only [segmentsReserved, List.map_cons, reservedTop] at ihr ⊢
    rw [ihr]
    simp only [linuxBrkStart, linuxElfBrk, List.foldr_cons, segmentReservation] at ihr ⊢
    simp only [x86AddressSpace, pageRoundUp, pageRoundDown, pageSize] at hs ⊢
    have base := s.base.zero_le
    rw [uns_zw_of_bounds (by omega) (by omega), uns_zw_of_bounds (by omega) (by omega)]
    have := ihr
    generalize List.foldr (fun s m => max ((s.base : Int) + s.size) m) 0 rest = m at *
    omega

theorem linuxElfBrk_nonneg (segs : List Segment) : 0 ≤ linuxElfBrk segs := by
  induction segs with
  | nil => exact le_refl 0
  | cons s rest ih =>
    simp only [linuxElfBrk, List.foldr_cons] at ih ⊢
    omega

theorem linuxElfBrk_le (segs : List Segment)
    (bounded : ∀ s ∈ segs, (s.base : Int) + s.size ≤ x86AddressSpace.taskSize) :
    linuxElfBrk segs ≤ x86AddressSpace.taskSize := by
  induction segs with
  | nil => simp only [linuxElfBrk, List.foldr_nil, x86AddressSpace]; omega
  | cons s rest ih =>
    simp only [linuxElfBrk, List.foldr_cons] at ih ⊢
    have := bounded s (List.mem_cons_self ..)
    have := ih (fun s' m => bounded s' (List.mem_cons_of_mem _ m))
    omega

theorem linuxBrkStart_aligned (segs : List Segment) : linuxBrkStart segs % 4096 = 0 := by
  simp only [linuxBrkStart, pageRoundUp, pageSize]; omega

/-- **brk.** Every Linux initial brk is in LPS's `brk_aslr_max` window. -/
theorem linuxBrk_mem_window (c : LinuxAslrConfig) (segs : List Segment)
    (bounded : ∀ s ∈ segs, (s.base : Int) + s.size ≤ x86AddressSpace.taskSize) :
    linuxBrks c segs ⊆ brkWindow segs := by
  intro b hb
  have aligned := linuxBrkStart_aligned segs
  simp only [brkWindow, reservedTop_eq_linuxBrkStart segs bounded, brkAslrMax, pageSize,
    Set.mem_ofPred_eq]
  simp only [linuxBrks, Set.mem_ofPred_eq] at hb
  split at hb
  · obtain ⟨k, hk, rfl⟩ := hb; omega
  · subst hb; omega

/-- The window's top is a Linux brk: the window cannot be narrowed there. -/
theorem linuxBrk_top_attained (segs : List Segment) :
    linuxBrkStart segs + brkAslrMax ∈ linuxBrks defaultConfig segs := by
  simp only [linuxBrks, Set.mem_ofPred_eq]
  have randomized : defaultConfig.brkRandomized := by decide
  simp only [randomized, ↓reduceIte]
  exact ⟨2 ^ 30 / 4096 - 1, by decide, by simp only [brkAslrMax]; omega⟩

theorem linuxGap_bounds (c : LinuxAslrConfig) :
    128 * 1024 * 1024 ≤ linuxGap c ∧ linuxGap c ≤ stackTop / 6 * 5 := by
  simp only [linuxGap, stackTop, x86AddressSpace]
  omega

/-- **mmap base.** For `mmap_rnd_bits <= 32` every Linux base, top-down or legacy, is in
the window. -/
theorem linuxMmapBase_mem_window (c : LinuxAslrConfig) (bits : c.mmapRndBits ≤ 32) :
    linuxMmapBases c ⊆ mmapBaseWindow := by
  rintro m ⟨k, hk, -, rfl⟩
  have hk' : k < 2 ^ 32 :=
    lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) bits)
  have gap := linuxGap_bounds c
  simp only [mmapBaseWindow, x86LaunchBounds, x86AddressSpace, pageRoundUp, pageSize,
    stackTop, Set.mem_ofPred_eq] at gap ⊢
  split <;> omega

/-! ## Linux placements are valid entries -/

/-- A Linux launch placement is a valid x86 entry whenever the snapshot is valid, the
entry block fits below `TASK_SIZE` and the image lies below the stack reservation. -/
theorem linuxEntry_valid (isa : UserIsa) (snapshot : Snapshot) (inp : ProcInput)
    (c : LinuxAslrConfig) (bits : c.mmapRndBits ≤ 32) {execfnLen : Nat}
    (hexec : execfnLen ≤ 4096) (hargv : ValidArgv inp.argv) (henvp : ValidEnvp inp.envp)
    (valid : ValidSnapshot isa snapshot) {sp brk mmapBase : Int}
    (hsp : sp ∈ linuxSps c (linuxEntryReach inp.argv inp.envp execfnLen))
    (hbrk : brk ∈ linuxBrks c snapshot.image.segments) (hmmap : mmapBase ∈ linuxMmapBases c)
    (draw : EntryDraw)
    (fits : entryPageTop (zw sp) (stackBytes snapshot.image ⟨zw sp, zw brk, zw mmapBase, draw⟩ inp)
      ≤ x86AddressSpace.taskSize)
    (low : ∀ segment ∈ snapshot.image.segments,
      (segment.base : Int) + segment.size ≤ sp - stackMaxSize) :
    ValidEntry isa snapshot ⟨zw sp, zw brk, zw mmapBase, draw⟩ inp := by
  have bounded := fun s m => (valid.2.2.1 s m).2.2
  have spw := linuxSp_mem_window c (linuxEntryReach_le hargv henvp hexec) hsp
  have brkw := linuxBrk_mem_window c _ bounded hbrk
  have mw := linuxMmapBase_mem_window c bits hmmap
  have rt := reservedTop_eq_linuxBrkStart _ bounded
  have rt0 : 0 ≤ linuxBrkStart snapshot.image.segments := by
    have := linuxElfBrk_nonneg snapshot.image.segments
    simp only [linuxBrkStart, pageRoundUp, pageSize]
    omega
  have rtTop : linuxBrkStart snapshot.image.segments ≤ x86AddressSpace.taskSize + 4096 := by
    simp only [linuxBrkStart]
    have := linuxElfBrk_le _ bounded
    simp only [pageRoundUp, pageSize, x86AddressSpace] at this ⊢
    omega
  simp only [spWindow, brkWindow, mmapBaseWindow, Set.mem_ofPred_eq, x86LaunchBounds,
    x86AddressSpace, x86StackTopShiftMax, brkAslrMax, pageSize] at spw brkw mw rtTop
  rw [rt] at brkw
  have usp : uns (zw sp) = sp := uns_zw_of_bounds (by omega) (by omega)
  have ubrk : uns (zw brk) = brk := uns_zw_of_bounds (by omega) (by omega)
  have umm : uns (zw mmapBase) = mmapBase := uns_zw_of_bounds (by omega) (by omega)
  rw [validEntry_iff_windows]
  refine ⟨valid, ?_, ?_, ?_, fits, ?_⟩
  · simp only [spWindow, Set.mem_ofPred_eq, x86LaunchBounds, x86AddressSpace,
      x86StackTopShiftMax, usp]
    omega
  · simp only [brkWindow, Set.mem_ofPred_eq, rt, brkAslrMax, pageSize, ubrk]
    omega
  · simp only [mmapBaseWindow, Set.mem_ofPred_eq, x86LaunchBounds, x86AddressSpace, pageSize,
      umm]
    omega
  · intro segment mem
    rw [usp]
    exact low segment mem

/-! ## Unrandomized launches and controls -/

theorem unrandomized_not_randomized (c : LinuxAslrConfig) : ¬ c.unrandomized.randomized :=
  fun h => h.1 rfl

/-- `randomize_va_space = 0`: the stack top is `STACK_TOP`, a single point of the window. -/
theorem linuxStackTops_unrandomized (c : LinuxAslrConfig) :
    linuxStackTops c.unrandomized = {stackTop} := by
  ext t
  simp only [linuxStackTops, unrandomized_not_randomized c, ↓reduceIte, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, a, hr, ha, rfl⟩; omega
  · rintro rfl; exact ⟨0, 0, le_refl _, le_refl _, by omega⟩

/-- `randomize_va_space = 0`: brk is `ELF_PAGEALIGN(elf_brk)`. -/
theorem linuxBrks_unrandomized (c : LinuxAslrConfig) (segs : List Segment) :
    linuxBrks c.unrandomized segs = {linuxBrkStart segs} := by
  ext b
  have : ¬ c.unrandomized.brkRandomized := fun h => unrandomized_not_randomized c h.1
  simp only [linuxBrks, this, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_singleton_iff]

/-- `randomize_va_space = 0`: a single mmap base. -/
theorem linuxMmapBases_unrandomized (c : LinuxAslrConfig) :
    linuxMmapBases c.unrandomized =
      {if c.legacyLayout then pageRoundUp (stackTop / 3)
        else pageRoundUp (stackTop - linuxGap c.unrandomized)} := by
  ext m
  simp only [linuxMmapBases, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, -, hk, rfl⟩
    have : k = 0 := hk.resolve_left (unrandomized_not_randomized c)
    subst this
    simp [LinuxAslrConfig.unrandomized]
  · rintro rfl
    exact ⟨0, Nat.two_pow_pos _, Or.inr rfl, by
      simp [LinuxAslrConfig.unrandomized]⟩

/-- The unrandomized top-down base is the window's upper end `TASK_SIZE - 128 MiB` under
the default stack rlimit and guard gap. -/
theorem defaultConfig_unrandomized_mmapBase :
    linuxMmapBases defaultConfig.unrandomized = {x86LaunchBounds.mmapBaseMax} := by
  rw [linuxMmapBases_unrandomized]
  congr 1

/-- The pre-widening stack window (riscv64's 2 GiB below `TASK_SIZE`). -/
def oldSpWindowLo : Int := x86AddressSpace.taskSize - 2 * 1024 * 1024 * 1024

/-- The old window excluded real launches: at the default configuration, a stack top
16 GiB below `STACK_TOP` gives an `rsp` far below its bottom. -/
theorem old_sp_window_excluded_linux :
    ∃ sp ∈ linuxSps defaultConfig 4096, sp < oldSpWindowLo := by
  refine ⟨stackTop - stackRndMask * 4096 - 16, ⟨stackTop - stackRndMask * 4096,
    ⟨stackRndMask, 0, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [defaultConfig, LinuxAslrConfig.randomized, oldSpWindowLo, stackTop,
      stackRndMask, x86AddressSpace] <;> decide

end Silmaril.Process.LPS.Machines.X86Launch.Aslr
