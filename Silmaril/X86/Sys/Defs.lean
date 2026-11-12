module

public import Silmaril.X86.Extends.Defs

/-!
# `Sys`: a machine with Linux memory system calls

`Sys.isa I hl` adds a **`syscall` step** to any segment-VC machine `I`. On a state where `I`
has no step and the program counter holds the two bytes `0F 05` (executable), the machine
takes one step of a **functional model of the Linux x86-64 kernel** for the system calls that
a memory allocator makes. Every `I` step is a step of the new machine (`Sys.extends`), so
every run, triple and contract proved on `I` lifts unchanged.

## The kernel's choices are an oracle in the state

The state (`SysState σ`) is an `I` state, the kernel's own memory-management state
(`Kernel`: the program break) and an **answer stream** `ans : Nat → Answer`. The `n`-th system
call reads `ans 0` and the state keeps `fun k => ans (k + 1)`, as the time-stamp oracle of the
`rdtsc` layer does. A statement about every state therefore holds for every sequence of kernel
decisions, and the step is still a function, so `SegVC` and the `Isa.Extends` lenses apply. An
answer says

* whether the kernel **refuses** the call (`refuse`), and with which error (`err`): the "may
  fail" outcome of every modelled call (no memory, a resource limit, an interrupted or
  non-blocking `getrandom`, an RLIMIT on the break);
* the **address** `mmap` picks (`addr`); a pick that is misaligned, above the user address
  limit or overlapping a mapping is a refusal with `ENOMEM`;
* the value of `r11` after the call (`r11`; Linux stores `RFLAGS` there, whose encoding the
  core does not model);
* the bytes `getrandom` returns (`rnd`).

## The calls (x86-64 numbers, `arch/x86/entry/syscalls/syscall_64.tbl`)

Arguments in `rdi rsi rdx r10 r8 r9`, the number in `rax`; the result (or `-errno`) in `rax`,
`rcx` gets the address after `syscall`, `r11` the oracle value; nothing else changes.

| call | nr | model |
|---|---|---|
| `mmap` | 9 | anonymous private mappings only (`flags` is `MAP_PRIVATE|MAP_ANONYMOUS`, optionally `MAP_NORESERVE`; `off = 0`; `fd` is ignored, as Linux ignores it for `MAP_ANONYMOUS`); length 0 is `EINVAL`; the pages are zero |
| `mprotect` | 10 | changes the permissions of whole mapped pages; `ENOMEM` if a page is unmapped |
| `munmap` | 11 | removes the pages from the mapping list |
| `brk` | 12 | Linux's `brk`: below `start_brk` it reports the break; shrinking unmaps; growing maps zero pages unless refused or overlapping |
| `mremap` | 25 | `flags` 0 or `MREMAP_MAYMOVE`: shrink in place, grow in place, or move to the answer's address with the bytes copied |
| `madvise` | 28 | `MADV_DONTNEED` (4) zeroes the (private, anonymous) pages; other advice is a no-op |
| `prctl` | 157 | `PR_SET_VMA` only (naming a mapping): no effect |
| `getrandom` | 318 | writes `n` oracle bytes to the buffer and returns `n` |

Anything else (another number, an unsupported flag, a `getrandom` buffer the kernel cannot
write) has **no step**: a statement proved on this machine never reaches it. In particular
`futex`, signals, `exit` and the abort path of the allocator are not modelled.

## What is assumed

This is a model of the kernel's interface, not a proof about Linux. The model admits every
behaviour of Linux for these calls that it covers (each Linux outcome is the model's step for
some answer), except in three places where it is coarser:

* a refusal changes nothing (Linux may have partially done the work only for `munmap` and
  `mprotect` across several mappings, which a refusal here does not represent);
* `getrandom` writes all `n` bytes or none (Linux may return fewer only when interrupted
  for requests above 256 bytes);
* `MADV_DONTNEED` is applied to private anonymous memory (file mappings are not modelled).

Pages are 4096 bytes; the user address space ends at `2^47 - 4096`.
-/

@[expose] public section

namespace Silmaril.X86.Sys

open Silmaril.X86 (State Word Byte Reg)
open Silmaril.Process (Memory Region Permissions)
open Silmaril.X86.SegVC (Isa)

/-! ## The kernel -/

/-- The page size. -/
def page : Nat := 4096

/-- `n` rounded up to a page boundary (`PAGE_ALIGN`). -/
def pageUp (n : Nat) : Nat := (n + (page - 1)) / page * page

/-- The end of the user address space (`TASK_SIZE` with 4-level paging). -/
def userTop : Nat := 2 ^ 47 - page

/-- The kernel's memory-management state: `mm->start_brk` and `mm->brk`. -/
structure Kernel where
  brkStart : Nat
  brk : Nat
  deriving DecidableEq, Repr

/-- **One answer of the kernel** to one system call. -/
structure Answer where
  /-- The call is refused with error `err + 1`. -/
  refuse : Bool
  err : Fin 4095
  /-- The address `mmap` picks. -/
  addr : Nat
  /-- `r11` after the call. -/
  r11 : Word
  /-- The bytes `getrandom` delivers. -/
  rnd : Nat → Byte

/-! ## Mappings -/

/-- `[a, a + n)` with the parts of each region outside it (`munmap`'s effect on the list). -/
def cut (rs : List Region) (a n : Nat) : List Region :=
  rs.flatMap fun r =>
    (if r.base < a then [⟨r.base, min (r.base + r.size) a - r.base, r.permissions⟩] else []) ++
    (if a + n < r.base + r.size then
      [⟨max r.base (a + n), r.base + r.size - max r.base (a + n), r.permissions⟩] else [])

/-- No region meets `[a, a + n)`. -/
def unmapped (rs : List Region) (a n : Nat) : Bool :=
  rs.all fun r => decide (r.base + r.size ≤ a ∨ a + n ≤ r.base ∨ r.size = 0)

/-- Every byte of `[a, a + n)` lies in some region (whatever its permissions). -/
def mappedAll (rs : List Region) (a n : Nat) : Bool :=
  (List.range n).all fun i => rs.any fun r => decide (r.Contains (a + i))

/-- The permissions of a `PROT_*` value. -/
def protOf (prot : Nat) : Permissions := ⟨prot % 2 = 1, prot / 2 % 2 = 1, prot / 4 % 2 = 1⟩

/-- Map `[a, a + n)` with permissions `p`, zero-filled. -/
def mapZero (m : Memory) (a n : Nat) (p : Permissions) : Memory :=
  ⟨⟨a, n, p⟩ :: cut m.regions a n, Memory.install m.bytes a (List.replicate n 0)⟩

/-- Read-write, not executable. -/
def rw : Permissions := ⟨true, true, false⟩

/-! ## The calls -/

/-- The value `-e` of an error `e`. -/
def neg (e : Nat) : Word := 0 - BitVec.ofNat 64 e

/-- `EINVAL`, `ENOMEM`. -/
def EINVAL : Nat := 22
def ENOMEM : Nat := 12

/-- A result: the value in `rax`, the new memory and kernel state. -/
abbrev Out := Word × Memory × Kernel

/-- `brk(addr)` (`mm/mmap.c`, `SYSCALL_DEFINE1(brk)`): the result is the new break. -/
def brk (m : Memory) (k : Kernel) (a : Answer) (addr : Nat) : Out :=
  let cur := BitVec.ofNat 64 k.brk
  if addr < k.brkStart then (cur, m, k)
  else
    let nb := pageUp addr
    let ob := pageUp k.brk
    if nb = ob then (BitVec.ofNat 64 addr, m, { k with brk := addr })
    else if addr ≤ k.brk then
      (BitVec.ofNat 64 addr, { m with regions := cut m.regions nb (ob - nb) }, { k with brk := addr })
    else if a.refuse || !decide (nb ≤ userTop) || !unmapped m.regions ob (nb - ob) then (cur, m, k)
    else (BitVec.ofNat 64 addr, mapZero m ob (nb - ob) rw, { k with brk := addr })

/-- The flags `mmap` supports: `MAP_PRIVATE|MAP_ANONYMOUS`, optionally `MAP_NORESERVE`. -/
def mmapFlagsOk (flags : Nat) : Bool := flags = 0x22 || flags = 0x4022

/-- `mmap(addr, len, prot, flags, fd, off)` for anonymous private mappings; `none` outside the
model. The hint `addr` is ignored (the answer picks the address), and so is `fd`. -/
def mmap (m : Memory) (k : Kernel) (a : Answer) (len prot flags _fd off : Word) : Option Out :=
  if !mmapFlagsOk flags.toNat || off ≠ 0 || 7 < prot.toNat then none
  else if len = 0 then some (neg EINVAL, m, k)
  else if a.refuse then some (neg (a.err.val + 1), m, k)
  else
    let n := pageUp len.toNat
    if a.addr % page = 0 ∧ 0 < a.addr ∧ a.addr + n ≤ userTop ∧ unmapped m.regions a.addr n then
      some (BitVec.ofNat 64 a.addr, mapZero m a.addr n (protOf prot.toNat), k)
    else some (neg ENOMEM, m, k)

/-- `munmap(addr, len)`. -/
def munmap (m : Memory) (k : Kernel) (a : Answer) (addr len : Word) : Out :=
  if addr.toNat % page ≠ 0 || len = 0 then (neg EINVAL, m, k)
  else if a.refuse then (neg (a.err.val + 1), m, k)
  else (0, { m with regions := cut m.regions addr.toNat (pageUp len.toNat) }, k)

/-- `mprotect(addr, len, prot)`. -/
def mprotect (m : Memory) (k : Kernel) (a : Answer) (addr len prot : Word) : Out :=
  let n := pageUp len.toNat
  if addr.toNat % page ≠ 0 || 7 < prot.toNat then (neg EINVAL, m, k)
  else if n = 0 then (0, m, k)
  else if !mappedAll m.regions addr.toNat n then (neg ENOMEM, m, k)
  else if a.refuse then (neg (a.err.val + 1), m, k)
  else
    let rs := ⟨addr.toNat, n, protOf prot.toNat⟩ :: cut m.regions addr.toNat n
    (0, { m with regions := rs }, k)

/-- `madvise(addr, len, advice)`: `MADV_DONTNEED` zeroes the pages. -/
def madvise (m : Memory) (k : Kernel) (a : Answer) (addr len advice : Word) : Out :=
  let n := pageUp len.toNat
  if addr.toNat % page ≠ 0 then (neg EINVAL, m, k)
  else if a.refuse then (neg (a.err.val + 1), m, k)
  else if advice.toNat = 4 then
    if mappedAll m.regions addr.toNat n then
      (0, { m with bytes := Memory.install m.bytes addr.toNat (List.replicate n 0) }, k)
    else (neg ENOMEM, m, k)
  else (0, m, k)

/-- `getrandom(buf, n, flags)`; `none` if the buffer is not writable. -/
def getrandom (m : Memory) (k : Kernel) (a : Answer) (buf n flags : Word) : Option Out :=
  if 7 < flags.toNat then some (neg EINVAL, m, k)
  else if a.refuse then some (neg (a.err.val + 1), m, k)
  else
    match m.writeBytes buf.toNat ((List.range n.toNat).map a.rnd) with
    | some m' => some (n, m', k)
    | none => none

/-- `mremap(old, oldlen, newlen, flags)` with `flags` 0 or `MREMAP_MAYMOVE` (1): shrink in
place, grow in place (the answer's address is `old`), or move to the answer's address (copying
the bytes); `none` outside the model or for unbacked bytes. -/
def mremap (m : Memory) (k : Kernel) (a : Answer) (old oldlen newlen flags : Word) : Option Out :=
  let o := old.toNat
  let on := pageUp oldlen.toNat
  let nn := pageUp newlen.toNat
  if 1 < flags.toNat then none
  else if o % page ≠ 0 || newlen = 0 then some (neg EINVAL, m, k)
  else match m.regions.find? (·.Contains o) with
  | none => some (neg 14, m, k)
  | some r =>
    if !mappedAll m.regions o on then some (neg 14, m, k)
    else if a.refuse then some (neg (a.err.val + 1), m, k)
    else if nn ≤ on then
      some (old, { m with regions := cut m.regions (o + nn) (on - nn) }, k)
    else if a.addr = o then
      if o + nn ≤ userTop ∧ unmapped m.regions (o + on) (nn - on) then
        some (old, mapZero m (o + on) (nn - on) r.permissions, k)
      else some (neg ENOMEM, m, k)
    else if flags.toNat = 1 ∧ a.addr % page = 0 ∧ 0 < a.addr ∧ a.addr + nn ≤ userTop ∧
        unmapped m.regions a.addr nn then
      match Memory.readBacking m.bytes o on with
      | none => none
      | some bs =>
        let m1 := mapZero m a.addr nn r.permissions
        some (BitVec.ofNat 64 a.addr,
          ⟨cut m1.regions o on, Memory.install m1.bytes a.addr bs⟩, k)
    else some (neg ENOMEM, m, k)

/-- `PR_SET_VMA`. -/
def prSetVma : Nat := 0x53564d41

/-- **The kernel's answer to the request in `c`** (number in `rax`), or `none` outside the
model. -/
def call (c : State) (m : Memory) (k : Kernel) (a : Answer) : Option Out :=
  let nr := (c.read .rax).toNat
  let a0 := c.read .rdi
  let a1 := c.read .rsi
  let a2 := c.read .rdx
  let a3 := c.read .r10
  let a4 := c.read .r8
  let a5 := c.read .r9
  if nr = 9 then mmap m k a a1 a2 a3 a4 a5
  else if nr = 10 then some (mprotect m k a a0 a1 a2)
  else if nr = 11 then some (munmap m k a a0 a1)
  else if nr = 12 then some (brk m k a a0.toNat)
  else if nr = 25 then mremap m k a a0 a1 a2 a3
  else if nr = 28 then some (madvise m k a a0 a1 a2)
  else if nr = 157 then
    if a0.toNat = prSetVma then
      some (if a.refuse then neg (a.err.val + 1) else 0, m, k)
    else none
  else if nr = 318 then getrandom m k a a0 a1 a2
  else none

/-- The core after the call: the result in `rax`, the return address in `rcx`, `r11`. -/
def retCore (c : State) (rax r11 : Word) : State :=
  { ((c.write .rax rax).write .rcx (c.rip + 2)).write .r11 r11 with rip := c.rip + 2 }

/-! ## The machine -/

/-- **The state**: a state of the underlying machine, the kernel and the answer stream. -/
structure SysState (σ : Type) where
  s : σ
  k : Kernel
  ans : Nat → Answer

variable {σ : Type}

/-- The bytes at the program counter are `syscall` (`0F 05`), fetched for execution. -/
def atSyscall (m : Memory) (rip : Word) : Bool := m.fetchBytes rip.toNat 2 == some [0x0F, 0x05]

/-- **The `syscall` step** of a state of `I`. -/
def sysStep (I : Isa σ) (x : SysState σ) : Option (SysState σ) :=
  let c := I.core x.s
  let m := I.mem x.s
  if atSyscall m c.rip then
    (call c m x.k (x.ans 0)).map fun (r, m', k') =>
      ⟨I.upd x.s (retCore c r (x.ans 0).r11) m', k', fun n => x.ans (n + 1)⟩
  else none

/-- **One step**: `I`'s step, and where `I` has none, the `syscall` step. -/
def step (I : Isa σ) (x : SysState σ) : Option (SysState σ) :=
  match I.step x.s with
  | some t => some { x with s := t }
  | none => sysStep I x

/-- **The machine with system calls.** `hl` says that `I`'s invariant survives a change of core
and memory (true for the machines whose invariant is `True`). -/
@[reducible] def isa (I : Isa σ) (hl : ∀ s c m, I.live s → I.live (I.upd s c m)) :
    Isa (SysState σ) where
  Instr := I.Instr
  instDecEq := I.instDecEq
  decode := I.decode
  exec := I.exec
  core x := I.core x.s
  mem x := I.mem x.s
  upd x c m := { x with s := I.upd x.s c m }
  core_upd x c m := I.core_upd x.s c m
  mem_upd x c m := I.mem_upd x.s c m
  upd_self x := by simp [I.upd_self]
  ok := I.ok
  live x := I.live x.s
  step := step I
  live_step := by
    intro x y hx h
    unfold step at h
    split at h
    · cases h; exact I.live_step hx (by assumption)
    · unfold sysStep at h
      dsimp only at h
      by_cases hs : atSyscall (I.mem x.s) (I.core x.s).rip = true
      · simp only [hs, ↓reduceIte] at h
        obtain ⟨⟨r, m', k'⟩, _, rfl⟩ := Option.map_eq_some_iff.mp h
        exact hl _ _ _ hx
      · simp only [hs] at h; cases h
  step_of := by
    intro x base code o l i c m hlive hl' hrip hfit hdec hx hok
    have h := I.step_of hlive hl' hrip hfit hdec hx hok
    simp [step, h]

/-- **`Sys.isa I` extends `I`** along `x ↦ x.s` (the kernel and the answers are the frame). -/
@[reducible] def «extends» (I : Isa σ) (hl : ∀ s c m, I.live s → I.live (I.upd s c m)) :
    I.Extends (isa I hl) where
  view x := x.s
  put x s := { x with s := s }
  view_put _ _ := rfl
  put_put _ _ _ := rfl
  put_view _ := rfl
  core _ := rfl
  mem _ := rfl
  upd _ _ _ := rfl
  live _ h := h
  step h := by simp [step, h]

end Silmaril.X86.Sys
