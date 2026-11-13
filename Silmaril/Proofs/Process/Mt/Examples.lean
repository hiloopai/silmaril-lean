module

public import Silmaril.Process.Mt.X86.Defs
public meta import Silmaril.Process.Mt.X86.Defs
public meta import Silmaril.Process.Mt.Prim.Defs
public meta import Silmaril.X86.Basic

/-!
# Examples: runs of the multithreaded x86 process

Three small x86-64 programs, hand-assembled, run with the executable SC scheduler
(`Mt.X86.run`; every run of it is a run of `MtProc X sc Prim.table (Base.none Unit)` by
`Mt.X86.run_sound`). Checked with `#guard` (compiled evaluation; the instruction decoder is
too large for kernel `decide`).

1. **Two threads increment a counter under a mutex primitive.** Each thread runs
   `call LOCK; mov rax, [rbx]; add rax, 1; mov [rbx], rax; call UNLOCK; exit(0)`, with
   `LOCK`/`UNLOCK` bound to the `mutexLock`/`mutexUnlock` primitives. Interleaved
   schedules end with the counter at `2` and the process exited with status `0`; while one
   thread holds the lock, the other cannot take the `LOCK` step.
2. **A futex handoff.** Thread 1 waits (`FUTEX_WAIT_PRIVATE`) while a flag word is `0`;
   thread 2 sets the flag and wakes one waiter (`FUTEX_WAKE_PRIVATE`); thread 1 then reads
   the flag and calls `exit_group (flag)`. If thread 2 goes first, the wait returns `-EAGAIN`.
   Either way the process exits with status `1`.
3. **`clone`.** A thread calls `clone` with glibc's `pthread_create` flags, a new stack and a
   TLS base; the child has `rsp` = the new stack, `fsBase` = the TLS base, `rax = 0`; the
   parent gets the child's tid in `rax` and at `ptid`; the process is in multithreaded mode.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Examples

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Process (Memory Region)
open Silmaril.Process.Mt
open Silmaril.Process.Mt.X86

/-! ## Set-up -/

/-- A register file with the listed values, zero elsewhere. -/
def regs (vs : List (Reg × Word)) : Silmaril.Machine.RegisterFile Reg Word :=
  fun r => ((vs.find? (·.1 == r)).map (·.2)).getD 0

/-- A thread core at `rip` with the listed registers. -/
def core (rip : Nat) (vs : List (Reg × Word)) : Core :=
  ⟨{ regs := regs vs, rip := BitVec.ofNat 64 rip, flags := ⟨none, none, none, none, none, none⟩ },
    fun _ => 0⟩

/-- Code at `0x1000` (read, execute), data at `0x3000` and stacks at `0x5000`–`0x8000` (read,
write). -/
def mem (code : List (Nat × List Byte)) : Memory :=
  let rx : Silmaril.Process.Permissions := ⟨true, false, true⟩
  let rw : Silmaril.Process.Permissions := ⟨true, true, false⟩
  let zeros := (List.range 0x40).map fun _ => (0 : Byte)
  ⟨[⟨0x1000, 0x1000, rx⟩, ⟨0x3000, 0x1000, rw⟩, ⟨0x5000, 0x3000, rw⟩],
    code.foldl (fun b c => Memory.install b c.1 c.2) (Memory.install ∅ 0x3000 zeros)⟩

/-- A configuration with threads `tids` running the given cores. -/
def cfg (ths : List (Nat × Core)) (m : Memory) : XCfg Unit :=
  ⟨fun t => (ths.find? (·.1 == t)).map fun p => { st := .run p.2 }, m, {}, (), false, none⟩

/-- An 8-byte word of memory. -/
def word (C : XCfg Unit) (a : Nat) : Option Nat := Prim.rd C.ms a 8

/-- A thread's core, if it is running. -/
def coreOf (C : XCfg Unit) (t : Nat) : Option Core :=
  match C.th t with
  | some ⟨.run c, _⟩ => some c
  | _ => none

/-- Thread `t` is blocked in `FUTEX_WAIT`. -/
def waits (C : XCfg Unit) (t : Nat) : Bool :=
  match C.th t with
  | some ⟨.wait _ _, _⟩ => true
  | _ => false

/-! ## 1. Two threads, a counter and a mutex -/

/-- The primitives' entry points: `LOCK` at `0x2000`, `UNLOCK` at `0x2010`. -/
def envM : Env Unit := { prims := [(0x2000, Prim.Std.mutexLock.id), (0x2010, Prim.Std.mutexUnlock.id)] }

/-- `call 0x2000; mov rax, [rbx]; add rax, 1; mov [rbx], rax; call 0x2010; mov rax, 60;
xor rdi, rdi; syscall`, at `0x1000`. -/
def incCode : List Byte :=
  [0xE8, 0xFB, 0x0F, 0x00, 0x00,          -- call 0x2000
   0x48, 0x8B, 0x03,                      -- mov rax, [rbx]
   0x48, 0x83, 0xC0, 0x01,                -- add rax, 1
   0x48, 0x89, 0x03,                      -- mov [rbx], rax
   0xE8, 0xFC, 0x0F, 0x00, 0x00,          -- call 0x2010
   0x48, 0xC7, 0xC0, 0x3C, 0x00, 0x00, 0x00, -- mov rax, 60
   0x48, 0x31, 0xFF,                      -- xor rdi, rdi
   0x0F, 0x05]                            -- syscall

/-- Thread `t` with its own stack; `rdi` = the lock (`0x3000`), `rbx` = the counter
(`0x3008`). -/
def incCore (sp : Nat) : Core := core 0x1000 [(.rsp, BitVec.ofNat 64 sp), (.rdi, 0x3000), (.rbx, 0x3008)]

def C1 : XCfg Unit := cfg [(1, incCore 0x5ff8), (2, incCore 0x6ff8)] (mem [(0x1000, incCode)])

/-- Thread 1 to completion, then thread 2. -/
def seqRun := run envM ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] ++ [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]) (C1, [1, 2])

/-- Interleaved: both call `LOCK`, thread 1 takes it, thread 2 waits for its `UNLOCK`. -/
def mixRun := run envM [1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2] (C1, [1, 2])

#guard (seqRun.bind fun p => word p.1 0x3008) == some 2
#guard (seqRun.map fun p => p.1.status) == some (some 0)
#guard (mixRun.bind fun p => word p.1 0x3008) == some 2
#guard (mixRun.map fun p => p.1.status) == some (some 0)

/-- After `call LOCK` by both and `LOCK` by thread 1, thread 2 cannot take its `LOCK` step. -/
def heldCfg := run envM [1, 2, 1] (C1, [1, 2])

#guard heldCfg.isSome
#guard (heldCfg.bind fun p => exec1 envM p.2 p.1 2).isNone
#guard (heldCfg.bind fun p => exec1 envM p.2 p.1 1).isSome

/-! ## 2. A futex handoff -/

/-- Thread 1 at `0x1100`: `mov rax, 202; xor rsi, rsi; xor rdx, rdx; syscall` (wait while
`[rdi] = 0`); `mov rdi, [rdi]; mov rax, 231; syscall` (`exit_group ([rdi])`). -/
def waitCode : List Byte :=
  [0x48, 0xC7, 0xC0, 0xCA, 0x00, 0x00, 0x00, -- mov rax, 202
   0x48, 0x31, 0xF6,                      -- xor rsi, rsi   (FUTEX_WAIT)
   0x48, 0x31, 0xD2,                      -- xor rdx, rdx   (expected 0)
   0x0F, 0x05,                            -- syscall
   0x48, 0x8B, 0x3F,                      -- mov rdi, [rdi]
   0x48, 0xC7, 0xC0, 0xE7, 0x00, 0x00, 0x00, -- mov rax, 231
   0x0F, 0x05]                            -- syscall

/-- Thread 2 at `0x1200`: `mov qword [rdi], 1; mov rax, 202; mov rsi, 1; mov rdx, 1; syscall`
(wake one waiter); `mov rdi, rax; mov rax, 60; syscall` (`exit (woken)`). -/
def wakeCode : List Byte :=
  [0x48, 0xC7, 0x07, 0x01, 0x00, 0x00, 0x00, -- mov qword [rdi], 1
   0x48, 0xC7, 0xC0, 0xCA, 0x00, 0x00, 0x00, -- mov rax, 202
   0x48, 0xC7, 0xC6, 0x01, 0x00, 0x00, 0x00, -- mov rsi, 1   (FUTEX_WAKE)
   0x48, 0xC7, 0xC2, 0x01, 0x00, 0x00, 0x00, -- mov rdx, 1   (one waiter)
   0x0F, 0x05,                            -- syscall
   0x48, 0x89, 0xC7,                      -- mov rdi, rax
   0x48, 0xC7, 0xC0, 0x3C, 0x00, 0x00, 0x00, -- mov rax, 60
   0x0F, 0x05]                            -- syscall

def C2 : XCfg Unit :=
  cfg [(1, core 0x1100 [(.rsp, 0x5ff8), (.rdi, 0x3010)]), (2, core 0x1200 [(.rsp, 0x6ff8), (.rdi, 0x3010)])]
    (mem [(0x1100, waitCode), (0x1200, wakeCode)])

/-- Thread 1 blocks first. -/
def blockFirst := run ({} : Env Unit) [1, 1, 1, 1] (C2, [1, 2])

#guard (blockFirst.map fun p => waits p.1 1) == some true

/-- Then thread 2 sets the flag and wakes it (one waiter woken: `rax = 1`), and thread 1
exits the group with the flag. -/
def handoff := run ({} : Env Unit) [1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1] (C2, [1, 2])

#guard (handoff.map fun p => p.1.status) == some (some 1)

/-- Thread 2's `FUTEX_WAKE` returns `1`. -/
def afterWake := run ({} : Env Unit) [1, 1, 1, 1, 2, 2, 2, 2, 2] (C2, [1, 2])

#guard (afterWake.bind fun p => (coreOf p.1 2).map fun c => (c.core.read .rax).toNat) == some 1
#guard (afterWake.map fun p => waits p.1 1) == some false

/-- Thread 2 first: thread 1's wait finds the flag set and returns `-EAGAIN`. -/
def wakeFirst := run ({} : Env Unit) [2, 2, 2, 2, 2, 1, 1, 1, 1] (C2, [1, 2])

#guard (wakeFirst.bind fun p => (coreOf p.1 1).map fun c => c.core.read .rax) == some errAgain
#guard (wakeFirst.bind fun p => (coreOf p.1 2).map fun c => (c.core.read .rax).toNat) == some 0

def wakeFirstEnd := run ({} : Env Unit) [2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1] (C2, [1, 2])

#guard (wakeFirstEnd.map fun p => p.1.status) == some (some 1)

/-! ## 3. `clone` -/

/-- At `0x1300`: `clone (0x3d0f00, 0x7ff0, 0x3018, 0x301c, 0x7800)`. -/
def cloneCode : List Byte :=
  [0x48, 0xC7, 0xC0, 0x38, 0x00, 0x00, 0x00, -- mov rax, 56
   0x48, 0xC7, 0xC7, 0x00, 0x0F, 0x3D, 0x00, -- mov rdi, 0x3d0f00
   0x48, 0xC7, 0xC6, 0xF0, 0x7F, 0x00, 0x00, -- mov rsi, 0x7ff0 (new stack)
   0x48, 0xC7, 0xC2, 0x18, 0x30, 0x00, 0x00, -- mov rdx, 0x3018 (ptid)
   0x49, 0xC7, 0xC2, 0x1C, 0x30, 0x00, 0x00, -- mov r10, 0x301c (ctid)
   0x49, 0xC7, 0xC0, 0x00, 0x78, 0x00, 0x00, -- mov r8, 0x7800 (tls)
   0x0F, 0x05]                            -- syscall

def C3 : XCfg Unit := cfg [(1, core 0x1300 [(.rsp, 0x5ff8)])] (mem [(0x1300, cloneCode)])

def cloned := run ({} : Env Unit) [1, 1, 1, 1, 1, 1, 1] (C3, [1])

#guard (cloned.map fun p => p.2) == some [1, 2]
#guard (cloned.map fun p => p.1.mt) == some true
#guard (cloned.bind fun p => (coreOf p.1 1).map fun c => (c.core.read .rax).toNat) == some 2
#guard (cloned.bind fun p => (coreOf p.1 2).map fun c =>
  ((c.core.read .rax).toNat, (c.core.read .rsp).toNat, c.core.fsBase.toNat, c.core.rip.toNat)) ==
  some (0, 0x7ff0, 0x7800, 0x1300 + 44)
#guard (cloned.bind fun p => Prim.rd p.1.ms 0x3018 4) == some 2
#guard (cloned.bind fun p => (p.1.th 2).bind (·.ctid)) == some 0x301c

end Silmaril.Proofs.Process.Mt.Examples
