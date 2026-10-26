module

public import Silmaril.Apps.Sha256sum.Process
public import Silmaril.Process.CLI.X86Linux

/-! # x86-64 Linux as a `Sys.Machine`

`x86Machine r11Of` runs `Process.CLI.X86Linux.step` (the `X86.Ext` machine with `syscall`
recognised) and turns each `syscall` into a `Sys.Call` with the x86-64 Linux ABI
(`arch/x86/entry/syscalls/syscall_64.tbl`; number in `rax`, arguments in
`rdi rsi rdx`; `read` 0, `write` 1, `close` 3, `brk` 12, `exit` 60, `exit_group` 231,
`openat` 257). This extends `Process.CLI.X86Linux.request`, which models only `read`,
`write` and `exit`, with what a file-reading tool needs:

* `openat(AT_FDCWD, path, O_RDONLY)`: the path is the NUL-terminated string at `rsi`;
* `read(fd, buf, n)`: the reply's bytes are stored at `buf`;
* `write(fd, buf, n)`: the `n` bytes at `buf` are the request;
* `close(fd)`;
* `brk(addr)`: handled here, not by the environment (it is invisible to the world):
  a request at or above the start of the heap is granted and the new pages are mapped
  readable, writable and zero-filled; anything else returns the current break. Linux may
  also refuse a request (an `RLIMIT_DATA` or address-space limit). This is an
  idealized no-refusal profile, not a theorem about Linux allocation: growth
  currently checks neither the address limit nor disjointness from the stack
  or other mappings. `Init` separates the heap start from the image only.
  A real-binary result needs explicit heap/frame and grant/refusal obligations;
  OOM, an unsupported instruction, and a modeled architectural crash are distinct.

On return `rax` holds the result (`-errno` for an error), `rcx` the address after
`syscall`, and `r11` the value `r11Of core`. Linux puts `RFLAGS` in `r11`; statements
quantify over `r11Of`, so they cover that and any other choice.

A buffer the kernel cannot read or write (Linux: `EFAULT`) and a request outside this
profile make the machine stuck, which `Live` statements rule out: a program proved live
here never passes a bad pointer.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.X86Sys

open Silmaril.Apps.Sha256sum
open Silmaril.Apps.Sha256sum.Sys
open Silmaril.Process (Byte Memory Region Permissions)
open Silmaril.Process.CLI
open Silmaril.X86 (Word Reg)

abbrev Core := Silmaril.X86.State

structure XState where
  core : Core
  memory : Memory
  /-- The start of the heap (Linux `mm->start_brk`). -/
  brkStart : Nat
  /-- The current break. -/
  brk : Nat
  /-- The kernel could not deliver a reply into the program's memory. -/
  faulted : Bool := false

def toU8 (b : Byte) : UInt8 := UInt8.ofNat b.toNat
def ofU8 (b : UInt8) : Byte := BitVec.ofNat 8 b.toNat

/-- The NUL-terminated string at `address`, reading at most `fuel` bytes. -/
def cstring (m : Memory) : Nat → Nat → Option Bytes
  | _, 0 => none
  | address, fuel + 1 =>
    match m.readBytes address 1 with
    | some [b] => if b = 0 then some [] else (toU8 b :: ·) <$> cstring m (address + 1) fuel
    | _ => none

/-- `AT_FDCWD` as the 32-bit `int` the kernel reads. -/
def atFdcwd : BitVec 32 := BitVec.ofInt 32 (-100)

/-- A decoded request. -/
inductive Req where
  | call (c : Call)
  | brk (addr : Nat)
  | exit (status : Nat)

def fd32 (w : Word) : Nat := (w.setWidth 32).toNat

/-- Decode the trapped core's request; `none` outside the profile or for an unreadable
buffer. -/
def decode (c : Core) (m : Memory) : Option Req :=
  let nr := (c.read .rax).toNat
  let a0 := c.read .rdi
  let a1 := c.read .rsi
  let a2 := c.read .rdx
  if nr = 0 then some (.call (.read (fd32 a0) a2.toNat))
  else if nr = 1 then
    (m.readBytes a1.toNat a2.toNat).map fun bs => .call (.write (fd32 a0) (bs.map toU8))
  else if nr = 3 then some (.call (.close (fd32 a0)))
  else if nr = 12 then some (.brk a0.toNat)
  else if nr = 257 then
    if a0.setWidth 32 = atFdcwd ∧ a2.setWidth 32 = 0 then
      (cstring m a1.toNat Silmaril.Process.addressLimit).map fun p => .call (.openat p)
    else none
  else if nr = 60 ∨ nr = 231 then some (.exit a0.toNat)
  else none

/-- Linux errno numbers (`include/uapi/asm-generic/errno-base.h`, `errno.h`). -/
def errnoNum : Errno → Nat
  | .ENOENT => 2 | .EACCES => 13 | .EISDIR => 21 | .ENOTDIR => 20 | .ELOOP => 40
  | .ENAMETOOLONG => 36 | .EIO => 5 | .ENOSPC => 28 | .EBADF => 9

def raxOf : Ret → Word
  | .ok n => BitVec.ofNat 64 n
  | .data b => BitVec.ofNat 64 b.length
  | .err e => BitVec.ofInt 64 (-(errnoNum e : Int))

/-- The core the kernel returns to. -/
def returnCore (r11Of : Core → Word) (c : Core) (rax : Word) : Core :=
  ((c.write .rax rax).write .rcx c.rip).write .r11 (r11Of c)

/-- The program state after the environment's reply. -/
def resume (r11Of : Core → Word) (s : XState) (c : Core) (call : Call) (r : Ret) : XState :=
  let core := returnCore r11Of c (raxOf r)
  match call, r with
  | .read _ _, .data b =>
    match s.memory.writeBytes (c.read .rsi).toNat (b.map ofU8) with
    | some m => { s with core := core, memory := m }
    | none => { s with faulted := true }
  | _, _ => { s with core := core }

def rwPerm : Permissions := ⟨true, true, false⟩

/-- `brk(addr)`: grow (mapping zero-filled pages) or report the current break. -/
def brkStep (r11Of : Core → Word) (s : XState) (c : Core) (addr : Nat) : XState :=
  if s.brk < addr then
    { s with core := returnCore r11Of c (BitVec.ofNat 64 addr), brk := addr
             memory := { regions := ⟨s.brk, addr - s.brk, rwPerm⟩ :: s.memory.regions
                         bytes := Memory.install s.memory.bytes s.brk
                           (List.replicate (addr - s.brk) 0) } }
  else if s.brkStart ≤ addr then
    { s with core := returnCore r11Of c (BitVec.ofNat 64 addr), brk := addr }
  else { s with core := returnCore r11Of c (BitVec.ofNat 64 s.brk) }

def step (r11Of : Core → Word) (s : XState) : Action XState :=
  if s.faulted then .stuck else
  match X86Linux.step s.core s.memory with
  | .retired c m => .tau { s with core := c, memory := m }
  | .fault _ => .stuck
  | .syscall c =>
    match decode c s.memory with
    | none => .stuck
    | some (.exit n) => .exit n
    | some (.brk addr) => .tau (brkStep r11Of s c addr)
    | some (.call call) => .call call (resume r11Of s c call)

def x86Machine (r11Of : Core → Word) : Machine := ⟨XState, step r11Of⟩

/-! ## The loader -/

/-- `POSIXLY_CORRECT` is present in an environment string list. -/
def HasPosix (envp : List (List Byte)) : Prop :=
  ∃ e ∈ envp, (lit "POSIXLY_CORRECT=").map ofU8 <+: e

/-- The `execve` input for a world: its `argv`, and an environment that has
`POSIXLY_CORRECT` exactly when the world says so (other variables are arbitrary; the
program reads no other). Standard input is the kernel's (`Sys.KState`), not the ISA's. -/
def InputOf (w : World) (input : ProcInput) : Prop :=
  input.argv = w.argv.map (·.map ofU8) ∧ (HasPosix input.envp ↔ w.posix = true)

/-- The end of the image's highest segment. -/
def imageEnd (image : Image) : Nat :=
  (image.segments.map fun seg => seg.vaddr + seg.memSize).foldl max 0

/-- Every launch of `image` on world `w`: the `Process.CLI.X86Linux.Loaded` relation (the
System V stack with `argv` and `envp`, the segments mapped, `rip` at the entry), and a
heap starting at or above the end of the image (Linux randomises it). -/
def Init (image : Image) (w : World) (s : XState) : Prop :=
  ∃ input, InputOf w input ∧ X86Linux.Loaded image input s.core s.memory ∧
    imageEnd image ≤ s.brkStart ∧ s.brk = s.brkStart ∧ s.faulted = false

end Silmaril.Apps.Sha256sum.X86Sys
