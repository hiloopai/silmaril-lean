module

public import Silmaril.Wasi.Os.Defs

@[expose] public section

/-!
# A concrete x86 runtime of `hello` (Part D of `docs/projects/wasm-wasi.md`)

`Silmaril.Wasi.Os` states the code obligations of an x86 stdout host stub (`WriteStub`) and of a
runtime of `hello` (`HelloRt`) and proves them `IoSafeN` with `lpsEnv`; whether some program
meets them was the frozen open target `Task.helloRt_exists`. That target is **false**
(`not_helloRt_exists` in `Silmaril.Wasi.Runtime.Thms`): `WriteStub.source` asks the stub to hold
*every* non-empty byte list `bs` as its write source, but LPS reads at most `MAX_RW_COUNT`
bytes for one `write`, so no stub exists for a list longer than that. Its exact-state shape
(`next` returns to the state `st rest` itself) also rules out natural loops: the written
bytes stay in memory and `r11` records the flags.

This module states the corrected obligations and a concrete program meeting them.

* `WriteLoop c segs ch e`: the obligations of a stdout write loop **up to an invariant**.
  `Inv bs m` says that `m` is at the loop's `syscall` with the bytes `bs` still to write, and
  `Fin m` that the loop has finished. Only the states of the invariant carry obligations, the
  same ones as `WriteStub`'s: a `syscall` handled by `writeArm`, on the channel `ch`, with
  source exactly `bs`; after a short write of `ds`, a syscall-free run to `Inv` of the rest,
  or to `Fin`.
* `ExitOk m`: `m` is at a `syscall` requesting `exit(0)`.
* `HelloLoop c segs ch e`: a runtime of `hello`, which runs syscall-free from `start` to
  `Inv hiBytes`, and from every `Fin` state to `ExitOk`.
* The program (`helloCode`, 42 bytes at `codeBase = 0x401000`, with `hi` at
  `dataBase = 0x402000`):

  ```
  0x401000: mov $0x402000,%esi ; mov $2,%edx
  loop:     mov $1,%eax ; mov $1,%edi ; syscall        # write(1, rsi, rdx)
            add %rax,%rsi ; sub %rax,%rdx ; jne loop   # short write: loop on the rest
            mov $60,%eax ; mov $0,%edi ; syscall       # exit(0)
  ```

  `helloMem` is its memory: the code read-execute, the data read-only. `helloStart` is the
  launch state (every register `0`, `rip = codeBase`).
* `RegsAt o a d s x m`: `m` has memory `helloMem`, `rip = codeBase + o`, and `rax, rdi, rsi,
  rdx = a, d, s, x`. `helloInv` and `helloFin` are the loop's invariant and final states.
* `Task.helloLoop_exists`: the corrected target. It is proved (`helloLoop_exists`), on the open
  machine `Open.step` and every machine refining it, for every LPS model whose descriptor `1`
  is a live channel; LPS's `initModel` binds it to channel `1` (`initModel_stdout`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Runtime

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Process (Memory Region)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Wasi.Os
open Silmaril.Wasi.Examples (hiBytes)

/-! ## The corrected obligations -/

/-- **The code obligations of an x86 stdout write loop, up to an invariant.** -/
structure WriteLoop (c : MState → Option MState) (segs : List Segment) (ch : Word)
    (e : Silmaril.Process.LPS.Model) where
  /-- The loop is at its `syscall` with the bytes `bs` still to write. -/
  Inv : List Byte → MState → Prop
  /-- The loop has written everything. -/
  Fin : MState → Prop
  /-- Some byte is left. -/
  nonempty : ∀ bs m, Inv bs m → bs ≠ []
  /-- At a `syscall`. -/
  trap : ∀ bs m, Inv bs m → AtSyscall m
  /-- `writeArm` handles it. -/
  handles : ∀ bs m, Inv bs m → ∀ k, (writeArm segs).Handles (trapAt m k) e
  /-- The descriptor is the channel `ch`. -/
  chan : ∀ bs m, Inv bs m → ∀ k,
    fdLookup e.fds (fd32 ((reqAt segs m k).arg 0)) = some (.channel ch)
  /-- The source is exactly the bytes left. -/
  source : ∀ bs m, Inv bs m → ∀ k,
    writeSource (reqAt segs m k).mem ((reqAt segs m k).arg 1) ((reqAt segs m k).arg 2) = bs
  /-- After a partial write of `ds`, the loop runs without syscalls to the rest. -/
  next : ∀ bs m, Inv bs m → ∀ k (ds : List Byte), 1 ≤ ds.length → ds <+: bs →
    ∀ n, SafeN c (fun m' => if bs.drop ds.length = [] then Fin m' else Inv (bs.drop ds.length) m')
      n (resume (trapAt m k) (writeEff segs m k ds))

/-- At a `syscall` requesting `exit(0)`. -/
def ExitOk (m : MState) : Prop :=
  AtSyscall m ∧ (m.core.read .rax).toNat = 60 ∧ m.core.read .rdi &&& 255 = 0

/-- **An x86 runtime of `hello`** over a write loop. -/
structure HelloLoop (c : MState → Option MState) (segs : List Segment) (ch : Word)
    (e : Silmaril.Process.LPS.Model) extends WriteLoop c segs ch e where
  /-- The launch state. -/
  start : MState
  /-- It runs without syscalls to the loop, with `hi` to write. -/
  toWrite : ∀ n, SafeN c (Inv hiBytes) n start
  /-- After the loop it runs without syscalls to `exit(0)`. -/
  toExit : ∀ m, Fin m → ∀ n, SafeN c ExitOk n m

/-- **The corrected open target** (proved: `helloLoop_exists`): a runtime of `hello` exists on
the open machine, for every LPS model whose descriptor `1` is a live channel. -/
def Task.helloLoop_exists : Prop :=
  ∀ (e : Silmaril.Process.LPS.Model) (ch : Word),
    fdLookup e.fds 1 = some (.channel ch) → wIs0 ch = false →
    ∃ (c : MState → Option MState) (segs : List Segment),
      Silmaril.Machine.X86.Safe.Refines Silmaril.Machine.X86.Open.step c ∧
        Nonempty (HelloLoop c segs ch e)

/-! ## The program -/

/-- The load address of the code. -/
def codeBase : Word := 0x401000#64

/-- The load address of `hi`. -/
def dataBase : Word := 0x402000#64

/-- **The code** (42 bytes; see the module comment). -/
def helloCode : List Byte :=
  [0xbe, 0x00, 0x20, 0x40, 0x00,   -- mov $0x402000,%esi
   0xba, 0x02, 0x00, 0x00, 0x00,   -- mov $2,%edx
   0xb8, 0x01, 0x00, 0x00, 0x00,   -- loop: mov $1,%eax
   0xbf, 0x01, 0x00, 0x00, 0x00,   -- mov $1,%edi
   0x0f, 0x05,                     -- syscall
   0x48, 0x01, 0xc6,               -- add %rax,%rsi
   0x48, 0x29, 0xc2,               -- sub %rax,%rdx
   0x75, 0xec,                     -- jne loop
   0xb8, 0x3c, 0x00, 0x00, 0x00,   -- mov $60,%eax
   0xbf, 0x00, 0x00, 0x00, 0x00,   -- mov $0,%edi
   0x0f, 0x05]                     -- syscall

/-- The mappings: one page of code (read, execute), one page of data (read). -/
def helloRegions : List Region :=
  [⟨0x401000, 0x1000, ⟨true, false, true⟩⟩, ⟨0x402000, 0x1000, ⟨true, false, false⟩⟩]

/-- **The memory of the runtime**: the code at `codeBase`, `hi` at `dataBase`. -/
def helloMem : Memory :=
  ⟨helloRegions, Memory.install (Memory.install ∅ 0x402000 hiBytes) 0x401000 helloCode⟩

/-- **The launch state**: every register `0`, flags defined and clear, `rip = codeBase`. -/
def helloStart : MState :=
  ⟨{ regs := fun _ => 0, rip := codeBase,
     flags := ⟨some false, some false, some false, some false, some false, some false⟩ },
   helloMem⟩

/-- `m` runs the program at offset `o`, with `rax, rdi, rsi, rdx = a, d, s, x`. -/
def RegsAt (o : Nat) (a d s x : Word) (m : MState) : Prop :=
  m.memory = helloMem ∧ m.core.rip = codeBase + BitVec.ofNat 64 o ∧ m.core.read .rax = a ∧
    m.core.read .rdi = d ∧ m.core.read .rsi = s ∧ m.core.read .rdx = x

/-- **The loop invariant**: at the `write` syscall, `j` bytes of `hi` written, the rest left. -/
def helloInv (bs : List Byte) (m : MState) : Prop :=
  ∃ j, j < 2 ∧ bs = hiBytes.drop j ∧
    RegsAt 20 1#64 1#64 (dataBase + BitVec.ofNat 64 j) (BitVec.ofNat 64 (2 - j)) m

/-- The loop has finished: at the `exit` sequence. -/
def helloFin (m : MState) : Prop := ∃ a d s x, RegsAt 30 a d s x m

end Silmaril.Wasi.Runtime
