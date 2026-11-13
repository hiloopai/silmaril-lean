module

public import Silmaril.X86.Concurrency.Bridge.Defs
public import Silmaril.X86.Concurrency.Bridge.Crit.Code.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Defs

/-!
# A compiled caller of the mutex, validated through its call sites: definitions

The object
`examples/litmus-c/calls/obj/calls.o` (gcc 13.3.0 `-O2`, pinned flags plus
`-fno-optimize-sibling-calls`) holds `mutex_lock` and `mutex_unlock` (same bytes as the
pinned ones) and the caller

```
crit_add2:  call mutex_lock ; mov eax,[rsi] ; add eax,2 ; mov [rsi],eax ; call mutex_unlock ; ret
```

a critical section in the shape of the pool (`lock(m); body; unlock(m)`). Its linking
certificate `cert` cuts it at the two `call`s: an empty segment, `call mutex_lock` (validated by
`SpinLock.cert`, the lock), the body (`load`, `assign`, `store`), `call mutex_unlock`
(`Spin.unlockCert`), an empty last segment. The caller's own `ret` is its caller's business.

The linked CIR program is `critCir lk ul` with `lk`, `ul` the `spinMutex` code
(`cert_body`), so the callee parts are exactly the code behind the mutex interface.

For the explorer (`Robust`): `critC`, two threads that each set `rdi := m`, `rsi := x` and
run the linked program with loop bound `L = 2`, over the cells `x`, the lock word and its token,
all `0`; and `racyC`, the same threads with both callee bodies removed (no lock).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Bridge.Crit

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.Prim (ent at_ op32)

/-- The certificate of an empty segment. -/
def empty : GCert := ⟨[], [ent 0 []]⟩

/-- `mov eax, [rsi]` (relaxed). -/
def ld : Stmt := .load .rax .rlx 4 .wb (at_ .rsi 0)

/-- `add eax, 2`. -/
def add2 : Stmt := .assign .rax (op32 .add .rax (.lit 2))

/-- `mov [rsi], eax` (relaxed). -/
def st : Stmt := .store .rlx 4 .wb (at_ .rsi 0) (.reg .rax)

/-- The certificate of the critical section's body (code offsets `0x45`–`0x4c`). -/
def bodyCert : GCert where
  start := [ld, add2, st]
  entries := [ent 0 [ld, add2, st], ent 2 [add2, st], ent 5 [st], ent 7 []]

/-- `mutex_lock`: its 32 bytes before the `ret` at `0x20`, the spin-lock certificate. -/
def lockCallee : Callee := ⟨Code.lockOff, 0x20, Prim.SpinLock.cert⟩

/-- `mutex_unlock`: its 4 bytes before the `ret` at `0x34`, the unlock certificate. -/
def unlockCallee : Callee := ⟨Code.unlockOff, 4, Mutex.Spin.unlockCert⟩

/-- **The linking certificate of `crit_add2`.** -/
def cert : LCert where
  parts := [⟨0, empty, lockCallee⟩, ⟨7, bodyCert, unlockCallee⟩]
  lastLen := 0
  lastCert := empty

/-- The linked program with the callee bodies `lk`, `ul` (the shape of `cert.body L`). -/
def critCir (L : Nat) (lk ul : Stmt) : Stmt :=
  .seq (empty.body L) (.seq push8 (.seq lk (.seq pop8
    (.seq (bodyCert.body L) (.seq push8 (.seq ul (.seq pop8 (empty.body L))))))))

/-- The shared counter. -/
def x : Nat := 0x200

/-- The mutex. -/
def m : Nat := 0x100

/-- The loop bound of the instances. -/
def L : Nat := 2

/-- A thread: `rdi := m`, `rsi := x` (the arguments of `crit_add2(m, x)`), then `p`. -/
def thread (p : Stmt) : Stmt :=
  .seq (.assign .rdi (.lit m)) (.seq (.assign .rsi (.lit x)) p)

/-- The cells: `x`, the lock word and its token, all `0`. -/
def cells : List (Nat × Nat) := [(x, 0), (m, 0), (Mutex.Spin.tok m, 0)]

/-- **Two threads running the validated `crit_add2`** linked with the mutex, loop bound `L`. -/
def critC : Robust.CSt :=
  Robust.start [(thread (cert.body L), Regs.zero), (thread (cert.body L), Regs.zero)] cells

/-- **The racy mutant**: the same threads with both callee bodies removed (no lock). -/
def racyC : Robust.CSt :=
  Robust.start [(thread (critCir L .skip .skip), Regs.zero),
    (thread (critCir L .skip .skip), Regs.zero)] cells

/-- A mutant certificate: the two callees swapped. -/
def swapped : LCert where
  parts := [⟨0, empty, unlockCallee⟩, ⟨7, bodyCert, lockCallee⟩]
  lastLen := 0
  lastCert := empty

/-- The counter holds `v`. -/
def xIs (v : Nat) (c : Robust.CSt) : Bool := Robust.memOf c.mem x == some v

/-! ## A minimal caller, run concretely (non-vacuity of `LRun`)

The image `call +0 ; ret` at base `0x1000` (`E8 00 00 00 00 C3`): the
caller is an empty segment and one call to the empty callee at offset 5, whose `ret` (`C3`) is
the byte after the call. Its memories: `miniM1` maps the code (read/execute) and a 16-byte stack
(read/write) at `0x2000`, with the code installed; `miniM2` is `miniM1` with the return address
`0x1005` written at `0x2008` (what the `call` writes). The cores: `miniS0` (`rip = 0x1000`,
`rsp = 0x2010`), `miniS1` after the call, `miniS2` after the `ret`. -/

/-- The bytes `call +0 ; ret`. -/
def miniCode : List (BitVec 8) := [0xE8, 0, 0, 0, 0, 0xC3]

/-- Code (read/execute) at `0x1000`, stack (read/write) at `0x2000`, 16 bytes each. -/
def miniRegions : List Silmaril.Process.Region :=
  [⟨0x1000, 0x10, ⟨true, false, true⟩⟩, ⟨0x2000, 0x10, ⟨true, true, false⟩⟩]

/-- The start core: `rip = 0x1000`, `rsp = 0x2010`. -/
def miniS0 : Silmaril.X86.State := Silmaril.X86.Litmus.initCore 0x1000 [(.rsp, 0x2010)]

/-- The image. -/
def miniT : Tv.XThread := ⟨0x1000, miniCode, miniRegions, miniS0⟩

/-- The memory before the call: the code installed. -/
def miniM1 : Silmaril.Process.Memory :=
  ⟨miniRegions, Silmaril.Process.Memory.install ∅ 0x1000 miniCode⟩

/-- The return address `0x1005`, little-endian. -/
def miniSlot : List (BitVec 8) := [5, 0x10, 0, 0, 0, 0, 0, 0]

/-- The memory after the call: the return address at `0x2008`. -/
def miniM2 : Silmaril.Process.Memory :=
  ⟨miniRegions, Silmaril.Process.Memory.install miniM1.bytes 0x2008 miniSlot⟩

/-- The core after the call. -/
def miniS1 : Silmaril.X86.State :=
  { miniS0.write .rsp (miniS0.read .rsp - 8) with
    rip := miniS0.rip + 5 + (0 : BitVec 32).signExtend 64 }

/-- The core after the `ret`. -/
def miniS2 : Silmaril.X86.State :=
  { miniS1.write .rsp (miniS1.read .rsp + 8) with rip := miniS0.rip + 5 }

/-- The linking certificate: an empty segment, a call to the empty callee at 5, an empty last
segment. -/
def miniCert : LCert := ⟨[⟨0, empty, ⟨5, 0, empty⟩⟩], 0, empty⟩

/-- The observed run: the `call` (from `miniM1` to `miniM2`) and the `ret` (on `miniM2`, no
interference). -/
def miniObs : List LObs := [.call ⟨miniM1, miniS1, miniM2⟩, .ret ⟨miniM2, miniS2, miniM2⟩]

end Silmaril.X86.Concurrency.Bridge.Crit
