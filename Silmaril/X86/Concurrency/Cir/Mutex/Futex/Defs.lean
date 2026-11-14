module

public import Silmaril.X86.Concurrency.Cir.Mutex.Defs
public import Silmaril.X86.Concurrency.Cir.TvCfg.Fx.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Code.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Defs

/-!
# Drepper's futex mutex in CIR

The mutex of `examples/litmus-c/futex-mutex/fmutex.c`
(gcc 13.3.0, `-O2`, pinned in `Mutex.Futex.Code`), translation-validated into CIR by the
checker `TvCfg.Fx.tvFx` at the first step. Everything after that is about these CIR programs.

## The programs

`fmutex_lock` (Drepper's mutex 2/3 lock):

```
rax := 0; rdx := 1; rax := cas(acq)([rdi], expected rax, new rdx)
if rax ≠ 0:
  if rax = 2: SLOW
  else: rax := 2; rax := xchg(acq)([rdi], rax); if rax ≠ 0: SLOW
SLOW = r8 := 202; rsi := 128; rdx := 2; BODY; while rax ≠ 0: BODY
BODY = r10 := 0; rax := r8; futex_wait([rdi], rdx); rax := edx; rax := xchg(acq)([rdi], rax)
```

The x86 code is a do-while loop entered from two places, so `SLOW` appears twice and `BODY`
is unrolled once (CIR has only `while` loops).

`fmutex_unlock` (exchange release): `rax := 0; rax := xchg(rel)([rdi], rax); if eax = 2:
r10 := 0; rax := 202; rsi := 129; rdx := 1; futex_wake([rdi], rdx)`.

`fmutex_unlock_dec` (Drepper's original unlock): `rax := fetch_sub(rel)([rdi], 1)` (the
destination `rax` is a CIR scratch register; x86's `lock sub` writes none), and if the old value
was not `1`: the futex-call registers, `[rdi] := 0` (release, a plain `mov`), and the wake.

## The mutex (`fmutex`, in `Thms`)

The object is the spin mutex's: the lock word at `l` and the token cell at `l + 4`, with
`Spin.locked`, `Spin.inv` (the `lockInv l (locked l ∗ R)`: the word is `0` and the
invariant holds the token and `R`, or the word is not `0`) and `Spin.init`. The futex word
`2` ("contended") is just another non-zero value: the invariant does not need to know who
waits.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex.Futex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx
open Silmaril.X86.Concurrency.Cir.Prim (at_ r32 zTest zCmpI op32 thr)

/-! ## `fmutex_lock` -/

namespace Lock

/-- `xor eax, eax`. -/
def zero : Stmt := .assign .rax (op32 .xor .rax (.reg .rax))
/-- `mov edx, 1`. -/
def one : Stmt := .assign .rdx (.lit 1)
/-- `lock cmpxchg [rdi], edx` (acquire). -/
def cas : Stmt := .rmw .rax .acq 4 (.cas (.reg .rax)) (at_ .rdi 0) (.reg .rdx)
/-- `mov eax, 2`. -/
def two : Stmt := .assign .rax (.lit 2)
/-- `xchg [rdi], eax` (acquire). -/
def xchg : Stmt := .rmw .rax .acq 4 .xchg (at_ .rdi 0) (.reg .rax)
/-- `mov r8d, 202` (`SYS_futex`). -/
def nr : Stmt := .assign .r8 (.lit 202)
/-- `mov esi, 128` (`FUTEX_WAIT_PRIVATE`). -/
def op : Stmt := .assign .rsi (.lit 128)
/-- `mov edx, 2`. -/
def val : Stmt := .assign .rdx (.lit 2)
/-- `xor r10d, r10d` (no timeout). -/
def tmo : Stmt := .assign .r10 (op32 .xor .r10 (.reg .r10))
/-- `mov rax, r8`. -/
def sys : Stmt := .assign .rax (.reg .r8)
/-- `mov eax, edx`. -/
def back : Stmt := .assign .rax (r32 .rdx)

/-- One round of the wait loop: sleep while the word is `2`, then mark it contended again. -/
def body : List Stmt := [tmo, sys, waitStmt, back, xchg]

/-- `while (c != 0) { futex_wait(2); c = xchg(2) }`. -/
def wloop : Stmt := .loop 0 (notE (zTest .rax)) (Tv.chain body)

/-- The slow path from `1e`: the call registers, one round, then the loop. -/
def slow : List Stmt := [nr, op, val] ++ body ++ [wloop]

/-- `if (c != 2) c = xchg(2)`, then the slow path unless the exchange found the lock free. -/
def contend : Stmt :=
  .ite (zCmpI .rax 2) (Tv.chain slow)
    (Tv.chain [two, xchg, .ite (zTest .rax) .skip (Tv.chain slow)])

/-- **`fmutex_lock` in CIR.** -/
def prog : List Stmt := [zero, one, cas, .ite (notE (casZ 0)) (Tv.chain [contend]) .skip]

/-- Known values on the slow path from `1e` on. -/
def kSlow : List (Reg × Word) := [(.r8, 202), (.rsi, 128), (.rdx, 2)]

/-- The certificate. -/
def cert : FCert where
  start := prog
  entries :=
    [ fent 0 prog, fent 2 (prog.drop 1) none [(.rax, 0)],
      fent 7 (prog.drop 2) none [(.rax, 0), (.rdx, 1)],
      fent 0xb (prog.drop 3) (some (casZ 0)),
      fent 0xd [],
      fent 0xe [contend], fent 0x11 [contend] (some (zCmpI .rax 2)),
      fent 0x13 [two, xchg, .ite (zTest .rax) .skip (Tv.chain slow)],
      fent 0x18 [xchg, .ite (zTest .rax) .skip (Tv.chain slow)],
      fent 0x1a [.ite (zTest .rax) .skip (Tv.chain slow)],
      fent 0x1c [.ite (zTest .rax) .skip (Tv.chain slow)] (some (zTest .rax)),
      fent 0x1e slow, fent 0x24 (slow.drop 1) none [(.r8, 202)],
      fent 0x29 (slow.drop 2) none [(.r8, 202), (.rsi, 128)],
      fent 0x2e (slow.drop 3) none kSlow [.rcx, .r11],
      fent 0x31 (slow.drop 4) none ((.r10, 0) :: kSlow) [.rcx, .r11],
      fent 0x34 (slow.drop 5) none ((.rax, 202) :: (.r10, 0) :: kSlow) [.rcx, .r11],
      fent 0x36 (slow.drop 6) none [(.r8, 202), (.rsi, 128), (.rdx, 2)] clob,
      fent 0x38 (slow.drop 7) none kSlow [.rcx, .r11],
      fent 0x3a [wloop] none kSlow [.rcx, .r11],
      fent 0x3c [wloop] (some (zTest .rax)) kSlow [.rcx, .r11],
      fent 0x3e [] none [] clob,
      fent 0x3f [] none [] clob ]

end Lock

/-! ## `fmutex_unlock` -/

namespace Unlock

/-- `xchg [rdi], eax` (release). -/
def xchg : Stmt := .rmw .rax .rel 4 .xchg (at_ .rdi 0) (.reg .rax)

/-- The wake: the call registers and `futex_wake([rdi], 1)`. -/
def wake : List Stmt :=
  [Lock.tmo, .assign .rax (.lit 202), .assign .rsi (.lit 129), .assign .rdx (.lit 1), wakeStmt]

/-- **`fmutex_unlock` in CIR.** -/
def prog : List Stmt := [Lock.zero, xchg, .ite (zCmpI .rax 2) (Tv.chain wake) .skip]

/-- The certificate. -/
def cert : FCert where
  start := prog
  entries :=
    [ fent 0 prog, fent 2 (prog.drop 1) none [(.rax, 0)], fent 4 (prog.drop 2),
      fent 7 (prog.drop 2) (some (zCmpI .rax 2)), fent 9 [],
      fent 0x10 wake, fent 0x13 (wake.drop 1) none [(.r10, 0)],
      fent 0x18 (wake.drop 2) none [(.r10, 0), (.rax, 202)],
      fent 0x1d (wake.drop 3) none [(.r10, 0), (.rax, 202), (.rsi, 129)],
      fent 0x22 (wake.drop 4) none [(.r10, 0), (.rax, 202), (.rsi, 129), (.rdx, 1)],
      fent 0x24 [] none [] clob ]

end Unlock

/-! ## `fmutex_unlock_dec` -/

namespace UnlockDec

/-- `lock sub [rdi], 1` (release), with `rax` as CIR's scratch destination. -/
def dec : Stmt := .rmw .rax .rel 4 (.op .sub) (at_ .rdi 0) (.lit 1)

/-- `mov dword [rdi], 0` (release): a plain store. -/
def st0 : Stmt := .store .rel 4 .wb (at_ .rdi 0) (.lit 0)

/-- The release and wake. -/
def wake : List Stmt :=
  [Lock.tmo, .assign .rax (.lit 202), .assign .rsi (.lit 129), st0, .assign .rdx (.lit 1),
    wakeStmt]

/-- **`fmutex_unlock_dec` in CIR.** -/
def prog : List Stmt := [dec, .ite (notE (subZ .rax 1#32)) (Tv.chain wake) .skip]

/-- The certificate. -/
def cert : FCert where
  start := prog
  entries :=
    [ fent 0 prog, fent 4 (prog.drop 1) (some (subZ .rax 1#32)) [] [.rax], fent 6 [] none [] [.rax],
      fent 0x10 wake none [] [.rax], fent 0x13 (wake.drop 1) none [(.r10, 0)] [.rax],
      fent 0x18 (wake.drop 2) none [(.r10, 0), (.rax, 202)],
      fent 0x1d (wake.drop 3) none [(.r10, 0), (.rax, 202), (.rsi, 129)],
      fent 0x23 (wake.drop 4) none [(.r10, 0), (.rax, 202), (.rsi, 129)],
      fent 0x28 (wake.drop 5) none [(.r10, 0), (.rax, 202), (.rsi, 129), (.rdx, 1)],
      fent 0x2a [] none [] clob ]

end UnlockDec


/-! ## Mutant certificates (the checker must reject them) -/

namespace Mutants

/-- Replace every futex wait by a wake. -/
def swapW : Stmt → Stmt
  | .futexWait .. => wakeStmt
  | .seq s t => .seq (swapW s) (swapW t)
  | .ite c s t => .ite c (swapW s) (swapW t)
  | .loop n c b => .loop n c (swapW b)
  | s => s

/-- `fmutex_lock`'s certificate with the wait claimed to be a wake. -/
def lockWake : FCert :=
  ⟨Lock.prog.map swapW, Lock.cert.entries.map fun e => { e with cir := e.cir.map swapW }⟩

/-- `fmutex_lock`'s certificate without known register values: the checker cannot see that the
`syscall` is a futex wait, nor that `rax < 2^32` at the `cmpxchg`. -/
def lockNoKn : FCert :=
  ⟨Lock.prog, Lock.cert.entries.map fun e => { e with kn := [] }⟩

/-- `fmutex_unlock`'s certificate with its release claimed to be a plain store (`mov`). -/
def unlockStore : FCert :=
  let st : Stmt := .store .rel 4 .wb (at_ .rdi 0) (.reg .rax)
  ⟨[Lock.zero, st, .ite (zCmpI .rax 2) (Tv.chain Unlock.wake) .skip],
    Unlock.cert.entries.map fun e =>
      { e with cir := e.cir.map fun x => if TvCfg.sbeq x Unlock.xchg then st else x }⟩

/-- Replace byte `i` of `code` by `v`. -/
def setByte (code : List (BitVec 8)) (i v : Nat) : List (BitVec 8) := code.set i (BitVec.ofNat 8 v)

/-- **Code mutants**: one byte changed, same length, checked against the unchanged
certificate. `fmutex_unlock` with `mov esi, 128` (its wake becomes a wait). -/
def unlockWaitOp : List (BitVec 8) := setByte Code.fmutexUnlock 0x19 0x80
/-- `fmutex_unlock` with `mov [rdi], eax` in place of `xchg [rdi], eax`. -/
def unlockMov : List (BitVec 8) := setByte Code.fmutexUnlock 0x2 0x89
/-- `fmutex_unlock` comparing the old value with `1` instead of `2`. -/
def unlockCmp1 : List (BitVec 8) := setByte Code.fmutexUnlock 0x6 0x01
/-- `fmutex_lock` calling system call `203` instead of `202` (futex). -/
def lockNr203 : List (BitVec 8) := setByte Code.fmutexLock 0x20 0xcb
/-- `fmutex_lock` without the `lock` prefix on `cmpxchg` (a `nop` in its place). -/
def lockNoLock : List (BitVec 8) := setByte Code.fmutexLock 0x7 0x90
/-- `fmutex_lock` waiting for the value `1` instead of `2`. -/
def lockVal1 : List (BitVec 8) := setByte Code.fmutexLock 0x2a 0x01
/-- `fmutex_lock` with `je` in place of the `jne` after the `cmpxchg`. -/
def lockJe : List (BitVec 8) := setByte Code.fmutexLock 0xb 0x74
/-- `fmutex_unlock_dec` subtracting `2`. -/
def decSub2 : List (BitVec 8) := setByte Code.fmutexUnlockDec 0x3 0x02

end Mutants

/-! ## A concrete x86 run through the futex call (non-vacuity of `SysStep`) -/

namespace Wit

open Silmaril.X86.MemoryModel.Litmus (XAct)

/-- `fmutex_unlock` at `0x1000`, the lock word at `0x2000` (a readable, writable region). -/
def thread : Tv.XThread :=
  ⟨0x1000, Code.fmutexUnlock, [⟨0x2000, 0x10, ⟨true, true, false⟩⟩],
    Silmaril.X86.Litmus.initCore 0x1000 [(.rdi, 0x2000)]⟩

/-- The first successor of `stepSym` when every read returns `2` (the lock is contended). -/
def nxt (s : Silmaril.X86.State) : List XAct × Silmaril.X86.State :=
  match Silmaril.X86.Litmus.stepSym thread [2] s with
  | some (o :: _) => o
  | _ => ([], s)

/-- The core after `k` such steps. -/
def core : Nat → Silmaril.X86.State
  | 0 => thread.init
  | k + 1 => (nxt (core k)).2

/-- The core after the `syscall` (a wake), with `rax`, `rcx`, `r11` returned as `0`. -/
def fin : Silmaril.X86.State :=
  { (((core 8).write .rax 0).write .rcx 0).write .r11 0 with
    rip := (core 8).rip + BitVec.ofNat 64 2, flags := (core 8).flags }

/-- The actions of the run: eight litmus steps (`xchg` reads `2`), then the wake. -/
def acts : List (List XAct) :=
  (List.range 8).map (fun k => (nxt (core k)).1) ++ [(Lab.fwake 0x2000 1 0).acts]

end Wit

/-! ## C11 shapes with futex calls -/

/-- **The C11 shape of a futex lock**: atomic loads, read-modify-writes that are at least
acquire, and futex waits. -/
def c11FLockB (s : Stmt) : Bool :=
  (accessesOf s).all fun
    | .load _ m .. => m != .na
    | .rmw _ m .. => acqMode m
    | .futexWait .. => true
    | _ => false

/-- **The C11 shape of a futex unlock**: read-modify-writes that are at least release, and futex
wakes. A release *store* (Drepper's original unlock) fails it. -/
def c11FUnlockB (s : Stmt) : Bool :=
  (accessesOf s).all fun
    | .rmw _ m .. => relMode m
    | .futexWake .. => true
    | _ => false

/-! ## Explorer instance (non-vacuity) -/

namespace Inst

open Silmaril.X86.Concurrency.Cir.Robust

/-- One thread runs `lock(m); unlock(m)` on an unlocked futex mutex (loop bound 2). -/
def one : CSt :=
  start [(.seq (Mutex.Inst.call (Lock.cert.body 2) (.lit Even.m))
      (Mutex.Inst.call (Unlock.cert.body 2) (.lit Even.m)), Regs.zero)]
    [(Even.m, 0), (Spin.tok Even.m, 0)]

/-- The lock word is `0` again. -/
def unlockedB (c : CSt) : Bool := (memOf c.mem Even.m) == some 0

/-! ### A contended run, by schedule

The explorer branches 256 ways on the queue byte of every futex call, so a kernel-checked
exhaustive two-thread instance timed out. A **schedule** avoids the enumeration: `walk` follows
one thread at a time and takes the first successor of `tsoStepT` (for a futex call, queue byte
`0`), and each step is a TSO step by `tsoStepT_sound`. -/

/-- `Even` linked with the futex mutex (`fmutex_lock`, `fmutex_unlock`), loop bound `2`. -/
def evenC : CSt :=
  start (Mutex.Inst.threads (Mutex.Inst.call (Lock.cert.body 2))
      (Mutex.Inst.call (Unlock.cert.body 2)))
    (Mutex.Inst.cells ++ [(Even.m, 0), (Spin.tok Even.m, 0)])

/-- Follow a schedule of thread ids, taking each thread's first enumerated TSO successor. -/
def walk (N : Nat) (c : CSt) : List Nat → CSt
  | [] => c
  | t :: ts => if t < N ∧ t < c.buf.length then walk N ((tsoStepT c t).getD 0 c) ts else c

/-- The next leaf statement. -/
def headS : Stmt → Stmt
  | .seq s _ => headS s
  | s => s

/-- The next statement is a futex wait. -/
def atWait (s : Stmt) : Bool := match headS s with | .futexWait .. => true | _ => false

/-- The next statement is a futex wake. -/
def atWake (s : Stmt) : Bool := match headS s with | .futexWake .. => true | _ => false

/-- Thread 0 locks and runs its critical section, its stores flush, then thread 1 fails the
`cas`, marks the word contended (`xchg 2`) and reaches its futex wait. -/
def cont1 : CSt := walk 2 evenC (List.replicate 27 0 ++ List.replicate 25 1)

/-- Thread 0's unlock exchange sees `2` and it reaches its futex wake. -/
def cont2 : CSt := walk 2 cont1 (List.replicate 11 0)

/-- Thread 0 wakes and finishes; thread 1 returns from its wait, takes the lock, runs its
critical section and unlocks. -/
def cont3 : CSt := walk 2 cont2 (List.replicate 3 0 ++ List.replicate 42 1)

end Inst

/-! ## Open goals -/

/-- The ticket lock's object: `next` and `serving`, both `0`. -/
def ticketInit (l : Nat) : Csl.Heap :=
  Csl.Heap.union (Csl.Heap.single l 0) (Csl.Heap.single (l + 4) 0)

/- The plan for Drepper's original unlock (kept; the proof is `Task.decUnlock` below).
Every client proved against the interface gets its goal
on TSO when linked with `fmutex_lock` and `fmutex_unlock_dec` (`fetch_sub`, then a plain `mov`
release of `0`, then a wake).

The obstacle is `Task.movUnlock`: `LabOk` rejects the `mov`, a non-draining write to
the invariant's lock word. Plan: a simulation into the accepted `fmutex` (exchange release). The
`mov` is the only non-draining write other threads see; it
is followed in program order by the wake, a draining call, so it is flushed before the thread
does anything else that is visible. A buffered `[l] := 0` that has not flushed is matched by
the exchange not yet executed; the other threads see the old value `1` or `2` meanwhile, and
the exchange's old value (`1` or `2`) only selects whether to wake, which no client observes.
Note: the `lock sub` is a draining write too. With old value `1` it writes `0` and is
itself the release, matched by the exchange. With old value `2` it writes `1`, keeps the word
non-zero and moves no ownership, so it is a stutter of `fmutex`'s run, and the release is the
later `mov`. The simulation must cover both cases.
Registers: `fmutex_unlock_dec` leaves `rax`, `rcx`, `r11` as junk, like the exchange unlock. -/
/-- **The first statement of `Task.decUnlock`**, over `Client.Proved` (kept as the record of the
original statement). It is **false** (`Mutex.Futex.decUnlockIface_false`). A client is
any Lean function of its holes, so it can recognise `fmutex_lock` and `fmutex_unlock_dec`. In every
`Iface` with those codes, the `Iface`'s own specs exclude every invariant state with a 32-bit
lock word that is disjoint from a lock token: the lock's `cas` puts the word in every invariant
state; with a word other than `1` the unlock's `lock sub` takes the contended path, whose
non-draining `mov` of `0` is allowed only to an owned cell (the later futex wake drains, but comes
too late); and a word `1` leads, by another thread's failed `cas` and `xchg 2`, to a word `2`. So a
client that locks, unlocks and then writes a forbidden value is vacuously proved against every
`Iface`, and writes it when linked with the real codes. The restatement over `ProvedR` is
`Task.decUnlock` below. -/
def decUnlockIface : Prop :=
  ∀ (C : Client) (goal : (Nat → Regs) → Csl.Heap → Prop), C.Proved goal → 8 ≤ C.slot →
    ∀ (L : Nat) (Cf : Csl.OCfg),
      Csl.OReach .tso C.N (C.startWith
        (fun a => .seq (.assign .rdi a) (Lock.cert.body L))
        (fun a => .seq (.assign .rdi a) (UnlockDec.cert.body L))
        (C.locks.foldr (fun l h => Csl.Heap.union (Spin.init l) h) Csl.Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < C.N, (Cf.ts t).1 = .skip) → goal (fun t => (Cf.ts t).2) Cf.mem

/-- **Drepper's original unlock** (PROVED, `Futex.decUnlock_holds`). Every client
proved against the interface with release stores (`ProvedR`) gets its goal on TSO when linked with
`fmutex_lock` and `fmutex_unlock_dec` (`fetch_sub`, then a plain `mov` release of `0`, then a
wake).

Restated from `decUnlockIface` (clients proved against the `Iface`), as `Task.movUnlock`
was. Proof: `fmutexDec : IfaceR` (the `Iface` proof of the lock, lifted; the unlock by
the release rule: the `lock sub` is a draining release when the old value is `1` and moves nothing
otherwise; on the contended path the `mov` is a release and the wake, a draining label touching no
cell, ends the pending window), and `Mutex.link_any_mutexR`. -/
def Task.decUnlock : Prop :=
  ∀ (C : Client) (goal : (Nat → Regs) → Csl.Heap → Prop), C.ProvedR goal → 8 ≤ C.slot →
    ∀ (L : Nat) (Cf : Csl.OCfg),
      Csl.OReach .tso C.N (C.startWith
        (fun a => .seq (.assign .rdi a) (Lock.cert.body L))
        (fun a => .seq (.assign .rdi a) (UnlockDec.cert.body L))
        (C.locks.foldr (fun l h => Csl.Heap.union (Spin.init l) h) Csl.Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < C.N, (Cf.ts t).1 = .skip) → goal (fun t => (Cf.ts t).2) Cf.mem

/-- **The first statement of `Task.ticketIface`**, over `Client.Proved` (kept as the record of
the original statement). It is **false** (`Mutex.Futex.ticketIfaceFirst_false`). A
client is any Lean function of its holes, so it can recognise the ticket unlock. In every
`Iface` with that unlock code, the `Iface`'s own `unlock_spec` forces every invariant state
disjoint from a lock token to hold a value of `2 ^ 32` or more in `serving` (a 32-bit value would
make the unlock's load a real step, after which the logic forces the holder to own `serving`
for the non-draining `mov`, and it can never give it up). So a client that locks, unlocks and
then writes a forbidden value is vacuously proved against every `Iface` (its unlock's first
load is inconsistent with every invariant state), and writes it when linked with the real
ticket lock.

The plan, kept: extend the heaps with ghost cells (an exclusive ticket token per drawn ticket,
handed out at the `lock xadd` on `next`, which drains), give the invariant `R` for the ticket
equal to `serving`, and acquire at the `serving` load (a non-draining read may gain cells). Then
the release-store simulation of `Task.decUnlock`. -/
def ticketIfaceFirst : Prop :=
  ∀ (C : Client) (goal : (Nat → Regs) → Csl.Heap → Prop), C.Proved goal → 8 ≤ C.slot →
    ∀ (L : Nat) (Cf : Csl.OCfg),
      Csl.OReach .tso C.N (C.startWith
        (fun a => .seq (.assign .rdi a) (Prim.TicketLock.cert.body L))
        (fun a => .seq (.assign .rdi a) (Prim.TicketUnlock.cert.body L))
        (C.locks.foldr (fun l h => Csl.Heap.union (ticketInit l) h) Csl.Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < C.N, (Cf.ts t).1 = .skip) → goal (fun t => (Cf.ts t).2) Cf.mem

/-- **The ticket lock behind the interface** (PROVED, `Futex.ticketIface_holds`).
Every client proved against the interface with ghost state (`ProvedG`), with fewer than `2 ^ 32`
threads, gets its goal on TSO when linked with the `ticket_lock` and `ticket_unlock` (whose
release is a plain `mov` of `serving + 1`).

Restated from `ticketIfaceFirst` (clients proved against the `Iface`), which is false
(`ticketIfaceFirst_false`). Two changes:

* **`ProvedG` instead of `Proved`**: who holds the lock is recorded only in the tickets, so the
  interface needs ghost state; the `IfaceR` is ghost-blind, so the Task quantifies over the
  clients proved against `Mutex.IfaceG` (every `IfaceR` is an `IfaceG`, `IfaceG.ofIfaceR`);
* **`C.N < 2 ^ 32`**: the tickets are 32-bit, so with `2 ^ 32` waiters two threads can hold the
  same ticket (the bound in `Task.ticketMutexTso`); `IfaceG.thrOk` carries it.

Proof: `ticketMutexG : IfaceG` (`ticketLock_acquireR`, `ticketUnlock_rel`, framed
by `Csl.Rel.safeR_inv_frame`) and `Mutex.link_any_mutexG` (`Csl.Rel.rel_tso`). -/
def Task.ticketIface : Prop :=
  ∀ (C : Client) (goal : (Nat → Regs) → Csl.Heap → Prop), C.ProvedG goal → 8 ≤ C.slot →
    C.N < 2 ^ 32 → ∀ (L : Nat) (Cf : Csl.OCfg),
      Csl.OReach .tso C.N (C.startWith
        (fun a => .seq (.assign .rdi a) (Prim.TicketLock.cert.body L))
        (fun a => .seq (.assign .rdi a) (Prim.TicketUnlock.cert.body L))
        (C.locks.foldr (fun l h => Csl.Heap.union (ticketInit l) h) Csl.Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < C.N, (Cf.ts t).1 = .skip) → goal (fun t => (Cf.ts t).2) Cf.mem

/-- The three functions: name, code, certificate. -/
def all : List (String × List (BitVec 8) × FCert) :=
  [ ("fmutex_lock", Code.fmutexLock, Lock.cert), ("fmutex_unlock", Code.fmutexUnlock, Unlock.cert),
    ("fmutex_unlock_dec", Code.fmutexUnlockDec, UnlockDec.cert) ]

end Silmaril.X86.Concurrency.Cir.Mutex.Futex
