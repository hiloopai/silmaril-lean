module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Defs
public import Silmaril.X86.Concurrency.Cir.Prim.Defs
public import Silmaril.X86.Concurrency.Cir.C11.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Code.Defs
public import Silmaril.X86.Concurrency.Cir.Prim.Clients.Defs
public import Mathlib.Data.Nat.Pairing

/-!
# A Mutex interface on CIR

Everything here is stated on CIR and on its CIR-native
CSL (`Cir.Csl`): a mutex is CIR code with CSL specs, a client is a CIR program with
holes for the two derived ops, and linking is filling the holes.

## The interface (`Iface`)

A mutex implementation provides, for a mutex object at address `l` protecting a resource `R`:

* `size`, `init l`: the object occupies addresses `[l, l + size)`, and `init l` are its cells
  in the unlocked state (a static initializer, as `PTHREAD_MUTEX_INITIALIZER`);
* `inv l R`: the mutex's share of the CSL resource invariant;
* `locked l`: the **abstract lock token**, owned by the holder (`locked_excl`: exclusive);
* `lockCode L`, `unlockCode L`: CIR code (loops bounded by `L`; the argument in `rdi`);
* the specs, under every frame invariant `J` (other locks, other shared state):
  * `init_inv`: `R ∗ init l ⊢ inv l R` (making a mutex);
  * `lock_spec`: `{emp} lock(l) {R ∗ locked l}` under `inv l R ∗ J`;
  * `unlock_spec`: `{R ∗ locked l} unlock(l) {emp}` under `inv l R ∗ J`.

Clients see only these fields, so a client proved `∀ M : Iface` uses nothing about how a mutex
represents its state.

## Derived ops and clients

`Iface.lock M L a` is `rdi := a; M.lockCode L`, and `Iface.unlock` likewise: lock and unlock
are **derived CIR ops**, not new primitives, so CIR stays as small as it was. A `Client` is a
CIR program with two holes (`body lk ul t`), its own cells, and the addresses of its mutexes,
each with a slot of `slot` bytes. `Client.link M L` fills the holes with `M`'s derived ops and
puts `M.init` at each mutex address. `Client.Sat goal M` is the client's CSL certificate at
`M`, and its proof that the postconditions imply `goal`.

## The implementation (`Spin`)

The mutex of `examples/litmus-c/mutex/mutex.c`, pinned in `Mutex.Code`:

* `mutex_lock` is byte-identical to the `spin_lock` (`Code.mutexLock = Prim.Code.spinLock`),
  so its CIR program is the `SpinLock.cert.body`, validated by the checker;
* `mutex_unlock` (C11 `atomic_exchange(release)`) and `mutex_unlock_sc` (C11
  `atomic_store(seq_cst)`) both compile to `xor eax,eax; xchg [rdi],eax`; their certificates are
  `Spin.unlockCert` and `Spin.unlockScCert` (modes `rel` and `sc`).

The logic has no ghost state, so the lock token is a real cell, `l + 4` (`mutex_t`'s `tok`
field), which no code accesses: `Spin.locked l = ∃ v, l + 4 ↦ v`, and the invariant is
`lockInv l (locked l ∗ R)`. The token moves only at the two exchanges, which drain the store
buffer, so the hand-off discipline holds.

## C11 modes

`acqMode`, `relMode`, `c11LockB`, `c11UnlockB`: the C11 shape of a lock (every
read-modify-write at least acquire, no `na` access) and an unlock (every access a
read-modify-write at least release). `cfgModesOk` checks every mode of a CFG certificate
against its x86 instruction with `C11.modeOk1` (closing, for these certificates, the
"modes unchecked" gap). The mapping from C11 to the interface:

| C11 source | x86 | CIR | interface |
| --- | --- | --- | --- |
| `while (xchg(acquire)) while (load(relaxed));` | `xchg` loop | `rmw acq` loop | `lock_spec` |
| `exchange(release)` | `xchg` | `rmw rel` | `unlock_spec` |
| `store(seq_cst)` | `xchg` | `rmw sc` | `unlock_spec` (same bytes) |
| `store(release)` | `mov` | `store rel` | `IfaceR`: `spinMov`, `Task.movUnlock` (proved) |

## The interface for release stores (`IfaceR`)

`LabOk` rejects a non-draining write to an unowned cell, so the `mov` unlock is not an
`Iface`. `IfaceR` is the same interface with its specs in the logic of `Csl.Rel` (`SafeR`, which
has a release rule for plain stores on TSO): the lock and unlock specs hold from either pending
flag, the lock ends with the flag clear. Clients proved against every `IfaceR` (`ProvedR`) get
their goal on TSO with every `IfaceR` (`Mutex.link_any_mutexR`); `Iface`s whose code drains
first are `IfaceR`s (`IfaceR.ofIface`), and so is the spinlock with the `mov` unlock (`spinMov`).

`Task.movUnlock` (now proved, `movUnlock_holds`) is restated over `ProvedR`. The original
statement, over `Client.Proved`, is kept as `movUnlockIface` and is **false**
(`movUnlockIface_false`): a client body is any Lean function of the two holes, so a client can test
whether its unlock hole is the `mov` code; every `Iface` with that unlock code can never have
its lock held in a consistent state (the `mov` would write an unowned cell), so such a client is
vacuously proved against every `Iface` and still misbehaves when linked with the real `mov`
unlock.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-! ## The interface -/

/-- **The CIR Mutex interface**: CIR code for lock and unlock with CSL specs over an abstract
invariant `inv l R` and an abstract, exclusive lock token `locked l`, and a static initializer.
The specs hold under every frame invariant `J`. -/
structure Iface where
  /-- The object's size in bytes: it occupies `[l, l + size)`. -/
  size : Nat
  /-- The object's cells in the unlocked state. -/
  init : Nat → Heap
  /-- The mutex's share of the resource invariant. -/
  inv : Nat → HProp → HProp
  /-- The lock token of the holder. -/
  locked : Nat → HProp
  /-- `lock`, argument in `rdi`, loops bounded by `L`. -/
  lockCode : Nat → Stmt
  /-- `unlock`, argument in `rdi`, loops bounded by `L`. -/
  unlockCode : Nat → Stmt
  init_dom : ∀ l a, (init l a).isSome → l ≤ a ∧ a < l + size
  init_inv : ∀ l (R : HProp) hR, R hR → Heap.Disjoint (init l) hR →
    inv l R (Heap.union (init l) hR)
  locked_excl : ∀ l h, ¬ (locked l ∗ locked l) h
  lock_spec : ∀ l (R J : HProp) L (rs : Regs), (rs .rdi).toNat = l →
    Csl.Safe (inv l R ∗ J) (fun _ => R ∗ locked l) (lockCode L) rs Heap.empty
  unlock_spec : ∀ l (R J : HProp) L (rs : Regs) h, (rs .rdi).toNat = l → (R ∗ locked l) h →
    Csl.Safe (inv l R ∗ J) (fun _ => hemp) (unlockCode L) rs h

/-- **Derived op** `lock(a)`: `rdi := a; lock`. -/
def Iface.lock (M : Iface) (L : Nat) (a : Expr) : Stmt := .seq (.assign .rdi a) (M.lockCode L)

/-- **Derived op** `unlock(a)`: `rdi := a; unlock`. -/
def Iface.unlock (M : Iface) (L : Nat) (a : Expr) : Stmt := .seq (.assign .rdi a) (M.unlockCode L)

/-- The cells of unlocked mutexes at the addresses `ls`. -/
def initAll (M : Iface) : List Nat → Heap
  | [] => Heap.empty
  | l :: ls => Heap.union (M.init l) (initAll M ls)

/-! ## Clients -/

/-- **A client**: `N` threads whose bodies have holes `lk`, `ul` for the derived ops, its own
initial cells `mem`, and its mutex addresses `locks`, each with `slot` bytes reserved. -/
structure Client where
  N : Nat
  body : (Expr → Stmt) → (Expr → Stmt) → Nat → Stmt
  mem : Heap
  locks : List Nat
  slot : Nat

/-- The start of a client with given derived ops and mutex cells. -/
def Client.startWith (C : Client) (lk ul : Expr → Stmt) (mcells : Heap) : Cfg :=
  ⟨fun t => (if t < C.N then C.body lk ul t else .skip, Regs.zero), Heap.union C.mem mcells⟩

/-- **Linking** a client with a mutex: fill the holes with `M`'s derived ops (loop bound `L`)
and place unlocked mutexes at the client's addresses. -/
def Client.link (C : Client) (M : Iface) (L : Nat) : Cfg :=
  C.startWith (M.lock L) (M.unlock L) (initAll M C.locks)

/-- **The client's contract at `M`**: for every loop bound, a CSL certificate of the linked
start, whose postconditions and invariant imply `goal` (thread registers, final memory) in every
memory containing them. -/
def Client.Sat (C : Client) (goal : (Nat → Regs) → Heap → Prop) (M : Iface) : Prop :=
  ∀ L, ∃ (I : HProp) (Q : Nat → Regs → HProp) (hs : Nat → Heap) (hI : Heap),
    GInv I Q C.N (C.link M L) hs hI ∧
    ∀ (rs : Nat → Regs) (mem : Heap) (hs' : Nat → Heap) (hI' : Heap),
      (∀ t < C.N, Q t (rs t) (hs' t)) → I hI' → (∀ t, Heap.Le (hs' t) mem) → Heap.Le hI' mem →
      goal rs mem

/-- **Proved against the interface**: the contract at every mutex that fits the slots. -/
def Client.Proved (C : Client) (goal : (Nat → Regs) → Heap → Prop) : Prop :=
  ∀ M : Iface, M.size ≤ C.slot → C.Sat goal M

/-! ## The implementation: the spin mutex of `mutex.c` -/

namespace Spin

open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.TvCfg

/-- The token cell of the mutex at `l`: `mutex_t`'s `tok` field. -/
def tok (l : Nat) : Nat := l + 4

/-- **The lock token**: the token cell, any value. -/
def locked (l : Nat) : HProp := fun h => ∃ v, h = Heap.single (tok l) v

/-- **The invariant**: the spinlock invariant with the token next to the resource. -/
def inv (l : Nat) (R : HProp) : HProp := lockInv l (locked l ∗ R)

/-- The unlocked object: lock word `0`, token `0`. -/
def init (l : Nat) : Heap := Heap.union (Heap.single l 0) (Heap.single (tok l) 0)

/-- `xor eax, eax`. -/
def zero : Stmt := .assign .rax (op32 .xor .rax (.reg .rax))

/-- `xchg [rdi], eax` (release). -/
def xchgRel : Stmt := .rmw .rax .rel 4 .xchg (at_ .rdi 0) (.reg .rax)

/-- `xchg [rdi], eax` (seq_cst). -/
def xchgSc : Stmt := .rmw .rax .sc 4 .xchg (at_ .rdi 0) (.reg .rax)

/-- **`mutex_unlock` in CIR** (C11 `exchange(release)`). -/
def unlockCert : GCert where
  start := [zero, xchgRel]
  entries := [ent 0 [zero, xchgRel], ent 2 [xchgRel], ent 4 []]

/-- **`mutex_unlock_sc` in CIR** (C11 `store(seq_cst)`). -/
def unlockScCert : GCert where
  start := [zero, xchgSc]
  entries := [ent 0 [zero, xchgSc], ent 2 [xchgSc], ent 4 []]

/-- The x86 threads of the pinned functions. -/
def all : List (String × List (BitVec 8) × GCert) :=
  [ ("mutex_lock", Code.mutexLock, SpinLock.cert), ("mutex_unlock", Code.mutexUnlock, unlockCert),
    ("mutex_unlock_sc", Code.mutexUnlockSc, unlockScCert) ]

end Spin

/-! ## C11 modes -/

/-- An acquire (or stronger) mode. -/
def acqMode (m : Mode) : Bool := m == .acq || m == .acqRel || m == .sc

/-- A release (or stronger) mode. -/
def relMode (m : Mode) : Bool := m == .rel || m == .acqRel || m == .sc

/-- The memory accesses of a statement, in program order. -/
def accessesOf : Stmt → List Stmt
  | .seq s t => accessesOf s ++ accessesOf t
  | .ite _ s t => accessesOf s ++ accessesOf t
  | .loop _ _ b => accessesOf b
  | s@(.load ..) | s@(.store ..) | s@(.rmw ..) | s@(.local _) | s@(.fence _)
  | s@(.futexWait ..) | s@(.futexWake ..) | s@(.spawn _) | s@(.join _) => [s]
  | _ => []

/-- **The C11 shape of a lock**: only atomic loads and read-modify-writes, every
read-modify-write at least acquire. -/
def c11LockB (s : Stmt) : Bool :=
  (accessesOf s).all fun
    | .load _ m .. => m != .na
    | .rmw _ m .. => acqMode m
    | _ => false

/-- **The C11 shape of an unlock**: only read-modify-writes, each at least release. (A release
*store* is the case of `Task.movUnlock`.) -/
def c11UnlockB (s : Stmt) : Bool :=
  (accessesOf s).all fun
    | .rmw _ m .. => relMode m
    | _ => false

/-- **The modes of a CFG certificate are implemented by its instructions**: at every entry
whose instruction has a CIR effect, `modeOk1` accepts the head statement's mode. -/
def cfgModesOk (t : Tv.XThread) (c : TvCfg.GCert) : Bool :=
  c.entries.all fun e =>
    match Tv.fetchAt t e.off with
    | some (i, _) =>
      match TvCfg.kindOf i, e.cir with
      | some (.op _), s :: _ => C11.modeOk1 i [s]
      | _, _ => true
    | none => true

/-! ## A client proved against the interface -/

namespace Even

/-! `Even`: two threads, one mutex at `m`, a shared cell `x` that is even outside the critical
section, and an output cell per thread. Thread `t` runs

```
lock(m); rbx := [x]; [x] := 1; [out t] := rbx; [x] := rbx; unlock(m)
```

with plain (`na`) accesses. Its critical section exposes the odd value `1` in `x`; with mutual
exclusion no other thread sees it, so both outputs are even. Without the lock a thread can read
the `1` (`Mutex.racy_odd`). -/

/-- The mutex. -/
def m : Nat := 0x100
/-- The shared cell. -/
def x : Nat := 0x200
/-- Thread `t`'s output cell. -/
def out (t : Nat) : Nat := 0x300 + 8 * t

/-- The critical section of thread `t`. -/
def cs (t : Nat) : Stmt :=
  Tv.chain [.load .rbx .na 8 .wb (.lit x), .store .na 8 .wb (.lit x) (.lit 1),
    .store .na 8 .wb (.lit (out t)) (.reg .rbx), .store .na 8 .wb (.lit x) (.reg .rbx)]

/-- Thread `t`, with holes `lk`, `ul` for the derived ops. -/
def body (lk ul : Expr → Stmt) (t : Nat) : Stmt := .seq (lk (.lit m)) (.seq (cs t) (ul (.lit m)))

/-- The client's cells: `x` and both outputs, all `0`. -/
def mem : Heap := fun a => if a = x ∨ a = out 0 ∨ a = out 1 then some 0 else none

/-- **The client.** One mutex at `m`, with an 8-byte slot. -/
def client : Client := ⟨2, body, mem, [m], 8⟩

/-- The resource the mutex protects: `x` holds an even value. -/
def R : HProp := fun h => ∃ v, v % 2 = 0 ∧ h = Heap.single x v

/-- **The client's goal**: both output cells hold even values. -/
def goal (_ : Nat → Regs) (mem : Heap) : Prop := ∀ t < 2, ∃ v, mem (out t) = some v ∧ v % 2 = 0

end Even

/-- The spin mutex with `spin_unlock` (C11 `store(release)`, a plain `mov`) in place of the
exchange: the same lock, the same object. -/
def movUnlockCode (_L : Nat) : Stmt := TvCfg.GCert.body Prim.SpinUnlock.cert 0

/-! ## Concrete instances for the explorer (non-vacuity and mutants) -/

namespace Inst

open Silmaril.X86.Concurrency.Cir.Robust

/-- The loop bound of the instances. -/
def L : Nat := 2

/-- A hole filled with nothing (the racy mutant). -/
def noOp (_ : Expr) : Stmt := .skip

/-- `rdi := a; c`. -/
def call (c : Stmt) (a : Expr) : Stmt := .seq (.assign .rdi a) c

/-- The client's cells as a list. -/
def cells : List (Nat × Nat) := [(Even.x, 0), (Even.out 0, 0), (Even.out 1, 0)]

/-- The two threads of `Even` with given holes. -/
def threads (lk ul : Expr → Stmt) : List (Stmt × Regs) :=
  [(Even.body lk ul 0, Regs.zero), (Even.body lk ul 1, Regs.zero)]

/-- **`Even` linked with the spin mutex** (`mutex_lock`, `mutex_unlock`), loop bound `2`. -/
def linkC : CSt :=
  start (threads (call (Prim.SpinLock.cert.body L)) (call (Spin.unlockCert.body L)))
    (cells ++ [(Even.m, 0), (Spin.tok Even.m, 0)])

/-- **`Even` linked with the spin lock and the `mov`-release unlock** (the instance of
`Task.movUnlock`). -/
def movC : CSt :=
  start (threads (call (Prim.SpinLock.cert.body L)) (call (movUnlockCode L)))
    (cells ++ [(Even.m, 0), (Spin.tok Even.m, 0)])

/-- **`Even` linked with the ticket lock** (`ticket_lock`, `ticket_unlock`), loop bound `2`:
the explorer instance of `Client.linkG ticketMutexG`. -/
def ticketC : CSt :=
  start (threads (call (Prim.TicketLock.cert.body L)) (call (Prim.TicketUnlock.cert.body L)))
    (cells ++ [(Even.m, 0), (Even.m + 4, 0)])

/-- **The racy mutant**: `Even` with both holes empty. -/
def racyC : CSt := start (threads noOp noOp) cells

/-- Both outputs even. -/
def evenOuts (c : CSt) : Bool :=
  (memOf c.mem (Even.out 0)).any (· % 2 == 0) && (memOf c.mem (Even.out 1)).any (· % 2 == 0)

end Inst

/-! ## Mutant certificates for the mode checks -/

namespace ModeMutants

open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.TvCfg

/-- `spin_unlock` (a plain `mov`) claimed `seq_cst`: x86 implements a `seq_cst` store only
with a locked instruction, so the mode check rejects it (the TV checker, which compares modes
away, accepts it). -/
def movSc : GCert where
  start := [.store .sc 4 .wb (at_ .rdi 0) (.lit 0)]
  entries := [ent 0 [.store .sc 4 .wb (at_ .rdi 0) (.lit 0)], ent 6 []]

/-- `mutex_lock` with a relaxed exchange: the modes are implemented (any atomic mode is), but it
is not an acquire, so it does not have the C11 shape of a lock. -/
def lockRlx : Stmt :=
  .seq (.assign .rdx (.lit 1)) (.seq SpinLock.movAX
    (.rmw .rax .rlx 4 .xchg (at_ .rdi 0) (.reg .rax)))

end ModeMutants

/-! ## The interface for release stores -/

/-- **The CIR Mutex interface in the logic with release stores** (`Csl.Rel.SafeR`). As `Iface`,
with the specs as `SafeR` specs under the invariant (ghost ignored, `liftI`): the lock and the
unlock are safe from either pending flag, the lock ends with the flag clear, owning `R` and the
token; the unlock gives them back (possibly by a release store, leaving the flag set). -/
structure IfaceR where
  /-- The object's size in bytes: it occupies `[l, l + size)`. -/
  size : Nat
  /-- The object's cells in the unlocked state. -/
  init : Nat → Heap
  /-- The mutex's share of the resource invariant. -/
  inv : Nat → HProp → HProp
  /-- The lock token of the holder. -/
  locked : Nat → HProp
  /-- `lock`, argument in `rdi`, loops bounded by `L`. -/
  lockCode : Nat → Stmt
  /-- `unlock`, argument in `rdi`, loops bounded by `L`. -/
  unlockCode : Nat → Stmt
  init_dom : ∀ l a, (init l a).isSome → l ≤ a ∧ a < l + size
  init_inv : ∀ l (R : HProp) hR, R hR → Heap.Disjoint (init l) hR →
    inv l R (Heap.union (init l) hR)
  locked_excl : ∀ l h, ¬ (locked l ∗ locked l) h
  lock_spec : ∀ l (R J : HProp) L (rs : Regs) (p : Bool), (rs .rdi).toNat = l →
    Rel.SafeR (Rel.liftI (inv l R ∗ J))
      (fun p' _ h g => p' = false ∧ (R ∗ locked l) h ∧ g = Heap.empty) p (lockCode L) rs
      Heap.empty Heap.empty
  unlock_spec : ∀ l (R J : HProp) L (rs : Regs) (p : Bool) h, (rs .rdi).toNat = l →
    (R ∗ locked l) h →
    Rel.SafeR (Rel.liftI (inv l R ∗ J)) (fun _ _ h g => h = Heap.empty ∧ g = Heap.empty) p
      (unlockCode L) rs h Heap.empty

/-- **Derived op** `lock(a)`. -/
def IfaceR.lock (M : IfaceR) (L : Nat) (a : Expr) : Stmt := .seq (.assign .rdi a) (M.lockCode L)

/-- **Derived op** `unlock(a)`. -/
def IfaceR.unlock (M : IfaceR) (L : Nat) (a : Expr) : Stmt :=
  .seq (.assign .rdi a) (M.unlockCode L)

/-- The cells of unlocked mutexes at the addresses `ls`. -/
def initAllR (M : IfaceR) : List Nat → Heap
  | [] => Heap.empty
  | l :: ls => Heap.union (M.init l) (initAllR M ls)

/-- **Linking** a client with an `IfaceR` mutex. -/
def Client.linkR (C : Client) (M : IfaceR) (L : Nat) : Cfg :=
  C.startWith (M.lock L) (M.unlock L) (initAllR M C.locks)

/-- **The client's contract at `M`** in the logic with release stores: for every loop bound, a
`GInvR` certificate of the linked start whose postconditions and invariant imply `goal`. -/
def Client.SatR (C : Client) (goal : (Nat → Regs) → Heap → Prop) (M : IfaceR) : Prop :=
  ∀ L, ∃ (I : Rel.GProp) (Q : Nat → Bool → Regs → Heap → Heap → Prop) (hs gs : Nat → Heap)
    (hI gI : Heap), Rel.GInvR I Q C.N (C.linkR M L) hs gs hI gI ∧
    ∀ (rs : Nat → Regs) (mem : Heap) (hs' gs' : Nat → Heap) (hI' gI' : Heap) (ps : Nat → Bool),
      (∀ t < C.N, Q t (ps t) (rs t) (hs' t) (gs' t)) → I hI' gI' →
      (∀ t, Heap.Le (hs' t) mem) → Heap.Le hI' mem → goal rs mem

/-- **Proved against the interface with release stores**: the contract at every `IfaceR` that
fits the slots. -/
def Client.ProvedR (C : Client) (goal : (Nat → Regs) → Heap → Prop) : Prop :=
  ∀ M : IfaceR, M.size ≤ C.slot → C.SatR goal M

/-! ## The interface with ghost state -/

/-- A heap assertion with no ghost cells, as a `GProp`. -/
def liftR (R : HProp) : Rel.GProp := fun h g => R h ∧ g = Heap.empty

/-- **The CIR Mutex interface with ghost state**. `IfaceR`'s specs fix the ghost
heap empty and read the invariant through `liftI`, so a mutex whose hand-off is recorded only
in ghost state (the ticket lock) is not an `IfaceR`. Here:

* the mutex's invariant `inv l R` and its token `locked l` are `GProp`s (physical and ghost),
  and a fresh mutex has ghost cells `ginit l`;
* a thread may lock only when `ready` (a ghost-only precondition, which the unlock gives back):
  thread `t` of a client with `N` threads starts with `gthr l t`, which is `ready` when
  `thrOk N` (the ticket lock: `N < 2 ^ 32`, so 32-bit tickets do not wrap among waiters);
* all ghost cells of the mutex at `l` lie in its region `(Nat.unpair a).1 = l`;
* `locked_excl` is exclusivity **relative to the invariant** (two disjoint tokens never coexist
  with an invariant state): a ticket token alone is not exclusive, only with the invariant;
* the specs hold under every ghost-aware frame `J` (`Rel.gsep`), for objects inside the address
  space (`l + size ≤ 2 ^ 64`); the lock is safe from either pending flag and ends with it clear;
  **the unlock starts with the flag clear** (the ticket unlock reads `serving`, an unowned cell,
  which `SafeR`'s side condition forbids while a release is pending).

Every `IfaceR` is an `IfaceG` (`Mutex.IfaceG.ofIfaceR`); the ticket lock is one
(`Mutex.ticketMutexG`). -/
structure IfaceG where
  /-- The object's size in bytes: it occupies `[l, l + size)`. -/
  size : Nat
  /-- The object's cells in the unlocked state. -/
  init : Nat → Heap
  /-- The ghost cells of a fresh mutex. -/
  ginit : Nat → Heap
  /-- The ghost cells thread `t` starts with. -/
  gthr : Nat → Nat → Heap
  /-- The client sizes the mutex supports. -/
  thrOk : Nat → Prop
  /-- The mutex's share of the resource invariant. -/
  inv : Nat → HProp → Rel.GProp
  /-- A thread's ghost state when it may lock. -/
  ready : Nat → Heap → Prop
  /-- The lock token of the holder. -/
  locked : Nat → Rel.GProp
  /-- `lock`, argument in `rdi`, loops bounded by `L`. -/
  lockCode : Nat → Stmt
  /-- `unlock`, argument in `rdi`, loops bounded by `L`. -/
  unlockCode : Nat → Stmt
  init_dom : ∀ l a, (init l a).isSome → l ≤ a ∧ a < l + size
  gdom : ∀ l a, ((ginit l a).isSome ∨ ∃ t, (gthr l t a).isSome) → (Nat.unpair a).1 = l
  gthr_disj : ∀ l t u, t ≠ u → Heap.Disjoint (gthr l t) (gthr l u)
  ginit_disj : ∀ l t, Heap.Disjoint (ginit l) (gthr l t)
  init_inv : ∀ l (R : HProp) hR, R hR → Heap.Disjoint (init l) hR →
    inv l R (Heap.union (init l) hR) (ginit l)
  ready_thr : ∀ l N t, thrOk N → t < N → ready l (gthr l t)
  locked_excl : ∀ l (R : HProp) h g,
    ¬ Rel.gsep (Rel.gsep (locked l) (locked l)) (inv l R) h g
  lock_spec : ∀ l (R : HProp) (J : Rel.GProp) L (rs : Regs) (p : Bool) g,
    (rs .rdi).toNat = l → l + size ≤ 2 ^ 64 → ready l g →
    Rel.SafeR (Rel.gsep (inv l R) J)
      (fun p' _ h g' => p' = false ∧ Rel.gsep (liftR R) (locked l) h g') p (lockCode L) rs
      Heap.empty g
  unlock_spec : ∀ l (R : HProp) (J : Rel.GProp) L (rs : Regs) h g,
    (rs .rdi).toNat = l → l + size ≤ 2 ^ 64 → Rel.gsep (liftR R) (locked l) h g →
    Rel.SafeR (Rel.gsep (inv l R) J) (fun _ _ h' g' => h' = Heap.empty ∧ ready l g') false
      (unlockCode L) rs h g

/-- **Derived op** `lock(a)`. -/
def IfaceG.lock (M : IfaceG) (L : Nat) (a : Expr) : Stmt := .seq (.assign .rdi a) (M.lockCode L)

/-- **Derived op** `unlock(a)`. -/
def IfaceG.unlock (M : IfaceG) (L : Nat) (a : Expr) : Stmt :=
  .seq (.assign .rdi a) (M.unlockCode L)

/-- The cells of unlocked mutexes at the addresses `ls`. -/
def initAllG (M : IfaceG) : List Nat → Heap
  | [] => Heap.empty
  | l :: ls => Heap.union (M.init l) (initAllG M ls)

/-- **Linking** a client with an `IfaceG` mutex. -/
def Client.linkG (C : Client) (M : IfaceG) (L : Nat) : Cfg :=
  C.startWith (M.lock L) (M.unlock L) (initAllG M C.locks)

/-- **The client's contract at `M`** in the logic with ghost state: for every loop bound, a
`GInvR` certificate of the linked start (the client places the ghost cells, using `M.ginit` and
`M.gthr`), whose postconditions and invariant imply `goal`. -/
def Client.SatG (C : Client) (goal : (Nat → Regs) → Heap → Prop) (M : IfaceG) : Prop :=
  ∀ L, ∃ (I : Rel.GProp) (Q : Nat → Bool → Regs → Heap → Heap → Prop) (hs gs : Nat → Heap)
    (hI gI : Heap), Rel.GInvR I Q C.N (C.linkG M L) hs gs hI gI ∧
    ∀ (rs : Nat → Regs) (mem : Heap) (hs' gs' : Nat → Heap) (hI' gI' : Heap) (ps : Nat → Bool),
      (∀ t < C.N, Q t (ps t) (rs t) (hs' t) (gs' t)) → I hI' gI' →
      (∀ t, Heap.Le (hs' t) mem) → Heap.Le hI' mem → goal rs mem

/-- **Proved against the interface with ghost state**: the contract at every `IfaceG` that fits
the slots and supports the client's number of threads. -/
def Client.ProvedG (C : Client) (goal : (Nat → Regs) → Heap → Prop) : Prop :=
  ∀ M : IfaceG, M.size ≤ C.slot → M.thrOk C.N → C.SatG goal M

/-! ## Unlock by a release store -/

/-- **The original statement of `Task.movUnlock`**, over `Client.Proved`. It is
**false** (`Mutex.movUnlockIface_false`): a client is any Lean function of its holes, so
it can test whether its unlock hole is the `mov` code and misbehave only then; every `Iface`
with that unlock code has a lock that never returns in a consistent state, so the client is
vacuously proved against all of them. Kept as the record of the counterexample. -/
def movUnlockIface : Prop :=
  ∀ (C : Client) (goal : (Nat → Regs) → Heap → Prop), C.Proved goal → 8 ≤ C.slot →
    ∀ (L : Nat) (Cf : OCfg),
      OReach .tso C.N (C.startWith
        (fun a => .seq (.assign .rdi a) (Prim.SpinLock.cert.body L))
        (fun a => .seq (.assign .rdi a) (movUnlockCode L))
        (C.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < C.N, (Cf.ts t).1 = .skip) → goal (fun t => (Cf.ts t).2) Cf.mem

/-- **Release by a plain store** (PROVED, `Mutex.movUnlock_holds`). Every client
proved against the interface with release stores (`ProvedR`) gets its goal on TSO when linked
with the spin lock and the `mov`-release unlock.

The first statement (`movUnlockIface`) asked this of clients proved against `Iface` only; it is
false (`movUnlockIface_false`). The plan "the interface fixes the specs, so clients proved against
`Iface` transfer" is imprecise: an `Iface`
certificate says nothing about code the logic rejects. The restated Task quantifies over the
clients the release rule can speak about. Proof: `spinMov : IfaceR` (the spin lock's `Iface` spec
lifted, `spin_unlock` a release of `R ∗ locked` by the release rule) and `link_any_mutexR`
(`Csl.Rel.rel_tso`). Clients proved against `IfaceR` include `Even` (`Even.provedR`), and
mutexes whose code drains first are `IfaceR`s (`IfaceR.ofIface`, e.g. `spinMutexR`). -/
def Task.movUnlock : Prop :=
  ∀ (C : Client) (goal : (Nat → Regs) → Heap → Prop), C.ProvedR goal → 8 ≤ C.slot →
    ∀ (L : Nat) (Cf : OCfg),
      OReach .tso C.N (C.startWith
        (fun a => .seq (.assign .rdi a) (Prim.SpinLock.cert.body L))
        (fun a => .seq (.assign .rdi a) (movUnlockCode L))
        (C.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < C.N, (Cf.ts t).1 = .skip) → goal (fun t => (Cf.ts t).2) Cf.mem

end Silmaril.X86.Concurrency.Cir.Mutex
