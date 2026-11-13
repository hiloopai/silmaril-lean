module

public import Silmaril.Process.Mt.Defs

/-!
# Standard trusted primitives

Abstract, logically atomic specifications (`PrimSpec`) of the synchronisation primitives that
C libraries and allocators build on. Each is **one atomic step** of `MtStep` (the `prim`
arm). Arguments are the System V integer argument registers (`rdi, rsi, rdx, rcx, r8, r9`),
in order.

* **Atomics** (`size ∈ {1, 2, 4, 8}`, naturally aligned): `load a`, `store a v`, `xchg a v`
  (returns the old value), `cas a e v` (returns the old value; writes `v` iff it was `e`),
  `fadd a v` (returns the old value; adds modulo `2 ^ (8 size)`), and `fence`;
* **Mutex** (`a` names the lock): `mutexLock a` acquires a free lock (blocks while another
  thread holds it; locking a lock the caller holds is a fault: glibc's default mutex would
  deadlock), `mutexTrylock a` acquires or returns `EBUSY` (16), `mutexUnlock a` releases a
  lock the caller holds (otherwise a fault);
* **Recursive lock** (glibc's `_IO_lock_t`, `PTHREAD_MUTEX_RECURSIVE`): `recLock a` acquires a
  free lock or increments the caller's depth, `recUnlock a` decrements it and releases at `0`;
* **MPSC list** (mimalloc's `xthread_free` / `thread_delayed_free`, jemalloc's remote frees):
  `mpscPush head node off` links `node` in front (stores the old head at `node + off`, then
  `head := node`), `mpscTakeAll head` swaps the head with `0` and returns the old list.

Footprints (`fp`): an atomic's bytes, the list's head word (and, for `mpscPush`, the link
word of the pushed node); the locks have none, since their state is abstract.

Locks keep their state **abstractly**, in `PrimSt.locks` (owner, depth): the lock word in
memory is the implementation's business. Relating the two is the job of a primitive's
correctness proof under a memory model (an explicit, separate assumption), which also needs
that plain code never touches the lock word.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Prim

open Silmaril.X86 (Word)

/-- `n` bytes at `a`, readable, as a little-endian number. -/
def rd (m : Memory) (a n : Nat) : Option Nat := (m.readBytes a n).map decLE

/-- Write the `n` low bytes of `v` at `a` (write-permitted). -/
def wr (m : Memory) (a n : Nat) (v : Nat) : Option Memory := m.writeBytes a (le n (BitVec.ofNat 64 v))

/-- A supported atomic access: 1, 2, 4 or 8 bytes, naturally aligned. -/
def Aligned (a n : Nat) : Prop := (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) ∧ a % n = 0

/-- Readable and writable. -/
def RW (m : Memory) (a n : Nat) : Prop := m.Permitted .read a n ∧ m.Permitted .write a n

instance (a n : Nat) : Decidable (Aligned a n) := by unfold Aligned; infer_instance
instance (m : Memory) (a n : Nat) : Decidable (RW m a n) := by unfold RW; infer_instance

/-- Argument `i` (`0`: `rdi`), as a number. -/
def arg (args : List Word) (i : Nat) : Nat := (args.getD i 0).toNat

/-- `EBUSY`. -/
def eBusy : Word := 16

variable {γ : Type}

/-- An atomic read-modify-write of `n` bytes at `arg 0`: from the old value `o` and the
arguments, the new value (`none`: no write) and the result. -/
def rmw (n : Nat) (f : Nat → List Word → Option Nat × Nat) : PrimSpec γ where
  pre _ args sh := Aligned (arg args 0) n ∧ RW sh.mem (arg args 0) n
  fp _ args a := arg args 0 ≤ a ∧ a < arg args 0 + n
  post _ args sh ret sh2 := ∃ o, rd sh.mem (arg args 0) n = some o ∧
    ret = BitVec.ofNat 64 (f o args).2 ∧ sh2.ps = sh.ps ∧ sh2.g = sh.g ∧
    match (f o args).1 with
    | none => sh2.mem = sh.mem
    | some v => wr sh.mem (arg args 0) n v = some sh2.mem

/-- `load a`. -/
def load (n : Nat) : PrimSpec γ := rmw n fun o _ => (none, o)

/-- `store a v`. -/
def store (n : Nat) : PrimSpec γ := rmw n fun _ args => (some (arg args 1 % 2 ^ (8 * n)), 0)

/-- `xchg a v`: returns the old value. -/
def xchg (n : Nat) : PrimSpec γ := rmw n fun o args => (some (arg args 1 % 2 ^ (8 * n)), o)

/-- `cas a e v`: returns the old value; writes `v` iff it equals `e`. -/
def cas (n : Nat) : PrimSpec γ :=
  rmw n fun o args => (if o = arg args 1 % 2 ^ (8 * n) then some (arg args 2 % 2 ^ (8 * n)) else none, o)

/-- `fadd a v`: returns the old value. -/
def fadd (n : Nat) : PrimSpec γ := rmw n fun o args => (some ((o + arg args 1) % 2 ^ (8 * n)), o)

/-- `fence`: no effect (every primitive step is a full barrier). -/
def fence : PrimSpec γ where
  fp _ _ _ := False
  pre _ _ _ := True
  post _ _ sh ret sh2 := ret = 0 ∧ sh2 = sh

/-- Only the lock table changes, to `f`. -/
def SetLocks (sh sh2 : Sh γ) (f : Nat → Option (Nat × Nat)) : Prop :=
  sh2.mem = sh.mem ∧ sh2.g = sh.g ∧ sh2.ps = { locks := f }

/-- `mutexLock a`: acquire a free lock; a lock the caller holds is a fault. -/
def mutexLock : PrimSpec γ where
  fp _ _ _ := False
  pre t args sh := ∀ d, sh.ps.locks (arg args 0) ≠ some (t, d)
  post t args sh ret sh2 := sh.ps.locks (arg args 0) = none ∧ ret = 0 ∧
    SetLocks sh sh2 (upd sh.ps.locks (arg args 0) (some (t, 1)))

/-- `mutexTrylock a`: acquire a free lock, or return `EBUSY`. -/
def mutexTrylock : PrimSpec γ where
  fp _ _ _ := False
  pre t args sh := ∀ d, sh.ps.locks (arg args 0) ≠ some (t, d)
  post t args sh ret sh2 :=
    (sh.ps.locks (arg args 0) = none ∧ ret = 0 ∧
      SetLocks sh sh2 (upd sh.ps.locks (arg args 0) (some (t, 1)))) ∨
    ((sh.ps.locks (arg args 0)).isSome ∧ ret = eBusy ∧ sh2 = sh)

/-- `mutexUnlock a`: release a lock the caller holds. -/
def mutexUnlock : PrimSpec γ where
  fp _ _ _ := False
  pre t args sh := sh.ps.locks (arg args 0) = some (t, 1)
  post _ args sh ret sh2 := ret = 0 ∧ SetLocks sh sh2 (upd sh.ps.locks (arg args 0) none)

/-- `recLock a`: acquire a free lock, or increment the caller's depth. -/
def recLock : PrimSpec γ where
  fp _ _ _ := False
  pre _ _ _ := True
  post t args sh ret sh2 := ret = 0 ∧
    ((sh.ps.locks (arg args 0) = none ∧ SetLocks sh sh2 (upd sh.ps.locks (arg args 0) (some (t, 1)))) ∨
     ∃ d, sh.ps.locks (arg args 0) = some (t, d) ∧
       SetLocks sh sh2 (upd sh.ps.locks (arg args 0) (some (t, d + 1))))

/-- `recUnlock a`: decrement the caller's depth, releasing at `0`. -/
def recUnlock : PrimSpec γ where
  fp _ _ _ := False
  pre t args sh := ∃ d, 0 < d ∧ sh.ps.locks (arg args 0) = some (t, d)
  post t args sh ret sh2 := ret = 0 ∧ ∃ d, sh.ps.locks (arg args 0) = some (t, d) ∧
    SetLocks sh sh2 (upd sh.ps.locks (arg args 0) (if d ≤ 1 then none else some (t, d - 1)))

/-- `mpscPush head node off`: `[node + off] := [head]; [head] := node`, atomically. -/
def mpscPush : PrimSpec γ where
  fp _ args a := (arg args 0 ≤ a ∧ a < arg args 0 + 8) ∨
    (arg args 1 + arg args 2 ≤ a ∧ a < arg args 1 + arg args 2 + 8)
  pre _ args sh := Aligned (arg args 0) 8 ∧ RW sh.mem (arg args 0) 8 ∧
    sh.mem.Permitted .write (arg args 1 + arg args 2) 8
  post _ args sh ret sh2 := ret = 0 ∧ sh2.ps = sh.ps ∧ sh2.g = sh.g ∧
    ∃ o m1, rd sh.mem (arg args 0) 8 = some o ∧ wr sh.mem (arg args 1 + arg args 2) 8 o = some m1 ∧
      wr m1 (arg args 0) 8 (arg args 1) = some sh2.mem

/-- `mpscTakeAll head`: `[head] := 0`, returning the old head. -/
def mpscTakeAll : PrimSpec γ where
  fp _ args a := arg args 0 ≤ a ∧ a < arg args 0 + 8
  pre t args sh := (xchg (γ := γ) 8).pre t [args.getD 0 0, 0] sh
  post t args sh ret sh2 := (xchg (γ := γ) 8).post t [args.getD 0 0, 0] sh ret sh2

/-! ## The standard table -/

/-- The standard primitives. -/
inductive Std where
  | fence
  | load (n : Nat) | store (n : Nat) | xchg (n : Nat) | cas (n : Nat) | fadd (n : Nat)
  | mutexLock | mutexTrylock | mutexUnlock | recLock | recUnlock
  | mpscPush | mpscTakeAll
  deriving DecidableEq, Repr

/-- The specification of a standard primitive. -/
def Std.spec : Std → PrimSpec γ
  | .fence => Prim.fence
  | .load n => Prim.load n
  | .store n => Prim.store n
  | .xchg n => Prim.xchg n
  | .cas n => Prim.cas n
  | .fadd n => Prim.fadd n
  | .mutexLock => Prim.mutexLock
  | .mutexTrylock => Prim.mutexTrylock
  | .mutexUnlock => Prim.mutexUnlock
  | .recLock => Prim.recLock
  | .recUnlock => Prim.recUnlock
  | .mpscPush => Prim.mpscPush
  | .mpscTakeAll => Prim.mpscTakeAll

/-- The primitive numbers: `fence` 0; `load`, `store`, `xchg`, `cas`, `fadd` of size `n` at
`16 k + n` (`k = 1 … 5`); the locks 100–104; the list 110–111. -/
def Std.id : Std → Nat
  | .fence => 0
  | .load n => 16 + n | .store n => 32 + n | .xchg n => 48 + n | .cas n => 64 + n
  | .fadd n => 80 + n
  | .mutexLock => 100 | .mutexTrylock => 101 | .mutexUnlock => 102 | .recLock => 103
  | .recUnlock => 104 | .mpscPush => 110 | .mpscTakeAll => 111

/-- Every standard primitive, once. -/
def Std.all : List Std :=
  [.fence, .mutexLock, .mutexTrylock, .mutexUnlock, .recLock, .recUnlock, .mpscPush, .mpscTakeAll] ++
    ([1, 2, 4, 8].flatMap fun n => [.load n, .store n, .xchg n, .cas n, .fadd n])

/-- **The standard primitive table.** -/
def table : PrimTable γ := fun p => (Std.all.find? (·.id == p)).map Std.spec

end Silmaril.Process.Mt.Prim

namespace Silmaril.Process.Mt.Prim

open Silmaril.X86 (Word)

variable {γ : Type}

/-! ## Executable primitives (for running examples) -/

/-- Run an atomic read-modify-write. -/
def execRmw (n : Nat) (f : Nat → List Word → Option Nat × Nat) (args : List Word) (sh : Sh γ) :
    Option (Word × Sh γ) :=
  if Aligned (arg args 0) n ∧ RW sh.mem (arg args 0) n then
    match rd sh.mem (arg args 0) n with
    | some o =>
      match (f o args).1 with
      | none => some (BitVec.ofNat 64 (f o args).2, sh)
      | some v =>
        (wr sh.mem (arg args 0) n v).map fun m => (BitVec.ofNat 64 (f o args).2, { sh with mem := m })
    | none => none
  else none

/-- Run a standard primitive: its result and shared state, or `none` (blocked, outside its
precondition, or not executable here: `recLock`, `recUnlock`, `mutexTrylock`, the list). -/
def Std.exec : Std → Nat → List Word → Sh γ → Option (Word × Sh γ)
  | .fence, _, _, sh => some (0, sh)
  | .load n, _, args, sh => execRmw n (fun o _ => (none, o)) args sh
  | .store n, _, args, sh => execRmw n (fun _ args => (some (arg args 1 % 2 ^ (8 * n)), 0)) args sh
  | .xchg n, _, args, sh => execRmw n (fun o args => (some (arg args 1 % 2 ^ (8 * n)), o)) args sh
  | .cas n, _, args, sh => execRmw n (fun o args =>
      (if o = arg args 1 % 2 ^ (8 * n) then some (arg args 2 % 2 ^ (8 * n)) else none, o)) args sh
  | .fadd n, _, args, sh => execRmw n (fun o args => (some ((o + arg args 1) % 2 ^ (8 * n)), o)) args sh
  | .mutexLock, t, args, sh =>
    if sh.ps.locks (arg args 0) = none then
      some (0, { sh with ps := { locks := upd sh.ps.locks (arg args 0) (some (t, 1)) } })
    else none
  | .mutexUnlock, t, args, sh =>
    if sh.ps.locks (arg args 0) = some (t, 1) then
      some (0, { sh with ps := { locks := upd sh.ps.locks (arg args 0) none } })
    else none
  | _, _, _, _ => none

/-- Run primitive number `p` of the standard table. -/
def execTable (p t : Nat) (args : List Word) (sh : Sh γ) : Option (Word × Sh γ) :=
  (Std.all.find? (·.id == p)).bind fun s => s.exec t args sh

end Silmaril.Process.Mt.Prim
