module

public import Silmaril.X86.Concurrency.Cir.Prim.Clients.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Pairing

/-!
# The synchronisation primitives: open goals for every client

`Prim/Thms.lean` proves the
locks' mutual exclusion, the seqlock's snapshot and the ring's FIFO order for one closed client
each, by exhaustive exploration of the CIR-native TSO machine. The statements for every client
(any number of threads, any critical section or values, any loop bound) are open, stated here on
the same machine, with plans. `Task.spinMutexTso` is proved (`Prim/Tasks/Thms`), and
so is `Task.ticketMutexTso`; `Task.seqlockTso` is proved and `Task.spscFifoTso` is
restated and proved (the original SPSC
statement is kept as `spscFifoTsoPrim` and refuted). None of the four stays open.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Prim.Clients

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Prim

/-! ## Open goals: the statements for every client

The explorer proves the statements above for one instance each. The client-independent
statements are open; each is stated on the same CIR-native TSO machine. -/

/-- A two-cell-or-more start: the given cells, empty elsewhere. -/
def heapOf (l : List (Nat × Nat)) (h : Csl.Heap) : Csl.Heap :=
  fun a => ((l.find? (·.1 == a)).map (·.2)).or (h a)

/-- The ghost token of `spinInvG`. -/
def spinTk : Csl.Heap := Csl.Heap.single 0 0

/-- **The spinlock's invariant with a ghost token** (for the release rule of
`Csl.Rel`): the word is `0` and the invariant holds `R` and the token, or the word is not `0`
and it holds neither. -/
def spinInvG (l : Nat) (R : Csl.HProp) : Csl.Rel.GProp := fun hI gI =>
  (∃ hR, R hR ∧ Csl.Heap.Disjoint (Csl.Heap.single l 0) hR ∧
      hI = Csl.Heap.union (Csl.Heap.single l 0) hR ∧ gI = spinTk) ∨
    (∃ v, v ≠ 0 ∧ hI = Csl.Heap.single l v ∧ gI = Csl.Heap.empty)

/-! ## The ticket lock's ghost state

Ghost cells of the ticket lock at `l` are `tkA l c k = Nat.pair l (4k + c)` (so each lock has its
own ghost region, `(Nat.unpair a).1 = l`), of four kinds, all with value `0`:

* `c = 0`, `T k`: **ticket `k` drawn** and its owner waiting;
* `c = 1`, `G k`: **turn `k` held** (the lock's holder);
* `c = 2`, `U k`: **receipt** of turn `k` (kept by the thread that held it);
* `c = 3`, `D u`: **permit `u`** (a thread may draw a ticket only with a permit; `u < B`).

The invariant counts with unbounded **virtual** counters `Nv` (tickets drawn) and `Sv` (turns
finished); memory holds them modulo `2 ^ 32`. The permits deposited by threads holding a drawn
ticket bound the number of tickets in flight by `B`, so with `B < 2 ^ 32` a waiting thread's
32-bit comparison is exact. -/

/-- A ghost cell of the ticket lock at `l`: kind `c`, index `k`. -/
def tkA (l c k : Nat) : Nat := Nat.pair l (4 * k + c)

/-- The ghost heap of the lock at `l` with the cells `(c, k)` satisfying `P` (all of value `0`). -/
noncomputable def gsetL (l : Nat) (P : Nat → Nat → Prop) : Csl.Heap := fun a =>
  open Classical in if ∃ c k, c < 4 ∧ P c k ∧ a = tkA l c k then some 0 else none

/-- **The lock's ghost cells**, with `Sv` turns finished, `Nv` tickets drawn, the permits `S`
deposited, and the current turn claimed (`cl`) or not. -/
def tkSet (Sv Nv : Nat) (S : Finset Nat) (cl : Bool) : Nat → Nat → Prop := fun c k =>
  (c = 0 ∧ (k < Sv ∨ (cl = true ∧ k = Sv) ∨ Nv ≤ k)) ∨ (c = 1 ∧ ¬ (cl = true ∧ k = Sv)) ∨
    (c = 2 ∧ (Sv < k ∨ (cl = false ∧ k = Sv))) ∨ (c = 3 ∧ k ∈ S)

/-- The two words: `next = Nv`, `serving = Sv` (32 bits). -/
def tkObj (l Nv Sv : Nat) : Csl.Heap :=
  Csl.Heap.union (Csl.Heap.single l (Nv % 2 ^ 32)) (Csl.Heap.single (l + 4) (Sv % 2 ^ 32))

/-- **The ticket lock's invariant with ghost state**, for at most `B` permits.
`Sv ≤ Nv`; the tickets in flight (`Nv - Sv`, of which one is the holder's when the turn is
claimed) are at most the deposited permits, all below `B`. The turn `Sv` is unclaimed (the
invariant holds `R`, `G Sv` and `U Sv`) or claimed (its holder has them, and gave back `T Sv`). -/
def ticketInvG (l B : Nat) (R : Csl.HProp) : Csl.Rel.GProp := fun hI gI =>
  ∃ (Nv Sv : Nat) (S : Finset Nat) (cl : Bool), Sv ≤ Nv ∧ (∀ u ∈ S, u < B) ∧
    (cl = true → Sv < Nv ∧ Nv - Sv ≤ S.card + 1) ∧ (cl = false → Nv - Sv ≤ S.card) ∧
    gI = gsetL l (tkSet Sv Nv S cl) ∧
    ((cl = true ∧ hI = tkObj l Nv Sv) ∨
      (cl = false ∧ ∃ hR, R hR ∧ Csl.Heap.Disjoint (tkObj l Nv Sv) hR ∧
        hI = Csl.Heap.union (tkObj l Nv Sv) hR))

/-- A thread ready to lock: permit `u`, receipts `F`. -/
def tkReady (u : Nat) (F : Nat → Prop) : Nat → Nat → Prop := fun c k =>
  (c = 3 ∧ k = u) ∨ (c = 2 ∧ F k)

/-- A thread waiting with ticket `k`, receipts `F`. -/
def tkWait (k : Nat) (F : Nat → Prop) : Nat → Nat → Prop := fun c j =>
  (c = 0 ∧ j = k) ∨ (c = 2 ∧ F j)

/-- A thread holding turn `k`, with permit `u` and receipts `F` and `k`. -/
def tkHeld (k u : Nat) (F : Nat → Prop) : Nat → Nat → Prop := fun c j =>
  (c = 1 ∧ j = k) ∨ (c = 3 ∧ j = u) ∨ (c = 2 ∧ (F j ∨ j = k))

/-- **A thread ready to lock** the ticket lock at `l` (for `Mutex.IfaceG`): a
permit `u < B` and any receipts. -/
def tkReadyG (l B : Nat) (g : Csl.Heap) : Prop :=
  ∃ u F, u < B ∧ g = gsetL l (tkReady u F)

/-- **The ticket lock's token** (for `Mutex.IfaceG`): no physical cell; a turn `k`,
a permit `u < B` and receipts. Exclusive only together with the invariant
(`Prim.Clients.tk_locked_excl`). -/
def tkLockedG (l B : Nat) : Csl.Rel.GProp := fun h g =>
  h = Csl.Heap.empty ∧ ∃ k u F, u < B ∧ g = gsetL l (tkHeld k u F)

/-- `N` threads, thread `t` running `chain [lock, cs t, unlock]` with `rdi = l`. -/
def lockCfg (lock unlock : Stmt) (N l : Nat) (cs : Nat → Stmt) (mem : Csl.Heap) : Csl.Cfg :=
  ⟨fun t => (if t < N then Tv.chain [lock, cs t, unlock] else .skip, regs [(.rdi, l)]), mem⟩

/-- **The spinlock is a lock on TSO, for every client** (PROVED,
`Prim.Clients.spinMutexTso_holds`, by the release rule of `Csl.Rel` with the ghost-token invariant
`spinInvG`). Let `N` threads each run
`spin_lock; cs t; spin_unlock` (the translation-validated bodies, loop bound `L`) on a lock word
`l` that is initially `0`, next to a heap `hR0` satisfying `R`. If every critical section is
CSL-safe from any heap satisfying `R` back to `R`, with no shared invariant, and keeps `rdi`, then
every finished, drained TSO state contains a heap satisfying `R` and the lock word is `0`.

Plan. `spinLock_acquire` is the acquire half in the logic. The release half is a plain `mov`,
which the `LabOk` rejects (a non-draining write to a cell it does not own). Extend `LabOk` with
a **release** clause: a non-draining atomic store to an invariant cell may give up ownership,
provided the thread then performs no atomic load of a cell it does not own before its next
draining label (a triangular-race-freedom side condition, Owens 2010; here the unlock is the
thread's last action). Prove the SC adequacy of the extended logic (as `csl_sc`), and the
buffered-to-SC simulation with *delayed* release: a buffered release is installed in the SC
abstraction only when it is flushed; FIFO flushing makes every earlier store of the thread
visible first, and the side condition makes the thread's later steps commute with the delay.
Checked for `N = 2`, `L = 2` and the increment client (`spin_mutex`, `spin_robust`). -/
def Task.spinMutexTso : Prop :=
  ∀ (N L l : Nat) (R : Csl.HProp) (hR0 : Csl.Heap) (cs : Nat → Stmt), l < 2 ^ 64 →
    hR0 l = none → R hR0 → (∀ t, .rdi ∉ (cs t).writes) →
    (∀ t rs h, R h → Csl.Safe (fun h => h = Csl.Heap.empty) (fun _ h' => R h') (cs t) rs h) →
    ∀ C : Csl.OCfg, Csl.OReach .tso N
      (lockCfg (SpinLock.cert.body L) (SpinUnlock.cert.body L) N l cs (heapOf [(l, 0)] hR0)).toO C →
      C.Drained → (∀ t < N, (C.ts t).1 = .skip) →
      C.mem l = some 0 ∧ ∃ hR, R hR ∧ Csl.Heap.Le hR C.mem

/-- **The ticket lock is a lock on TSO, for every client** (PROVED,
`Prim.Clients.ticketMutexTso_holds`, by the release rule of `Csl.Rel` with the ghost invariant
`ticketInvG`; the statement is unchanged). As `Task.spinMutexTso`, with
`next` at `l` and `serving` at `l + 4`, both initially `0`; at the end `next = serving = N`.
The plan, kept: as for the spinlock, but the CSL proof of `ticket_lock` needs ghost state
(the hand-off
from the releasing thread to the next ticket is observed by a plain load of `serving`, which
does not change memory, so a single resource invariant cannot record who holds `R`); the logic
has none. A ticket ghost map (ticket `k` holds `R` once `serving = k`) in the invariant, plus the
release clause of `Task.spinMutexTso`. Checked for `N = 2`, `L = 2` (`tick_mutex`,
`tick_robust`).

The hypothesis `N < 2 ^ 32` was added. The tickets are 32-bit (`lock xadd` on a
dword), so with `2 ^ 32 + 1` threads the counters wrap: the final `next` is `N % 2 ^ 32`, and two
threads can hold the same ticket. The statement without the bound was false. -/
def Task.ticketMutexTso : Prop :=
  ∀ (N L l : Nat) (R : Csl.HProp) (hR0 : Csl.Heap) (cs : Nat → Stmt), N < 2 ^ 32 →
    l + 8 < 2 ^ 64 → hR0 l = none → hR0 (l + 4) = none → R hR0 → (∀ t, .rdi ∉ (cs t).writes) →
    (∀ t rs h, R h → Csl.Safe (fun h => h = Csl.Heap.empty) (fun _ h' => R h') (cs t) rs h) →
    ∀ C : Csl.OCfg, Csl.OReach .tso N
      (lockCfg (TicketLock.cert.body L) (TicketUnlock.cert.body L) N l cs
        (heapOf [(l, 0), (l + 4, 0)] hR0)).toO C →
      C.Drained → (∀ t < N, (C.ts t).1 = .skip) →
      C.mem l = some N ∧ C.mem (l + 4) = some N ∧ ∃ hR, R hR ∧ Csl.Heap.Le hR C.mem

/-- **The seqlock protocol on TSO, for any writes and readers** (PROVED as stated,
`Prim.Clients.seqlockTso_holds`, with the single-writer logic of
`Proofs/…/Prim/Tasks/Sw.lean`: memory's `seq` and data words are functions of the number of
the writer's stores flushed, a reader's four loads read memory at non-decreasing flush counts,
and two equal even reads of `seq` pin that count to a multiple of `4`). One writer runs
`seq_write(s, a, b)` for each pair of `ws` in turn; `M` readers each run `seq_read(s, out_j)`
into their own two cells. At every finished, drained TSO state, each reader's output is the
initial pair `(0, 0)` or one of the written pairs. Plan: an invariant of the TSO machine over
the writer's buffer: memory's `seq` is even exactly when memory's data words are the pair of the
last completed write, and a reader whose two reads of `seq` agree and are even read no store of
the writer in between (TSO keeps the writer's stores in order and the reader's loads in order).
Checked for one write `(1, 1)` and one reader (`seq_snapshot`, `seq_robust`).

Three hypotheses were added; without them the statement was false.
* `ws.length < 2 ^ 31`: `seq` is a 32-bit word advanced by `2` per write, so after `2 ^ 31`
  writes it is `0` again; a reader that read `seq = 0` and `a`, then (after `2 ^ 31` writes)
  `b` and `seq = 0` again, accepts a torn pair (ABA).
* Each output pair `[o, o + 8)` lies inside the address space and is disjoint from the seqlock
  `[s, s + 12)`: with `o = s + 4` the reader's plain output stores interleave with the writer's
  data stores, and the final cells can hold a torn pair.
* The output pairs are pairwise disjoint: with `outs = [o, o + 4]` two readers overwrite each
  other's halves. -/
def Task.seqlockTso : Prop :=
  ∀ (L s : Nat) (ws : List (Nat × Nat)) (outs : List Nat), s + 12 < 2 ^ 64 →
    (∀ p ∈ ws, p.1 < 2 ^ 32 ∧ p.2 < 2 ^ 32) → ws.length < 2 ^ 31 →
    (∀ o ∈ outs, o + 8 ≤ 2 ^ 64 ∧ (o + 8 ≤ s ∨ s + 12 ≤ o)) →
    outs.Pairwise (fun o o' => o + 8 ≤ o' ∨ o' + 8 ≤ o) →
    let writer : Stmt := Tv.chain (ws.map fun p => Tv.chain [.assign .rsi (.lit p.1),
      .assign .rdx (.lit p.2), SeqWrite.cert.body L])
    let N := outs.length + 1
    let C0 : Csl.Cfg := ⟨fun t =>
      if t = 0 then (writer, regs [(.rdi, s)])
      else if t < N then (SeqRead.cert.body L, regs [(.rdi, s), (.rsi, outs.getD (t - 1) 0)])
      else (.skip, Regs.zero),
      heapOf ([(s, 0), (s + 4, 0), (s + 8, 0)] ++ outs.flatMap fun o => [(o, 0), (o + 4, 0)])
        Csl.Heap.empty⟩
    ∀ C : Csl.OCfg, Csl.OReach .tso N C0.toO C → C.Drained → (∀ t < N, (C.ts t).1 = .skip) →
      ∀ o ∈ outs, ∃ p ∈ (0, 0) :: ws, C.mem o = some p.1 ∧ C.mem (o + 4) = some p.2

/-- **The first statement of the SPSC goal** (**FALSE**,
`Prim.Clients.spscFifoTsoPrim_false`). The producer pushes the nonzero values `vs` in turn; the
consumer pops `k` times into the cells `out + 4i`; the claim was that the successful pops (the
nonzero outputs) are the first values of `vs`, in order.

Why it is false: `spsc_push` **drops** its value when the ring is full (it returns `0`), and the
client does not retry, so the successfully pushed values are a subsequence of `vs`, not a
prefix. With `vs = [1, 2, 3, 4]` and `k = 3`: push `1` and `2`, push `3` finds the ring full,
pop `1`, push `4`, pop `2`, pop `4`. The outputs are `[1, 2, 4]`, not `[1, 2, 3]`. This run is
even sequentially consistent; `spscFifoTsoPrim_false` replays it on the TSO machine. The goal is
restated as `Task.spscFifoTso` (the producer records each push's result).

The hypothesis that the output cells `[out, out + 4k)` are disjoint from the ring
`[q, q + 16)` was added. With `out = q` the first pop's output store overwrites `head`. -/
def spscFifoTsoPrim : Prop :=
  ∀ (L q out k : Nat) (vs : List Nat), q + 16 < 2 ^ 64 → out + 4 * k < 2 ^ 64 →
    (out + 4 * k ≤ q ∨ q + 16 ≤ out) →
    (∀ v ∈ vs, 0 < v ∧ v < 2 ^ 32) →
    let prod : Stmt :=
      Tv.chain (vs.map fun v => Tv.chain [.assign .rsi (.lit v), SpscPush.cert.body L])
    let cons : Stmt := Tv.chain ((List.range k).map fun i =>
      Tv.chain [.assign .rsi (.lit (out + 4 * i)), SpscPop.cert.body L])
    let C0 : Csl.Cfg := ⟨fun t =>
      if t = 0 then (prod, regs [(.rdi, q)]) else if t = 1 then (cons, regs [(.rdi, q)])
      else (.skip, Regs.zero),
      heapOf ([(q, 0), (q + 4, 0), (q + 8, 0), (q + 12, 0)] ++
        (List.range k).map fun i => (out + 4 * i, 0)) Csl.Heap.empty⟩
    ∀ C : Csl.OCfg, Csl.OReach .tso 2 C0.toO C → C.Drained → (∀ t < 2, (C.ts t).1 = .skip) →
      let got := ((List.range k).map fun i => (C.mem (out + 4 * i)).getD 0).filter (· != 0)
      got = vs.take got.length

/-- **The SPSC ring is FIFO and loses nothing on TSO, for any pushes and pops** (PROVED,
`Prim.Clients.spscFifoTso_holds`; restated from `spscFifoTsoPrim`, which is false).

The producer calls `spsc_push(vs[j])` for each `j` in turn and records the result (`1`: pushed,
`0`: the ring was full and the value was dropped) with a plain store to its own cell
`res + 4j`; the consumer pops `k` times into the cells `out + 4i`. At every finished, drained
TSO state, let `got` be the successful pops' values (the nonzero outputs), `pushed` the values
whose push succeeded, in order, and `rem` the values still in the ring (from `head` to `tail`).
Then `got ++ rem = pushed`: every pushed value is popped once, in order, or is still queued;
nothing is lost, duplicated or reordered.

The client is not SC-robust (`spsc_not_robust`), so the argument is TSO-specific (`Sw`): the
slot store precedes the `tail` store that publishes it in the producer's buffer, the
consumer's loads read memory in order, and the producer overwrites a slot only after reading
a `head` past it; stale index reads only make a push see a full ring or a pop an empty one.

Compared with the first statement: the producer's result stores are new (authored glue, as the
argument registers), with in-range and disjointness hypotheses for `[res, res + 4·|vs|)`. -/
def Task.spscFifoTso : Prop :=
  ∀ (L q out res k : Nat) (vs : List Nat), q + 16 < 2 ^ 64 → out + 4 * k < 2 ^ 64 →
    res + 4 * vs.length < 2 ^ 64 →
    (out + 4 * k ≤ q ∨ q + 16 ≤ out) → (res + 4 * vs.length ≤ q ∨ q + 16 ≤ res) →
    (res + 4 * vs.length ≤ out ∨ out + 4 * k ≤ res) →
    (∀ v ∈ vs, 0 < v ∧ v < 2 ^ 32) →
    let prod : Stmt := Tv.chain ((List.range vs.length).map fun j =>
      Tv.chain [.assign .rsi (.lit (vs.getD j 0)), SpscPush.cert.body L,
        .store .na 4 .wb (.lit (res + 4 * j)) (.reg .rax)])
    let cons : Stmt := Tv.chain ((List.range k).map fun i =>
      Tv.chain [.assign .rsi (.lit (out + 4 * i)), SpscPop.cert.body L])
    let C0 : Csl.Cfg := ⟨fun t =>
      if t = 0 then (prod, regs [(.rdi, q)]) else if t = 1 then (cons, regs [(.rdi, q)])
      else (.skip, Regs.zero),
      heapOf ([(q, 0), (q + 4, 0), (q + 8, 0), (q + 12, 0)] ++
        ((List.range k).map fun i => (out + 4 * i, 0)) ++
        (List.range vs.length).map fun j => (res + 4 * j, 0)) Csl.Heap.empty⟩
    ∀ C : Csl.OCfg, Csl.OReach .tso 2 C0.toO C → C.Drained → (∀ t < 2, (C.ts t).1 = .skip) →
      let got := ((List.range k).map fun i => (C.mem (out + 4 * i)).getD 0).filter (· != 0)
      let pushed := ((List.range vs.length).filter fun j => C.mem (res + 4 * j) == some 1).map
        fun j => vs.getD j 0
      let h := (C.mem q).getD 0
      let n := ((C.mem (q + 4)).getD 0 + 2 ^ 32 - h) % 2 ^ 32
      let rem := (List.range n).map fun j => (C.mem (q + 8 + 4 * ((h + j) % 2))).getD 0
      got ++ rem = pushed

end Silmaril.X86.Concurrency.Cir.Prim.Clients
