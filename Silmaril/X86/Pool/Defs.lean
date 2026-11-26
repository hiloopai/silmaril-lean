module

public import Silmaril.X86.MemEvent.Thms
public import Silmaril.X86.Safe.Stable.Defs
public import Silmaril.X86.MemoryModel.Tso.Defs

/-!
# Thread pools, disjoint parallelism and the frozen DRF statement

Everything here is
additive: no single-thread definition changes.

## SC pools

* `Pool Tid`: one core per running thread (`threads : Tid → Option State`, each with its own
  `fsBase`) and one shared `Memory`.
* `SCStep step p t p'`: thread `t` takes one step of **any** single-thread step function
  (`Open.step`, `Open9.step`, `Atomic9.step`, …) on its core and the shared memory.
* `SCStepF step Fin`: the same, for a thread whose core is not finished (`Fin t c`), and
  `SCReach` its reflexive-transitive closure. A finished thread is parked.

## Locations of a pool

* `Sep.Loc.isLocal`: registers, `rip` and the flags are per-thread; byte addresses and the
  mapping list `regions` are shared.
* `PLoc Tid`: a local location of a thread (`local t l`) or a shared one (`shared l`).
  `PFrag`, `PProp`, the pool separating conjunction `psep` (`∗ₚ`).
* `localFrag c`, `sharedFrag mem`: the two halves of `toFrag` (`toFrag_split`).
* `poolFrag p`: the total fragment of a pool. `embed t h` renames the local locations of a
  single-thread fragment to thread `t`; `atThread t P` and `atShared C` lift assertions.

## Frame-requantified safety

`LSafe step Fin Q r n c h`: the thread with core `c` owns the fragment `h` and may read the
read-only fragment `r`. For **every** memory consistent with `h ∪ r`, either the thread has
finished (`Fin c`) and `Q h` holds, or it takes a step that changes only locations of `h`,
and the successor is again safe. The memory is quantified **at every step**: what other
threads do outside `h ∪ r` between two steps cannot matter. `LTriple step Fin R P Q n` is
the triple form. `LTriple … emp P Q n → STripleS step n P Q` (`LTriple.toSTripleS`).
`Step1 step R I J` is one requantified step, from which `LTriple.of_chain` builds triples.

**Why not `STripleS`.** An earlier statement of `par_disjoint` used `STripleS`. That is
not sound for `Open.step`: an `STripleS` fixes the frame for the whole run, so a thread may
read a byte it does not own (made readable by owning `regions`), and rely on the byte not
changing between two reads. A second thread that owns the byte can change it in between.
`LSafe` closes that gap by quantifying the unowned memory at each step (the standard
definition of CSL safety: Vafeiadis, MFPS 2011, FROM MEMORY).

* `PoolSafe step Fin Q n p`: for every schedule of `n` steps of unfinished threads, no
  unfinished thread is stuck, and when all threads have finished `Q` holds.

## TSO pools (from access lists and store buffers)

* `EvMachine`: a single-thread machine given as fetch, executor and access list, with the
  locality proof. Instances `openEv`, `open9Ev`, `atomic9Ev`; `EvMachine.step`.
* `TPool Tid`: threads, shared memory, and per-thread FIFO store buffers of `(addr, bytes)`
  entries, oldest first (the buffers of `Tso.XState`).
* `overlay mem buf`: the thread's view, its own buffer installed over memory.
* `TsoStep M Fin p t p'`: thread `t` fetches and executes on its view. If the access list has
  a `locked` event or an `mfence`, the buffer must be empty and the memory is updated in place
  (`XStep.rmw`/`fence`). Otherwise the memory is unchanged and the written spans of the
  access list (exact) are appended to the buffer (`XStep.store`).
* `TsoFlush`: the oldest entry of one buffer is installed into memory, whole span at once
  (`XFlush`). Entries only ever hold bytes an executor wrote, so they are write-permitted.
* `TsoReach`, `Drained`, `forget`, `TPool.ofPool`.

## Ownership safety and the DRF statement

* `OwnershipSafe step Fin p`: a CSL certificate without resource invariants: pairwise
  disjoint owned fragments `σ t`, a shared read-only fragment `r`, and each running thread
  `LSafe` for every step index.
* `InFootprint`, `FetchStable`, `LSafeEv`, `LTripleEv`, `OwnershipSafeEv`: the same for an
  `EvMachine`, with every fetched and read byte in `h ∪ r`, every written byte in `h` (from
  the access list), and the fetch determined by the fetched bytes. `LSafe` alone permits racy
  reads of unowned bytes, which TSO can observe.
* `Task.drfTso` (**proved**: `drfTso_holds` in `Pool/Thms.lean`): footprint-ownership-
  safe pools have, under the TSO pool built from access lists, only drained states that the
  SC pool reaches. `LSafeEv` includes `FetchStable`; without it the statement is false
  (`drfTso_noFetch_false`).

Theorems are in `Pool/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Sep

/-- A location of the per-thread part of a machine state: registers, `rip` and flags. Byte
addresses and the mapping list are shared by all threads of a process. -/
def Loc.isLocal : Loc → Bool
  | .reg _ | .rip | .flags => true
  | .mem _ | .regions => false

end Silmaril.X86.Sep

namespace Silmaril.X86.Pool

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.X86.MemEvent (ChangesWithin)

/-! ## SC pools -/

set_option linter.dupNamespace false in
/-- A thread pool: a core per running thread, and one shared memory. -/
structure Pool (Tid : Type) where
  threads : Tid → Option State
  memory : Memory

variable {Tid : Type}

section SC
variable [DecidableEq Tid]

/-- **SC interleaving over any single-thread step**: thread `t` steps on its core and the
shared memory, and the result is written back. -/
inductive SCStep (step : MState → Option MState) : Pool Tid → Tid → Pool Tid → Prop
  | go {p : Pool Tid} {t : Tid} {c : State} {m' : MState} (ht : p.threads t = some c)
      (hs : step ⟨c, p.memory⟩ = some m') :
      SCStep step p t ⟨Function.update p.threads t (some m'.core), m'.memory⟩

/-- A step of an unfinished thread. -/
def SCStepF (step : MState → Option MState) (Fin : Tid → State → Prop) (p : Pool Tid) (t : Tid)
    (p' : Pool Tid) : Prop :=
  (∃ c, p.threads t = some c ∧ ¬ Fin t c) ∧ SCStep step p t p'

/-- SC reachability: finitely many steps of unfinished threads. -/
def SCReach (step : MState → Option MState) (Fin : Tid → State → Prop) :
    Pool Tid → Pool Tid → Prop :=
  Relation.ReflTransGen fun p p' => ∃ t, SCStepF step Fin p t p'

end SC

/-! ## Locations and fragments of a pool -/

/-- A location of a pool: a local location of one thread, or a shared one. `local t l` with
a shared `l`, and `shared l` with a local `l`, are junk and never hold a value. -/
inductive PLoc (Tid : Type) where
  | local (t : Tid) (l : Loc)
  | shared (l : Loc)

/-- A partial pool state. -/
abbrev PFrag (Tid : Type) := PLoc Tid → Option Val

/-- Pool assertions. -/
abbrev PProp (Tid : Type) := PFrag Tid → Prop

namespace PFrag

/-- The empty pool fragment. -/
def empty : PFrag Tid := fun _ => none

/-- Disjoint domains. -/
def Disjoint (a b : PFrag Tid) : Prop := ∀ l, a l = none ∨ b l = none

/-- Left-biased union. -/
def union (a b : PFrag Tid) : PFrag Tid := fun l =>
  match a l with
  | some v => some v
  | none => b l

/-- Containment. -/
def Le (a s : PFrag Tid) : Prop := ∀ l v, a l = some v → s l = some v

end PFrag

/-- Pool separating conjunction. -/
def psep (P Q : PProp Tid) : PProp Tid := fun H =>
  ∃ H₁ H₂, PFrag.Disjoint H₁ H₂ ∧ H = PFrag.union H₁ H₂ ∧ P H₁ ∧ Q H₂

/-- The empty pool assertion. -/
def pemp : PProp Tid := fun H => H = PFrag.empty

@[inherit_doc] scoped infixr:35 " ∗ₚ " => psep

/-- The per-thread half of `toFrag`: registers, `rip`, flags. -/
def localFrag (c : State) : Frag
  | .reg r => some (.word (c.read r))
  | .rip => some (.word c.rip)
  | .flags => some (.flags c.flags)
  | .mem _ => none
  | .regions => none

/-- The shared half of `toFrag`: byte cells and the mapping list. -/
def sharedFrag (mem : Memory) : Frag
  | .reg _ => none
  | .rip => none
  | .flags => none
  | .mem a => some (.cell ⟨mem.bytes.get? a, permsAt mem a⟩)
  | .regions => some (.regions mem.regions)

/-- A fragment owns no per-thread location. -/
def SharedOnly (h : Frag) : Prop := ∀ l, l.isLocal = true → h l = none

section Embed
variable [DecidableEq Tid]

/-- Rename the local locations of a single-thread fragment to thread `t`. -/
def embed (t : Tid) (h : Frag) : PFrag Tid
  | .local t' l => if t' = t ∧ l.isLocal = true then h l else none
  | .shared l => if l.isLocal = true then none else h l

/-- A fragment of shared locations, as a pool fragment. -/
def embedS (h : Frag) : PFrag Tid
  | .local _ _ => none
  | .shared l => if l.isLocal = true then none else h l

/-- Thread `t`'s view of a pool fragment. -/
def proj (t : Tid) (H : PFrag Tid) : Frag := fun l =>
  if l.isLocal = true then H (.local t l) else H (.shared l)

/-- The total fragment of a pool. -/
def poolFrag (p : Pool Tid) : PFrag Tid
  | .local t l => (p.threads t).bind fun c => localFrag c l
  | .shared l => sharedFrag p.memory l

/-- `P` holds of thread `t`'s part. -/
def atThread (t : Tid) (P : SProp) : PProp Tid := fun H => ∃ h, P h ∧ H = embed t h

/-- `C` holds of a part with shared locations only. -/
def atShared (C : SProp) : PProp Tid := fun H => ∃ h, C h ∧ SharedOnly h ∧ H = embedS h

end Embed

/-! ## Frame-requantified safety of one thread -/

/-- **Frame-requantified stable safety.** The thread with core `c` owns `h` and reads the
read-only `r`. For every memory consistent with `h ∪ r`: either the thread has finished and
`Q h` holds, or it steps, changing only locations of `h`, to a state that is again safe. -/
def LSafe (step : MState → Option MState) (Fin : State → Prop) (Q : SProp) (r : Frag) :
    Nat → State → Frag → Prop
  | 0, _, _ => True
  | n + 1, c, h => ∀ mem : Memory, Le (union h r) (toFrag ⟨c, mem⟩) →
      (Fin c ∧ Q h) ∨
      (¬ Fin c ∧ ∃ m', step ⟨c, mem⟩ = some m' ∧ ChangesWithin h ⟨c, mem⟩ m' ∧
        LSafe step Fin Q r n m'.core (reval h (toFrag m')))

/-- **Frame-requantified stable triple** with a read-only context `R`: from every owned
`P`-fragment, next to every disjoint `R`-fragment, the thread is `LSafe` for `n` steps. -/
def LTriple (step : MState → Option MState) (Fin : State → Prop) (R P Q : SProp) (n : Nat) :
    Prop :=
  ∀ (c : State) (h r : Frag), R r → P h → Disjoint h r → LSafe step Fin Q r n c h

/-- **One requantified step**: from every state consistent with an `I`-fragment next to a
disjoint `R`-fragment, the step succeeds, changes only the `I`-fragment, and re-values it into
a `J`-fragment. -/
def Step1 (step : MState → Option MState) (R I J : SProp) : Prop :=
  ∀ (c : State) (mem : Memory) (h r : Frag), R r → I h → Disjoint h r →
    Le (union h r) (toFrag ⟨c, mem⟩) →
    ∃ m', step ⟨c, mem⟩ = some m' ∧ ChangesWithin h ⟨c, mem⟩ m' ∧ J (reval h (toFrag m'))

section PoolSafe
variable [DecidableEq Tid]

/-- **Pool safety under every schedule** (partial correctness): within `n` steps of
unfinished threads, no unfinished thread is stuck, and once every thread has finished, `Q`
holds. -/
def PoolSafe (step : MState → Option MState) (Fin : Tid → State → Prop)
    (Q : Pool Tid → Prop) : Nat → Pool Tid → Prop
  | 0, _ => True
  | n + 1, p =>
    ((∀ t c, p.threads t = some c → Fin t c) ∧ Q p) ∨
    ((∃ t c, p.threads t = some c ∧ ¬ Fin t c) ∧
      (∀ t c, p.threads t = some c → ¬ Fin t c → ∃ p', SCStep step p t p') ∧
      ∀ t p', SCStepF step Fin p t p' → PoolSafe step Fin Q n p')

/-- **Ownership safety** (CSL without resource invariants): every running thread owns a
fragment `σ t`, the owned fragments are pairwise disjoint and disjoint from a shared
read-only fragment `r`, all are part of the pool, and each running thread is `LSafe` on its
fragment for every step index. -/
def OwnershipSafe (step : MState → Option MState) (Fin : Tid → State → Prop) (p : Pool Tid) :
    Prop :=
  ∃ (σ : Tid → Frag) (r : Frag) (Q : Tid → SProp),
    SharedOnly r ∧
    (∀ t, p.threads t = none → σ t = Frag.empty) ∧
    (∀ t t', t ≠ t' → PFrag.Disjoint (embed t (σ t)) (embed t' (σ t'))) ∧
    (∀ t, PFrag.Disjoint (embed t (σ t)) (embedS r)) ∧
    (∀ t, PFrag.Le (embed t (σ t)) (poolFrag p)) ∧
    PFrag.Le (embedS r) (poolFrag p) ∧
    ∀ t c, p.threads t = some c → ∀ n, LSafe step (Fin t) (Q t) r n c (σ t)

end PoolSafe

/-! ## Single-thread machines with access lists -/

/-- A single-thread machine given as fetch, executor and access list, with the locality
of the executor for the access list. -/
structure EvMachine where
  Instr : Type
  fetch : Memory → Nat → Option (Instr × Nat)
  exec : Instr → State → Memory → Nat → Silmaril.X86.Ext.Result
  accesses : Instr → State → Nat → List MemEvent.Event
  isLocal : ∀ i s n,
    MemEvent.Local MemEvent.extView (fun mem => exec i s mem n) (accesses i s n)

/-- The step of an `EvMachine`: fetch at `rip`, then execute on the one memory. -/
def EvMachine.step (M : EvMachine) (m : MState) : Option MState :=
  (M.fetch m.memory m.core.rip.toNat).bind fun p =>
    Silmaril.X86.Open.ofResult (M.exec p.1 m.core m.memory p.2)

/-- The open machine (`Open.step`), with `Ext8` access lists. -/
def openEv : EvMachine where
  Instr := Silmaril.X86.Ext8.Instr
  fetch := MemEvent.openFetch
  exec := Silmaril.X86.Ext8.exec
  accesses := MemEvent.ext8Accesses
  isLocal := MemEvent.ext8_local

/-- `Open9.step`, with `Ext9` access lists. -/
def open9Ev : EvMachine where
  Instr := Silmaril.X86.Ext9.Instr
  fetch := MemEvent.open9Fetch
  exec := Silmaril.X86.Ext9.exec
  accesses := MemEvent.ext9Accesses
  isLocal := MemEvent.ext9_local

/-- `Atomic9.step`, with the tagged atomic access lists. -/
def atomic9Ev : EvMachine where
  Instr := Silmaril.X86.Atomic9.Instr
  fetch := MemEvent.atomic9Fetch
  exec := Silmaril.X86.Atomic9.exec
  accesses := MemEvent.atomic9Accesses
  isLocal := MemEvent.atomic9_local

/-! ## Footprint-safe threads (the hypothesis of the DRF statement) -/

/-- **The footprint of one instruction lies in `h ∪ r`.** The `k` fetched bytes at `pc` and
every byte the access list reads are cells of the owned fragment `h` or the read-only `r`;
every byte it writes (including a write of the value already there) is a cell of `h`. -/
def InFootprint (h r : Frag) (pc k : Nat) (es : List MemEvent.Event) : Prop :=
  (∀ j < k, (union h r (.mem (pc + j))).isSome) ∧
  (∀ a, MemEvent.readSet es a → (union h r (.mem a)).isSome) ∧
  (∀ a, MemEvent.writeSet es a → (h (.mem a)).isSome)

/-- **The fetch is determined by the fetched bytes**: on every memory with the same mapping
list and the same `k` bytes from `pc`, the machine fetches the same instruction and length.
`InFootprint` puts the `k` fetched bytes in `h ∪ r`, but an `EvMachine`'s `fetch` is an
arbitrary function of the memory: without this condition a fetch could depend on a byte
another thread writes (a data race the access list does not show), and `Task.drfTso` is false
(`Pool/Thms.lean`, `drfTso_noFetch_false`). For `openEv` it holds of every `Ext` form
(`openFetch_stable`); the real decoders read a fifteen-byte window, and whether their `Ext8`
and later forms depend only on their own bytes is not proved. -/
def FetchStable (M : EvMachine) (mem : Memory) (pc : Nat) (i : M.Instr) (k : Nat) : Prop :=
  ∀ mem' : Memory, MemEvent.Agree (fun a => pc ≤ a ∧ a < pc + k) mem mem' →
    M.fetch mem' pc = some (i, k)

/-- **Footprint-safe**: `LSafe` for the step of an `EvMachine`, where in addition every
instruction fetches and reads only cells of `h ∪ r` and writes only cells of `h`
(`InFootprint`), and its fetch depends only on the fetched bytes (`FetchStable`). `LSafe`
alone allows a step to read a byte it does not own as long as every value is acceptable,
which is a data race: under TSO such a read can see a value that no SC interleaving produces
(store buffering). `LSafeEv.toLSafe` drops the extra conjuncts. -/
def LSafeEv (M : EvMachine) (Fin : State → Prop) (Q : SProp) (r : Frag) :
    Nat → State → Frag → Prop
  | 0, _, _ => True
  | n + 1, c, h => ∀ mem : Memory, Le (union h r) (toFrag ⟨c, mem⟩) →
      (Fin c ∧ Q h) ∨
      (¬ Fin c ∧ ∃ i k m', M.fetch mem c.rip.toNat = some (i, k) ∧
        FetchStable M mem c.rip.toNat i k ∧
        InFootprint h r c.rip.toNat k (M.accesses i c k) ∧
        M.step ⟨c, mem⟩ = some m' ∧ ChangesWithin h ⟨c, mem⟩ m' ∧
        LSafeEv M Fin Q r n m'.core (reval h (toFrag m')))

/-- The triple form of `LSafeEv`, as `LTriple` is of `LSafe`. -/
def LTripleEv (M : EvMachine) (Fin : State → Prop) (R P Q : SProp) (n : Nat) : Prop :=
  ∀ (c : State) (h r : Frag), R r → P h → Disjoint h r → LSafeEv M Fin Q r n c h

section OwnEv
variable [DecidableEq Tid]

/-- **Footprint ownership safety**: `OwnershipSafe` with every running thread `LSafeEv`, so
that no thread reads a byte another thread may write (data-race freedom by ownership).
`OwnershipSafeEv.toOwnershipSafe` forgets the footprints. -/
def OwnershipSafeEv (M : EvMachine) (Fin : Tid → State → Prop) (p : Pool Tid) : Prop :=
  ∃ (σ : Tid → Frag) (r : Frag) (Q : Tid → SProp),
    SharedOnly r ∧
    (∀ t, p.threads t = none → σ t = Frag.empty) ∧
    (∀ t t', t ≠ t' → PFrag.Disjoint (embed t (σ t)) (embed t' (σ t'))) ∧
    (∀ t, PFrag.Disjoint (embed t (σ t)) (embedS r)) ∧
    (∀ t, PFrag.Le (embed t (σ t)) (poolFrag p)) ∧
    PFrag.Le (embedS r) (poolFrag p) ∧
    ∀ t c, p.threads t = some c → ∀ n, LSafeEv M (Fin t) (Q t) r n c (σ t)

end OwnEv

/-! ## TSO pools -/

/-- A store-buffer entry: first address and bytes (`XState.buffer` entries). -/
abbrev Entry := Nat × List Byte

/-- A TSO pool: threads, shared memory, and per-thread FIFO store buffers, oldest first. -/
structure TPool (Tid : Type) where
  threads : Tid → Option State
  memory : Memory
  buffer : Tid → List Entry

/-- A thread's view of memory: its own buffer installed over memory, oldest entry first, so
the newest entry covering a byte wins (store forwarding, `viewMem`). -/
def overlay (mem : Memory) (buf : List Entry) : Memory :=
  { mem with bytes := buf.foldl (fun b e => Memory.install b e.1 e.2) mem.bytes }

/-- `n` bytes from `a` (absent bytes read as `0`; only used on written, hence backed, spans). -/
def readSpan (mem : Memory) (a n : Nat) : List Byte :=
  (List.range n).map fun i => (mem.bytes.get? (a + i)).getD 0

/-- The access list has a `locked` event or an `mfence`: it needs an empty store buffer. -/
def syncs (es : List MemEvent.Event) : Bool :=
  es.any fun e => e.locked || decide (e.kind = .fence .mfence)

/-- The buffer entries of an unlocked instruction: each written span of its access list, in
order, with the bytes the executor left there. -/
def storeEntries (es : List MemEvent.Event) (after : Memory) : List Entry :=
  (es.filter fun e => e.kind.writes).map fun e => (e.addr, readSpan after e.addr e.size)

section Tso
variable [DecidableEq Tid]

/-- **One TSO instruction step** of thread `t`, built from the access lists and the
buffers. The instruction is fetched from and executed on the thread's view. A synchronising
instruction (a `locked` event or `mfence`) needs an empty buffer and writes memory directly;
any other instruction leaves memory unchanged and enqueues its written spans. -/
inductive TsoStep (M : EvMachine) (Fin : Tid → State → Prop) :
    TPool Tid → Tid → TPool Tid → Prop
  | sync {p : TPool Tid} {t : Tid} {c c' : State} {i : M.Instr} {n : Nat} {mem' : Memory}
      (ht : p.threads t = some c) (hnf : ¬ Fin t c)
      (hf : M.fetch (overlay p.memory (p.buffer t)) c.rip.toNat = some (i, n))
      (hs : syncs (M.accesses i c n) = true) (he : p.buffer t = [])
      (hx : M.exec i c p.memory n = .ok c' mem') :
      TsoStep M Fin p t { p with threads := Function.update p.threads t (some c'), memory := mem' }
  | buffered {p : TPool Tid} {t : Tid} {c c' : State} {i : M.Instr} {n : Nat} {view' : Memory}
      (ht : p.threads t = some c) (hnf : ¬ Fin t c)
      (hf : M.fetch (overlay p.memory (p.buffer t)) c.rip.toNat = some (i, n))
      (hs : syncs (M.accesses i c n) = false)
      (hx : M.exec i c (overlay p.memory (p.buffer t)) n = .ok c' view') :
      TsoStep M Fin p t { p with
        threads := Function.update p.threads t (some c'),
        buffer := Function.update p.buffer t
          (p.buffer t ++ storeEntries (M.accesses i c n) view') }

/-- **Flush**: the oldest entry of one buffer reaches memory, whole span at once. -/
inductive TsoFlush : TPool Tid → TPool Tid → Prop
  | head {p : TPool Tid} {t : Tid} {a : Nat} {bs : List Byte} {rest : List Entry}
      (hb : p.buffer t = (a, bs) :: rest) :
      TsoFlush p { p with
        memory := { p.memory with bytes := Memory.install p.memory.bytes a bs },
        buffer := Function.update p.buffer t rest }

/-- TSO reachability: instruction steps and flushes. -/
def TsoReach (M : EvMachine) (Fin : Tid → State → Prop) : TPool Tid → TPool Tid → Prop :=
  Relation.ReflTransGen fun p p' => (∃ t, TsoStep M Fin p t p') ∨ TsoFlush p p'

end Tso

/-- All buffers are empty. -/
def Drained (p : TPool Tid) : Prop := ∀ t, p.buffer t = []

/-- Forget the (drained) buffers. -/
def forget (p : TPool Tid) : Pool Tid := ⟨p.threads, p.memory⟩

/-- An SC pool as a TSO pool with empty buffers. -/
def TPool.ofPool (p : Pool Tid) : TPool Tid := ⟨p.threads, p.memory, fun _ => []⟩

/-- The projection of a TSO pool to the byte-granular `Tso.XState` (memory as a partial
byte map; the buffers as they are). -/
def TPool.toX (p : TPool Tid) : Silmaril.X86.MemoryModel.Tso.XState Tid :=
  ⟨fun a => p.memory.bytes.get? a, p.buffer⟩

/-! ## The DRF statement -/

/-- **DRF route**, proved as `drfTso_holds`. A footprint-ownership-safe
SC pool (every running
thread owns a fragment, the fragments are disjoint, a common read-only fragment is shared, and
every thread is frame-requantified safe on its own fragment and fetches, reads and writes only
within its fragment and the read-only one) has, under the byte-granular TSO pool built from
the access lists and the buffers, only drained states that the SC pool reaches.

The hypothesis is `OwnershipSafeEv`, not `OwnershipSafe`. With `OwnershipSafe` the statement
is false (argued, not proved in Lean): two threads owning `x` and `y` respectively, with the
mapping list read-only shared, running `mov [x], 1; mov rax, [y]` and `mov [y], 1;
mov rbx, [x]` from `x = y = 0`, are `LSafe` with postconditions that accept any `rax`/`rbx`
(an unowned read is allowed when every value is acceptable). TSO buffers both stores and
reaches the drained state `rax = rbx = 0`, which no SC interleaving reaches.

`LSafeEv` also asks that each fetch be `FetchStable` (determined by its
own bytes and the mapping list). The version without that conjunct is false
(`drfTso_noFetch_false`): an `EvMachine` whose fetch reads a byte another thread writes satisfies
the hypothesis of that version and shows store buffering through the fetch. For `openEv`, every
`Ext` fetch is
stable (`openFetch_stable`), so the `ret` and `right_rot` pools meet the new hypothesis.

Note: `OwnershipSafe` has no lock invariants (CSL resources).
Lock-protected sharing is the next extension; this statement covers disjoint and read-only
sharing, which is what `par_disjoint`/`par_shared_ro` produce. -/
def Task.drfTso : Prop :=
  ∀ {Tid : Type} [DecidableEq Tid] (M : EvMachine) (Fin : Tid → State → Prop) (p₀ : Pool Tid),
    OwnershipSafeEv M Fin p₀ →
    ∀ p, TsoReach M Fin (TPool.ofPool p₀) p → Drained p → SCReach M.step Fin p₀ (forget p)

end Silmaril.X86.Pool
