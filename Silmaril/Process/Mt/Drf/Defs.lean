module

/-!
# The memory-model bridge for multi-threaded processes: SC with atomic primitives vs. store buffers

This module states the **DRF-modulo-primitives** bridge for multi-threaded x86 processes. A
multi-threaded process is decomposed into per-thread code on single-threaded machines, with
synchronisation (locked instructions, `mfence`, system calls, calls of trusted primitives) as
atomic steps. That decomposition is sound for the SC interleaving semantics. The bridge shows
it is also sound for x86-TSO and for XL, the loose x86 model, for programs that are race free
modulo synchronisation.

The setting is generic: any thread semantics whose steps report their memory accesses can be
plugged in. An x86 thread running on a single-threaded machine is one instance: its instruction
steps report `MemEvent` byte reads and writes, and its primitive calls and system calls are
synchronising steps.

## Memory, labels and systems

* **Memory** is total, `Mem := Nat → Nat`: an address of a byte cell to its value. Cells may be
  bytes or words; nothing below depends on their size.
* A **thread-local step** reports a label `Lab`:
  * `plain rs ws weak`: the plain (unlocked, `mov`-class) accesses of one instruction. It reads
    the cells `rs` with the values given there, then writes `ws` in order. `weak` marks `nt` and
    `str` stores (XL's weak stores). A step with no memory access is `plain [] [] false`.
  * `sfence`.
* A **synchronising step** of thread `t` (`Sys.sync t ts rs ws ts'`) needs `t`'s store buffer to
  be empty and acts atomically on memory. It reads `rs` and writes `ws`, and it may change the
  state of every thread (`ts` to `ts'`). Locked read-modify-writes, `xchg`, `mfence`, system
  calls (`futex`, `clone`, `exit`) and **calls of trusted primitives** (a mutex, a recursive
  stream lock, an atomic, a lock-free list, each run as one atomic step that meets its abstract
  specification) are synchronising steps.
* A system `Sys` runs threads `0 … N-1` that share memory. Thread slots that do not exist yet
  are states with no steps, which a synchronising step (`clone`) may replace.

## The machines

* `ScStep S N`: the **SC semantics with atomic primitives**. Steps interleave on one memory.
* `BStep M S N` for `M = .tso` or `.xl`: one **store buffer per thread** (`Ent`). Plain writes
  and `sfence` barriers enter the buffer. Plain reads see the thread's newest buffered value,
  else memory. A synchronising step needs an empty buffer. Flushes:
  * TSO: only the oldest entry (FIFO);
  * XL: any entry that does not pass an earlier barrier, an earlier store to the same cell, or
    an earlier store when both are write-back. So a weak (`nt`/`str`) store may overtake other
    stores and be overtaken by them, `sfence` orders stores, and synchronising steps order
    everything.

## Race freedom modulo primitives: ownership certificates

An ownership assignment `o : Own` says which thread owns which cell (`o t a`). A
**certificate** `Cert S N R` is an invariant `R` of SC configurations paired with ownership
assignments that is preserved by SC steps and under which:

* owned cells are owned by at most one thread;
* a plain read touches only cells the thread owns or that nobody owns;
* a plain write touches only cells the thread owns;
* a synchronising step of `t` touches no cell another thread owns;
* thread-local steps never take a cell away from a thread, and a synchronising step of `t`
  takes cells away from no other thread. Ownership moves only at synchronising steps of the
  thread that gives it up, which is the point where that thread's buffer is empty.

This is race freedom modulo synchronisation: two accesses of different threads to one cell
either are both reads, or one of them is a synchronising step, or the cell's ownership moved
between them through synchronising steps. A CSL derivation (a global invariant of disjoint
owned footprints and resource invariants) is a certificate, with `o t` the cells thread `t`
owns. So is the decomposition's thread-modular invariant: each thread proved alone on its
single-threaded machine, with lock invariants transferred at primitive calls.

## Primitives

The trusted primitives enter this module only as synchronising steps. Showing that a
primitive's *implementation* (for example glibc's `lll_lock`, or the recursive `_IO_lock_t`)
refines its atomic step under TSO or XL is a separate obligation, `PrimCorrect` in
`Silmaril.Process.Mt.Drf.Prim.Defs`.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Drf

/-! ## Memory -/

/-- Memory: a cell address to its value. -/
abbrev Mem := Nat → Nat

/-- Write one cell. -/
def Mem.set (m : Mem) (a v : Nat) : Mem := fun x => if x = a then v else m x

/-- Apply writes in order (a later write to a cell wins). -/
def Mem.write (m : Mem) : List (Nat × Nat) → Mem
  | [] => m
  | p :: ws => (m.set p.1 p.2).write ws

/-- Every read agrees with memory. -/
def Mem.Reads (m : Mem) (rs : List (Nat × Nat)) : Prop := ∀ p ∈ rs, m p.1 = p.2

/-! ## Labels and systems -/

/-- The label of a thread-local step: one instruction's plain accesses, or `sfence`. -/
inductive Lab where
  /-- Plain reads `rs` (cell and value read), then plain writes `ws` in order; `weak` marks
  `nt`/`str` stores. -/
  | plain (rs ws : List (Nat × Nat)) (weak : Bool)
  | sfence

/-- **A thread system.** `loc t s l s'`: thread `t` in state `s` takes a thread-local step
with label `l`. `sync t ts rs ws ts'`: thread `t` takes a synchronising step on the thread
states `ts`, reading `rs` and writing `ws` atomically, to the thread states `ts'`. -/
structure Sys where
  St : Type
  loc : Nat → St → Lab → St → Prop
  sync : Nat → (Nat → St) → List (Nat × Nat) → List (Nat × Nat) → (Nat → St) → Prop

/-- Update one thread. -/
def upd {α : Type} (f : Nat → α) (t : Nat) (x : α) : Nat → α :=
  fun u => if u = t then x else f u

/-- Reflexive-transitive closure. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl {a} : Star r a a
  | step {a b c} (h : r a b) (h' : Star r b c) : Star r a c

/-! ## SC with atomic primitives -/

/-- A configuration: thread states and memory. -/
structure Cfg (S : Sys) where
  ts : Nat → S.St
  mem : Mem

/-- **SC interleaving with atomic synchronisation** of threads `0 … N-1`. -/
inductive ScStep (S : Sys) (N : Nat) : Cfg S → Cfg S → Prop
  | plain {C : Cfg S} {t rs ws w s'} (ht : t < N) (hs : S.loc t (C.ts t) (.plain rs ws w) s')
      (hr : C.mem.Reads rs) : ScStep S N C ⟨upd C.ts t s', C.mem.write ws⟩
  | sfence {C : Cfg S} {t s'} (ht : t < N) (hs : S.loc t (C.ts t) .sfence s') :
      ScStep S N C ⟨upd C.ts t s', C.mem⟩
  | sync {C : Cfg S} {t rs ws ts'} (ht : t < N) (hs : S.sync t C.ts rs ws ts')
      (hr : C.mem.Reads rs) : ScStep S N C ⟨ts', C.mem.write ws⟩

/-- SC reachability. -/
abbrev ScReach (S : Sys) (N : Nat) : Cfg S → Cfg S → Prop := Star (ScStep S N)

/-! ## Store buffers: TSO and XL -/

/-- A buffer entry: a store of `v` to cell `a` (weak if `nt`/`str`), or an `sfence` barrier. -/
inductive Ent where
  | st (a v : Nat) (weak : Bool)
  | bar
  deriving DecidableEq, Repr

/-- The value an entry stores in cell `x`. -/
def Ent.val : Ent → Nat → Option Nat
  | .st a v _, x => if a = x then some v else none
  | .bar, _ => none

/-- The newest buffered value of cell `a` (buffers are oldest first). -/
def newest : List Ent → Nat → Option Nat
  | [], _ => none
  | e :: b, a => (newest b a).or (e.val a)

/-- A thread's view of memory: its newest buffered value, else memory. -/
def view (m : Mem) (b : List Ent) : Mem := fun a => (newest b a).getD (m a)

/-- The buffer entries of a plain write list. -/
def ents (ws : List (Nat × Nat)) (weak : Bool) : List Ent := ws.map fun p => .st p.1 p.2 weak

/-- XL's flush order: entry `e` may leave the buffer before the earlier entries `pre`. A
barrier must be oldest; a store may not pass a barrier, an earlier store to the same cell, or an
earlier store when both are write-back. -/
def Ent.passes : Ent → List Ent → Prop
  | .bar, pre => pre = []
  | .st a _ w, pre => ∀ e ∈ pre, match e with
    | .bar => False
    | .st a' _ w' => a' ≠ a ∧ (w = true ∨ w' = true)

/-- Flush an entry into memory. -/
def Ent.apply (m : Mem) : Ent → Mem
  | .st a v _ => m.set a v
  | .bar => m

/-- The buffered models: x86-TSO and XL (the loose x86 model). -/
inductive Model where
  | tso
  | xl
  deriving DecidableEq, Repr

/-- A buffered configuration. -/
structure BCfg (S : Sys) where
  ts : Nat → S.St
  mem : Mem
  buf : Nat → List Ent

/-- **Store-buffer steps** of threads `0 … N-1` under TSO or XL. -/
inductive BStep (M : Model) (S : Sys) (N : Nat) : BCfg S → BCfg S → Prop
  /-- Plain accesses: reads see the thread's view, writes are buffered. -/
  | plain {C : BCfg S} {t rs ws w s'} (ht : t < N) (hs : S.loc t (C.ts t) (.plain rs ws w) s')
      (hr : (view C.mem (C.buf t)).Reads rs) :
      BStep M S N C ⟨upd C.ts t s', C.mem, upd C.buf t (C.buf t ++ ents ws w)⟩
  /-- `sfence` buffers a barrier. -/
  | sfence {C : BCfg S} {t s'} (ht : t < N) (hs : S.loc t (C.ts t) .sfence s') :
      BStep M S N C ⟨upd C.ts t s', C.mem, upd C.buf t (C.buf t ++ [.bar])⟩
  /-- A synchronising step: needs an empty buffer, acts on memory. -/
  | sync {C : BCfg S} {t rs ws ts'} (ht : t < N) (hs : S.sync t C.ts rs ws ts')
      (he : C.buf t = []) (hr : C.mem.Reads rs) :
      BStep M S N C ⟨ts', C.mem.write ws, C.buf⟩
  /-- A flush: under TSO only the oldest entry, under XL any entry its order allows. -/
  | flush {C : BCfg S} {t pre e post} (hb : C.buf t = pre ++ e :: post) (hp : e.passes pre)
      (hm : M = .xl ∨ pre = []) :
      BStep M S N C ⟨C.ts, e.apply C.mem, upd C.buf t (pre ++ post)⟩

/-- Buffered reachability. -/
abbrev BReach (M : Model) (S : Sys) (N : Nat) : BCfg S → BCfg S → Prop := Star (BStep M S N)

/-- An SC configuration with empty buffers. -/
def Cfg.toB {S : Sys} (C : Cfg S) : BCfg S := ⟨C.ts, C.mem, fun _ => []⟩

/-- All buffers are empty. -/
def BCfg.Drained {S : Sys} (C : BCfg S) : Prop := ∀ t, C.buf t = []

/-- The first buffered value of cell `a` among the threads `us`. -/
def bufVal (buf : Nat → List Ent) (a : Nat) : List Nat → Option Nat
  | [] => none
  | u :: us => (newest (buf u) a).or (bufVal buf a us)

/-- **The abstraction of a buffered configuration**: every buffered value installed. Under a
certificate at most one thread buffers a cell, so the order of threads does not matter. -/
def BCfg.abs {S : Sys} (N : Nat) (C : BCfg S) : Cfg S :=
  ⟨C.ts, fun a => (bufVal C.buf a (List.range N)).getD (C.mem a)⟩

/-! ## Ownership certificates -/

/-- Ownership: `o t a` says thread `t` owns cell `a`. -/
abbrev Own := Nat → Nat → Prop

/-- **An ownership certificate** (race freedom modulo synchronisation): an invariant `R` of SC
configurations and ownership assignments, preserved by SC steps, under which owned cells are
owned by one thread, plain reads touch owned or unowned cells, plain writes touch owned cells,
synchronising steps touch no cell another thread owns, and ownership is taken from a thread
only at its own synchronising steps. -/
structure Cert (S : Sys) (N : Nat) (R : Cfg S → Own → Prop) : Prop where
  disj : ∀ C o, R C o → ∀ t u a, t ≠ u → o t a → o u a → False
  rd : ∀ C o, R C o → ∀ t < N, ∀ rs ws w s', S.loc t (C.ts t) (.plain rs ws w) s' →
    ∀ p ∈ rs, o t p.1 ∨ ∀ u, ¬ o u p.1
  wr : ∀ C o, R C o → ∀ t < N, ∀ rs ws w s', S.loc t (C.ts t) (.plain rs ws w) s' →
    ∀ p ∈ ws, o t p.1
  syncFp : ∀ C o, R C o → ∀ t < N, ∀ rs ws ts', S.sync t C.ts rs ws ts' →
    ∀ p ∈ rs ++ ws, ∀ u, u ≠ t → ¬ o u p.1
  plain : ∀ C o, R C o → ∀ t < N, ∀ rs ws w s', S.loc t (C.ts t) (.plain rs ws w) s' →
    C.mem.Reads rs → ∃ o', R ⟨upd C.ts t s', C.mem.write ws⟩ o' ∧ ∀ u a, o u a → o' u a
  sfence : ∀ C o, R C o → ∀ t < N, ∀ s', S.loc t (C.ts t) .sfence s' →
    ∃ o', R ⟨upd C.ts t s', C.mem⟩ o' ∧ ∀ u a, o u a → o' u a
  sync : ∀ C o, R C o → ∀ t < N, ∀ rs ws ts', S.sync t C.ts rs ws ts' → C.mem.Reads rs →
    ∃ o', R ⟨ts', C.mem.write ws⟩ o' ∧ ∀ u a, u ≠ t → o u a → o' u a

/-- Every buffered cell is owned by its (running) thread. -/
def BufOwned {S : Sys} (N : Nat) (C : BCfg S) (o : Own) : Prop :=
  ∀ t a, (newest (C.buf t) a).isSome → t < N ∧ o t a

end Silmaril.Process.Mt.Drf
