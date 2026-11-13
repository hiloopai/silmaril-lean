module

public import Silmaril.X86.Concurrency.Cir.Defs
public import Silmaril.X86.Sep.BI.Defs

/-!
# CSL over CIR: a CIR-native machine, store-buffer XL, and ownership safety

This module reasons about concurrency on a **small, CIR-native** semantics, not on the
byte-level candidate executions of `Silmaril.X86.MemoryModel`, and connects the two by one
bridge statement, `Task.cirXlOpAx`, proved as `Csl.cirXlOpAx_holds` (`Cir/Csl/Thms.lean`).

## The CIR-native semantics

* **Cells.** Memory is a cell heap `Heap := Nat → Option Nat`: an address of a (uniform)
  location to its value. Every access touches whole cells, as in uniform programs
  (`Prog.uniformB`), so there is no tearing, no byte splitting and no `Exec.Wf`.
* **Threads** take small steps `TStep s rs l s' rs'`. A step is silent (`l = none`) or emits
  one CIR label (`Cir.Lab`). A read may return any value (that fits): the memory machines
  decide which values are right. So threads and memory are separate, and the thread layer is
  reused by every machine below.
* **Labels to memory.** `Lab.reads` (cells and values a label reads), `Lab.wval` (the value
  it leaves in a cell, if it writes it), `Lab.okH H` (its reads agree with `H`),
  `Lab.updH H` (its writes applied), `Lab.na` (a non-atomic access), `Lab.drains` (on x86
  it needs an empty store buffer: locked RMW, `mfence`, a futex call).
* **Machines over `N` threads.**
  * `ScStep N`: SC interleaving; a label step reads and writes the one memory.
  * `OStep m N` for `m = .tso` or `.xl`: per-thread store buffers. Plain stores and the writes
    of a `local` block are buffered; loads read their own newest buffered value, else memory
    (store forwarding); draining labels need an empty buffer. Flushes:
    * TSO: only the oldest entry (FIFO);
    * XL: any entry that does not pass an earlier entry to the same cell, an `sfence` barrier,
      or an earlier entry when both are write-back. So weak (`nt`/`str`) stores may overtake
      and be overtaken by other stores, as in `ppoXl` (but, unlike `ppoXl`, never
      overtake an earlier load: see `Task.cirXlOpAx`); `sfence` orders stores; locked
      instructions and `mfence` order everything.
  The bridge from the axiomatic XL model to `OStep .xl` is the statement `Task.cirXlOpAx`.

## Ownership safety (CSL)

Assertions are predicates on a heap (`HProp`), with the BI connectives of
`Silmaril.X86.Sep.BI` over the separation algebra of partial maps (so the BI laws hold
for them: `Sep.BI.laws`). One resource invariant `I : HProp` describes the shared state.

`Safe I Q s rs h` (`SafeF`, greatest fixed point by a post-fixed-point witness): the thread
owning `h` is safe, ending with `Q`. Every step it can take is allowed:

* a **non-atomic** label (`na` load/store, `local` block) touches only owned cells;
* an **atomic** label may also touch the invariant's heap: for every `hI ⊨ I` disjoint from
  `h`, it touches only `h ∪ hI` and re-splits the result into a new owned heap and a new
  `I`-heap (ownership may move in or out: **atomic invariant access**);
* a **non-draining** atomic label (a plain-`mov` load or store with a C11 mode, `lfence`,
  `sfence`) writes only owned cells and gives up no cell. This is what makes the proof
  transfer to store buffers: ownership leaves a thread only at a locked RMW, `mfence` or futex
  call, when its buffer is empty. `nt`/`str` stores are plain stores, so they are always to
  owned cells; their hand-off happens at a locked instruction, which orders them in XL.

`GInv I Q N C hs hI` (the global CSL invariant): disjoint owned heaps `hs t` and invariant heap
`hI ⊨ I`, all agreeing with memory, and each thread safe on its heap.

`XInv`: `GInv` of the abstraction of a buffered configuration (`OCfg.abs`: each thread's
buffered values installed), and every buffered cell is owned by its thread.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Csl

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Sep.BI (SepAlg)
open Silmaril.X86.Atomic9 (FenceKind)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-! ## Heaps -/

/-- A cell heap: cell address to value. -/
abbrev Heap := Nat → Option Nat

namespace Heap

/-- The empty heap. -/
def empty : Heap := fun _ => none

/-- Disjoint domains (the separation algebra's `Disjoint`). -/
abbrev Disjoint (h₁ h₂ : Heap) : Prop := SepAlg.pmapDisjoint h₁ h₂

/-- Left-biased union (the separation algebra's `union`). -/
abbrev union (h₁ h₂ : Heap) : Heap := SepAlg.pmapUnion h₁ h₂

/-- Containment. -/
def Le (h s : Heap) : Prop := ∀ a v, h a = some v → s a = some v

/-- One cell. -/
def single (a v : Nat) : Heap := fun x => if x = a then some v else none

end Heap

/-- Heap assertions. -/
abbrev HProp := Heap → Prop

/-- Separating conjunction: `Sep.BI.sep` over partial maps. -/
abbrev hsep (P Q : HProp) : HProp := Silmaril.X86.Sep.BI.sep P Q

@[inherit_doc] scoped infixr:35 " ∗ " => hsep

/-- `a ↦ v`. -/
def pt (a v : Nat) : HProp := fun h => h = Heap.single a v

/-- `emp`. -/
def hemp : HProp := fun h => h = Heap.empty

end Silmaril.X86.Concurrency.Cir.Csl

namespace Silmaril.X86.Concurrency.Cir

open Csl (Heap)

/-! ## Labels as memory effects -/

/-- The value a block leaves in cell `a` (the last write to `a`). -/
def cellLast : List (Nat × Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | c :: cs, a => (cellLast cs a).or (if c.1 = a then some c.2.2 else none)

/-- The cells a label reads, with the values it read. -/
def Lab.reads : Lab → List (Nat × Nat)
  | .rd _ _ a _ v => [(a, v)]
  | .rmw _ a _ o _ => [(a, o)]
  | .fwait a _ s _ => [(a, s)]
  | .fblock a e => [(a, e)]
  | .blk _ ins _ _ => ins.map fun c => (c.1, c.2.2)
  | _ => []

/-- The value a label leaves in cell `a`, if it writes `a`. -/
def Lab.wval : Lab → Nat → Option Nat
  | .wr _ _ a _ v, x => if a = x then some v else none
  | .rmw _ a _ _ n, x => if a = x then some n else none
  | .blk _ _ outs _, x => cellLast outs x
  | _, _ => none

/-- The label touches cell `a` (reads or writes it). -/
def Lab.Touches (l : Lab) (a : Nat) : Prop := (∃ v, (a, v) ∈ l.reads) ∨ (l.wval a).isSome

/-- The label's reads agree with `H`. -/
def Lab.okH (H : Heap) (l : Lab) : Prop := ∀ p ∈ l.reads, H p.1 = some p.2

/-- The label's writes applied to `H`. -/
def Lab.updH (H : Heap) (l : Lab) : Heap := fun a => (l.wval a).or (H a)

/-- A non-atomic access: an `na` load or store, or a `local` block. -/
def Lab.na : Lab → Bool
  | .rd .na .. | .wr .na .. | .blk .. => true
  | _ => false

/-- On x86 the label needs an empty store buffer: a locked RMW, `mfence`, a futex call. -/
def Lab.drains : Lab → Bool
  | .rmw .. | .fence .mfence | .fwait .. | .fwake .. | .fblock .. => true
  | _ => false

/-- A memory label (not `spawn`/`join`, which these machines do not model). -/
def Lab.isMem : Lab → Bool
  | .spawn _ | .join _ => false
  | _ => true

/-- The label is a store of flavour `nt` or `str`. -/
def Lab.weakStore : Lab → Bool
  | .wr _ fl _ _ _ => fl != .wb
  | _ => false

end Silmaril.X86.Concurrency.Cir

namespace Silmaril.X86.Concurrency.Cir.Csl

open Silmaril.X86.Concurrency.Cir

/-! ## Thread steps -/

/-- Update one thread. -/
def upd {α : Type} (f : Nat → α) (t : Nat) (x : α) : Nat → α := fun u => if u = t then x else f u

/-- **Small steps of one thread.** Reads return any value that fits; the machine decides. -/
inductive TStep : Stmt → Regs → Option Lab → Stmt → Regs → Prop
  | assign {d e rs} : TStep (.assign d e) rs none .skip (rs.set d (e.eval rs))
  | load {d m sz fl a rs v} (hv : v < 2 ^ (8 * sz)) :
      TStep (.load d m sz fl a) rs (some (.rd m fl (a.eval rs).toNat sz v)) .skip
        (rs.set d (BitVec.ofNat 64 v))
  | store {m sz fl a v rs} :
      TStep (.store m sz fl a v) rs
        (some (.wr m fl (a.eval rs).toNat sz ((v.eval rs).toNat % 2 ^ (8 * sz)))) .skip rs
  | rmw {d m sz op a arg rs old} (hv : old < 2 ^ (8 * sz)) :
      TStep (.rmw d m sz op a arg) rs
        (some (.rmw m (a.eval rs).toNat sz old (op.result rs sz old (arg.eval rs)))) .skip
        (rs.set d (BitVec.ofNat 64 old))
  | fence {k rs} : TStep (.fence k) rs (some (.fence k)) .skip rs
  | fwait {d a v rs seen r} (hv : seen < 2 ^ 32) (hr : r < 2 ^ 8) :
      TStep (.futexWait d a v) rs
        (some (.fwait (a.eval rs).toNat ((v.eval rs).toNat % 2 ^ 32) seen r)) .skip
        (rs.set d (BitVec.ofNat 64 (if seen = (v.eval rs).toNat % 2 ^ 32 then 0 else eagain)))
  | fwake {a n rs q} (hq : q < 2 ^ 8) :
      TStep (.futexWake a n) rs (some (.fwake (a.eval rs).toNat (n.eval rs).toNat q)) .skip rs
  | spawn {t rs} : TStep (.spawn t) rs (some (.spawn t)) .skip rs
  | join {t rs} : TStep (.join t) rs (some (.join t)) .skip rs
  | blk {b rs ivs rvs ovs}
      (hspec : b.spec (b.rin.map (fun r => (rs r).toNat) ++ ivs) (rvs ++ ovs))
      (hi : ivs.length = b.ins.length) (hr : rvs.length = b.rout.length)
      (ho : ovs.length = b.outs.length) :
      TStep (.local b) rs (some (.blk b.name (cellVals b.ins ivs) (cellVals b.outs ovs) rvs))
        .skip (rs.setMany b.rout rvs)
  | seq {s t rs l s' rs'} (h : TStep s rs l s' rs') : TStep (.seq s t) rs l (.seq s' t) rs'
  | seqSkip {t rs} : TStep (.seq .skip t) rs none t rs
  | iteT {c s t rs} (h : truthy (c.eval rs) = true) : TStep (.ite c s t) rs none s rs
  | iteF {c s t rs} (h : truthy (c.eval rs) = false) : TStep (.ite c s t) rs none t rs
  | loopT {n c b rs} (h : truthy (c.eval rs) = true) :
      TStep (.loop (n + 1) c b) rs none (.seq b (.loop n c b)) rs
  | loopF {n c b rs} (h : truthy (c.eval rs) = false) : TStep (.loop n c b) rs none .skip rs

/-! ## The SC machine -/

/-- A configuration: thread states and one memory. -/
structure Cfg where
  ts : Nat → Stmt × Regs
  mem : Heap

/-- **SC interleaving** of threads `0 … N-1`. A label step needs its cells mapped and its
reads to agree with memory. -/
inductive ScStep (N : Nat) : Cfg → Cfg → Prop
  | tau {C t s' rs'} (ht : t < N) (hs : TStep (C.ts t).1 (C.ts t).2 none s' rs') :
      ScStep N C ⟨upd C.ts t (s', rs'), C.mem⟩
  | lab {C t l s' rs'} (ht : t < N) (hs : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs')
      (hm : l.isMem = true) (hc : ∀ a, l.Touches a → (C.mem a).isSome) (hok : l.okH C.mem) :
      ScStep N C ⟨upd C.ts t (s', rs'), l.updH C.mem⟩

/-- Reflexive-transitive closure. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl {a} : Star r a a
  | step {a b c} (h : r a b) (h' : Star r b c) : Star r a c

/-- SC reachability. -/
abbrev ScReach (N : Nat) : Cfg → Cfg → Prop := Star (ScStep N)

/-- Every thread below `N` has finished. -/
def Cfg.Done (N : Nat) (C : Cfg) : Prop := ∀ t < N, (C.ts t).1 = .skip

/-! ## Store-buffer machines: TSO and XL -/

/-- A store-buffer entry: a store of `v` to cell `a` (weak if `nt`/`str`), or an `sfence`
barrier. -/
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
def view (mem : Heap) (b : List Ent) : Heap := fun a => (newest b a).or (mem a)

end Silmaril.X86.Concurrency.Cir.Csl

namespace Silmaril.X86.Concurrency.Cir

open Csl (Ent)

/-- The buffer entries of a non-draining label. -/
def Lab.ents : Lab → List Ent
  | .wr _ fl a _ v => [.st a v (fl != .wb)]
  | .blk _ _ outs _ => outs.map fun c => .st c.1 c.2.2 false
  | .fence .sfence => [.bar]
  | _ => []

end Silmaril.X86.Concurrency.Cir

namespace Silmaril.X86.Concurrency.Cir.Csl

open Silmaril.X86.Concurrency.Cir

/-- XL's flush order: entry `e` may leave the buffer before the earlier entries `pre`. A
barrier must be oldest; a store may not pass a barrier, an earlier store to the same cell, or
an earlier store when both are write-back. -/
def Ent.passes : Ent → List Ent → Prop
  | .bar, pre => pre = []
  | .st a _ w, pre => ∀ e ∈ pre, match e with
    | .bar => False
    | .st a' _ w' => a' ≠ a ∧ (w = true ∨ w' = true)

/-- Flush an entry into memory. -/
def Ent.apply (mem : Heap) : Ent → Heap
  | .st a v _ => fun x => if x = a then some v else mem x
  | .bar => mem

/-- The buffered models. -/
inductive OModel where
  | tso
  | xl
  deriving DecidableEq, Repr

/-- A buffered configuration. -/
structure OCfg where
  ts : Nat → Stmt × Regs
  mem : Heap
  buf : Nat → List Ent

/-- **Store-buffer steps** of threads `0 … N-1` under TSO or XL. -/
inductive OStep (M : OModel) (N : Nat) : OCfg → OCfg → Prop
  | tau {C t s' rs'} (ht : t < N) (hs : TStep (C.ts t).1 (C.ts t).2 none s' rs') :
      OStep M N C { C with ts := upd C.ts t (s', rs') }
  /-- A non-draining label: reads its view, buffers its writes. -/
  | buffered {C t l s' rs'} (ht : t < N) (hs : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs')
      (hm : l.isMem = true) (hd : l.drains = false) (hc : ∀ a, l.Touches a → (C.mem a).isSome)
      (hok : l.okH (view C.mem (C.buf t))) :
      OStep M N C { C with ts := upd C.ts t (s', rs'), buf := upd C.buf t (C.buf t ++ l.ents) }
  /-- A draining label: needs an empty buffer, acts on memory. -/
  | drained {C t l s' rs'} (ht : t < N) (hs : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs')
      (hm : l.isMem = true) (hd : l.drains = true) (he : C.buf t = [])
      (hc : ∀ a, l.Touches a → (C.mem a).isSome) (hok : l.okH C.mem) :
      OStep M N C { C with ts := upd C.ts t (s', rs'), mem := l.updH C.mem }
  /-- A flush: TSO only the oldest entry; XL any entry its order allows. -/
  | flush {C t pre e post} (ht : t < N) (hb : C.buf t = pre ++ e :: post)
      (hp : e.passes pre) (hmod : M = .xl ∨ pre = []) :
      OStep M N C { C with mem := e.apply C.mem, buf := upd C.buf t (pre ++ post) }

/-- Buffered reachability. -/
abbrev OReach (M : OModel) (N : Nat) : OCfg → OCfg → Prop := Star (OStep M N)

/-- An SC configuration with empty buffers. -/
def Cfg.toO (C : Cfg) : OCfg := ⟨C.ts, C.mem, fun _ => []⟩

/-- All buffers are empty. -/
def OCfg.Drained (C : OCfg) : Prop := ∀ t, C.buf t = []

/-- The first buffered value of cell `a` among the threads `us`. -/
def firstNewest (buf : Nat → List Ent) (a : Nat) : List Nat → Option Nat
  | [] => none
  | u :: us => (newest (buf u) a).or (firstNewest buf a us)

/-- **The abstraction of a buffered configuration**: every buffered value installed (under
the ownership invariant at most one thread buffers a cell). Unmapped cells stay unmapped. -/
def OCfg.abs (N : Nat) (C : OCfg) : Cfg :=
  ⟨C.ts, fun a => (C.mem a).map fun v => (firstNewest C.buf a (List.range N)).getD v⟩

/-! ## Ownership safety -/

/-- **The obligations of one label step** of a thread owning `h`, whose successor heap must
satisfy `K`: a non-atomic label touches only owned cells; an atomic one may also touch the
invariant's heap and re-split ownership with it; a non-draining one writes only owned cells and
gives up none. See the module documentation. -/
def LabOk (I : HProp) (K : Heap → Prop) (l : Lab) (h : Heap) : Prop :=
  l.isMem = true ∧
    (l.na = true → (∀ a, l.Touches a → (h a).isSome) ∧ (l.okH h → K (l.updH h))) ∧
    (l.na = false → ∀ hI, I hI → Heap.Disjoint h hI →
      (∀ a, l.Touches a → (Heap.union h hI a).isSome) ∧
      (l.drains = false → ∀ a, (l.wval a).isSome → (h a).isSome) ∧
      (l.okH (Heap.union h hI) → ∃ h' hI', Heap.Disjoint h' hI' ∧
        Heap.union h' hI' = l.updH (Heap.union h hI) ∧ I hI' ∧ K h' ∧
        (l.drains = false → ∀ a, (h a).isSome → (h' a).isSome)))

/-- **The safety functional**: at `skip` the postcondition holds, silent steps keep the heap,
and every label step meets `LabOk`; successors must satisfy `R`. -/
def SafeF (I : HProp) (Q : Regs → HProp) (R : Stmt → Regs → Heap → Prop) (s : Stmt)
    (rs : Regs) (h : Heap) : Prop :=
  (s = .skip → Q rs h) ∧
  (∀ s' rs', TStep s rs none s' rs' → R s' rs' h) ∧
  (∀ l s' rs', TStep s rs (some l) s' rs' → LabOk I (R s' rs') l h)

/-- **Ownership safety** (greatest fixed point of `SafeF`): some post-fixed relation holds. -/
def Safe (I : HProp) (Q : Regs → HProp) (s : Stmt) (rs : Regs) (h : Heap) : Prop :=
  ∃ R : Stmt → Regs → Heap → Prop, R s rs h ∧ ∀ s rs h, R s rs h → SafeF I Q R s rs h

/-- **The global CSL invariant** of an SC configuration with ghost heaps `hs` (per thread)
and `hI` (the invariant's). -/
def GInv (I : HProp) (Q : Nat → Regs → HProp) (N : Nat) (C : Cfg) (hs : Nat → Heap)
    (hI : Heap) : Prop :=
  (∀ t u, t ≠ u → Heap.Disjoint (hs t) (hs u)) ∧ (∀ t, Heap.Disjoint (hs t) hI) ∧
  (∀ t, Heap.Le (hs t) C.mem) ∧ Heap.Le hI C.mem ∧ I hI ∧
  ∀ t < N, Safe I (Q t) (C.ts t).1 (C.ts t).2 (hs t)

/-- **The buffered invariant**: `GInv` of the abstraction, and each buffered cell is owned
by its (running) thread. -/
def XInv (I : HProp) (Q : Nat → Regs → HProp) (N : Nat) (C : OCfg) (hs : Nat → Heap)
    (hI : Heap) : Prop :=
  GInv I Q N (C.abs N) hs hI ∧ ∀ t a, (newest (C.buf t) a).isSome → t < N ∧ (hs t a).isSome

/-! ## Races -/

/-- **A race** in an SC configuration: two different threads can each take a label step,
both touch a cell, and at least one of the two is non-atomic. -/
def Race (N : Nat) (C : Cfg) : Prop :=
  ∃ t u l l' a, t < N ∧ u < N ∧ t ≠ u ∧
    (∃ s' rs', TStep (C.ts t).1 (C.ts t).2 (some l) s' rs') ∧
    (∃ s' rs', TStep (C.ts u).1 (C.ts u).2 (some l') s' rs') ∧
    l.Touches a ∧ l'.Touches a ∧ (l.na = true ∨ l'.na = true)

/-! ## From CIR programs -/

/-- The initial cell heap of a list of locations (the first location at an address wins). -/
def initHeap (locs : List Silmaril.X86.MemoryModel.Litmus.Loc) : Heap := fun a =>
  (locs.find? fun l => l.addr == a).map (·.init)

/-- The initial configuration of a CIR program. -/
def progInit (P : Prog) : Cfg :=
  ⟨fun i => ((P.threads[i]?.map Thread.body).getD .skip, Regs.zero), initHeap P.locs⟩

/-! ## The bridge from axiomatic XL -/

/-- **The bridge** (proved as `Csl.cirXlOpAx_holds` in `Cir/Csl/Thms.lean`): every axiomatic XL
behaviour (hence every TSO and SC behaviour,
`Cir.sc_le_xl`) of a uniform, spawn-free CIR program with positive access sizes **whose
CIR-native start is CSL-certified** is a final state of the CIR-native store-buffer XL machine:
all threads done, buffers drained, the same registers, and every location holding the
little-endian value of its final bytes.

The CSL hypothesis is needed: the CIR-native machines run a `local` block as one step,
reading all its input cells at once, while the axiomatic models see one load per input cell.
`MP+block` is uniform and spawn-free, axiomatic SC allows its
torn block read, and no run of `OStep .xl` reaches it. Under CSL a block touches only owned
cells, which no other thread writes, so the tear is not observable.

Scope: `Prog.uniformB` makes every access write-back, so this bridge covers the TSO part of XL
only (on uniform programs XL is TSO). Extending it to `nt`/`str` stores needs more than
`Ent.passes`: `ppoXl` also drops the order from an earlier **load** to a later weak store, which
no store-buffer machine (stores enter the buffer after earlier loads have read) reproduces;
e.g. `r0 = x; y :=nt 1 ∥ y := 2; mfence; x := 1` with `r0 = 1` and final `y = 2` is
axiomatically XL-allowed but, by an unformalised
argument, not an `OStep .xl` final. Under CSL the weak store is to an
owned cell, so again the reordering is not observable.

Proof idea (ax ⊆ op). For a uniform program every unit is a whole cell (no tearing: `Exec.tearable`
is false on aligned, same-footprint units), so each read takes its value from one write
(`Task.cirDomain`'s first step). Linearise `ghbXl` (acyclic by `Exec.Xl`; on uniform programs
it is TSO's `ghb`) and schedule: a write unit is its buffered store at its `po` position and
its flush at its `ghbXl` position; `lockXl` and `mfence` are the empty-buffer conditions. A
`local` block is scheduled as one step at the position of its first load: by the CSL
certificate (`Csl.no_race` on the SC machine, transported along the schedule) no other thread
writes its cells between its loads and stores. -/
def Task.cirXlOpAx : Prop :=
  ∀ (P : Prog), P.uniformB = true →
    (P.threads.all fun th => th.body.threadFree && th.body.posSizes && !th.spawned) = true →
    (∃ (I : HProp) (Q : Nat → Regs → HProp) (hs : Nat → Heap) (hI : Heap),
      GInv I Q P.threads.length (progInit P) hs hI) →
    ∀ f, Behav P Silmaril.X86.MemoryModel.Axiomatic.Exec.Xl f →
    ∃ C : OCfg, OReach .xl P.threads.length (progInit P).toO C ∧ C.Drained ∧
      (∀ t < P.threads.length, (C.ts t).1 = .skip ∧ f.regs t = (C.ts t).2) ∧
      ∀ l ∈ P.locs, Silmaril.X86.MemoryModel.Litmus.leValue f.mem l.addr l.size = C.mem l.addr

end Silmaril.X86.Concurrency.Cir.Csl

namespace Silmaril.X86.Concurrency.Cir.Csl.Ex

open Silmaril.X86.Concurrency.Cir

/-! ## A non-vacuity example: owned data next to a shared counter

Two threads. Thread `t` writes its own cell `8t` non-atomically, then does a `lock xadd` on a
shared counter at `16`, which lives in the invariant `∃ v, 16 ↦ v`. -/

/-- The counter. -/
def ctr : Nat := 16

/-- Thread `t`'s body: `[8t] := t + 1` (`na`), then `fetch_add(&ctr, 1)` (`sc`). -/
def body (t : Nat) : Stmt :=
  .seq (.store .na 8 .wb (.lit (8 * t)) (.lit (t + 1))) (.rmw .rax .sc 8 .fadd (.lit ctr) (.lit 1))

/-- The start: two threads, cells `0`, `8` and the counter all `0`. -/
def start : Cfg :=
  ⟨fun t => (if t < 2 then body t else .skip, Regs.zero),
    fun a => if a = 0 ∨ a = 8 ∨ a = ctr then some 0 else none⟩

/-- The invariant: the counter holds some value. -/
def inv : HProp := fun h => ∃ v, h = Heap.single ctr v

/-- Thread `t` ends owning its cell, holding `t + 1`. -/
def post (t : Nat) : Regs → HProp := fun _ h => h = Heap.single (8 * t) (t + 1)

/-- The ghost start: each thread owns its cell. -/
def own (t : Nat) : Heap := if t < 2 then Heap.single (8 * t) 0 else Heap.empty

/-- The example as a CIR program: three 8-byte locations at `0`, `8` and the
counter, and the two threads. Its CIR-native start is `start`. -/
def prog : Prog :=
  ⟨[⟨"a", 0, 8, 0⟩, ⟨"b", 8, 8, 0⟩, ⟨"ctr", ctr, 8, 0⟩], [⟨body 0, false⟩, ⟨body 1, false⟩]⟩

end Silmaril.X86.Concurrency.Cir.Csl.Ex

namespace Silmaril.X86.Concurrency.Cir.Csl.Ex

open Silmaril.X86.Concurrency.Cir

/-! ## A weak-behaviour witness: store buffering

`SB`: thread `0` stores `1` to cell `0` and loads cell `8`; thread `1` stores `1` to cell `8` and
loads cell `0` (all `rlx`, plain `mov`s). Both loads may return `0` on the buffered machines. -/

/-- `SB`'s thread `t`. -/
def sbBody (t : Nat) : Stmt :=
  .seq (.store .rlx 8 .wb (.lit (8 * t)) (.lit 1)) (.load .rbx .rlx 8 .wb (.lit (8 - 8 * t)))

/-- `SB`'s start: cells `0` and `8` hold `0`. -/
def sbStart : Cfg :=
  ⟨fun t => (if t < 2 then sbBody t else .skip, Regs.zero),
    fun a => if a = 0 ∨ a = 8 then some 0 else none⟩

end Silmaril.X86.Concurrency.Cir.Csl.Ex
