module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Drf
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Example
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Bridge
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Main
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.ExBehav

/-!
# CSL over CIR: the rules, soundness, race freedom and DRF ⇒ SC under TSO and XL

Everything here is PROVED (standard axioms
only). `drf_behav_of_bridge` is kept as the earlier form conditional on `Task.cirXlOpAx`, which
is now proved (`cirXlOpAx_holds`); `drf_behav` is its unconditional form. Proofs are in
`Silmaril/Proofs/X86/Concurrency/Cir/Csl/` (the bridge in its `XlOp/` subdirectory).

## Thread-local rules (on `Safe`)

* structural: `safe_skip`, `safe_conseq`, `safe_seq`, `safe_ite`, `safe_loop` (bounded loops
  with an invariant indexed by the remaining bound);
* **frame**: `safe_frame`;
* **atomic invariant access**: `safe_atomic`, the generic one-step rule;
* owned non-atomic accesses: `safe_load_na`, `safe_store_na`;
* **`lift_sequential`**: a `local(B)` block over owned cells is a CSL step whose
  only obligation is its sequential contract `B.spec`.

## Program-level results

* **parallel composition / adequacy on SC**: `csl_sc` — from `GInv` (each thread `Safe` on its
  own heap, all heaps disjoint, the invariant's heap satisfying `I`), every SC-reachable
  configuration satisfies `GInv` again, and a finished one satisfies every postcondition.
* **race freedom**: `no_race` (owned non-atomic accesses never race with any access of
  another thread), `weak_owned` (`nt`/`str` stores are always to owned cells).
* **DRF ⇒ SC under TSO and XL**: `drf_sc` — every configuration the store-buffer TSO or XL
  machine reaches from a CSL-certified start abstracts (buffers installed) to an
  SC-reachable configuration; drained, it *is* one (`drf_sc_drained`); `csl_buffered`:
  finished and drained, every postcondition holds of the final memory.
* `tso_le_xl_op`: the TSO machine's runs are XL machine runs.
* **`cirXlOpAx_holds`**: the bridge `Task.cirXlOpAx` holds. Every axiomatic XL
  (hence TSO and SC) behaviour of a uniform, thread-free, positive-size CIR program whose
  CIR-native start is CSL-certified is a drained final state of the store-buffer XL machine
  `OStep .xl`, with the same registers and location values.
* **`drf_behav`**: so every axiomatic XL (and so TSO and SC) behaviour of a uniform,
  CSL-certified CIR program is a final state of the CIR-native SC machine satisfying the
  postconditions. `drf_behav_of_bridge` is the earlier form, conditional on the bridge.
* `cirXlOpAx_needs_csl`: the bridge needs its CSL hypothesis. `MP+block` has an
  axiomatic SC behaviour (a block's two loads torn by another thread's stores) that no run of
  the XL store-buffer machine, where blocks are atomic, reaches.

## Non-vacuity

* `Ex.certified`: the CSL certificate of a two-thread program (each thread writes its own
  cell non-atomically, then does a `lock xadd` on a shared counter held by the invariant) is
  proved with the rules above;
* `Ex.buffered`: so every finished, drained TSO/XL state of it holds both threads' values;
* `Ex.xl_behav`: and, through the bridge, so does every axiomatic XL (hence TSO and SC)
  behaviour of the example as a CIR program (`Ex.prog`, `Ex.prog_init`);
  `Ex.xl_behav_some`: such a behaviour exists (the enumerator);
* `Ex.sb_weak`: the buffered machines are weak — TSO (hence XL) reaches the store-buffering
  outcome of `SB` (both loads `0`), and `Ex.sb_sc`: the SC machine does not, so the
  DRF theorem says something.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Csl

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy cellVals Block Flav Mode)

variable {I : HProp}

/-! ## Thread-local rules -/

theorem safe_skip {Q : Regs → HProp} {rs : Regs} {h : Heap} (hq : Q rs h) :
    Safe I Q .skip rs h := Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_skip hq

theorem safe_conseq {Q Q' : Regs → HProp} (hQ : ∀ rs h, Q rs h → Q' rs h) {s : Stmt}
    {rs : Regs} {h : Heap} (H : Safe I Q s rs h) : Safe I Q' s rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_conseq hQ H

/-- **Sequential composition.** -/
theorem safe_seq {Q : Regs → HProp} {s t : Stmt} {rs : Regs} {h : Heap}
    (H : Safe I (fun rs h => Safe I Q t rs h) s rs h) : Safe I Q (.seq s t) rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_seq H

/-- **Conditionals.** -/
theorem safe_ite {Q : Regs → HProp} {c : Expr} {s t : Stmt} {rs : Regs} {h : Heap}
    (hs : truthy (c.eval rs) = true → Safe I Q s rs h)
    (ht : truthy (c.eval rs) = false → Safe I Q t rs h) : Safe I Q (.ite c s t) rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_ite hs ht

/-- **Bounded loops.** -/
theorem safe_loop {Q : Regs → HProp} {c : Expr} {b : Stmt} (J : Nat → Regs → Heap → Prop)
    (hexit : ∀ k rs h, J k rs h → truthy (c.eval rs) = false → Q rs h)
    (hbody : ∀ k rs h, J (k + 1) rs h → truthy (c.eval rs) = true → Safe I (J k) b rs h)
    {n : Nat} {rs : Regs} {h : Heap} (hJ : J n rs h) : Safe I Q (.loop n c b) rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_loop J hexit hbody hJ

/-- **Frame rule.** -/
theorem safe_frame {Q : Regs → HProp} {F : HProp} {s : Stmt} {rs : Regs} {h hF : Heap}
    (H : Safe I Q s rs h) (hd : Heap.Disjoint h hF) (hf : F hF) :
    Safe I (fun rs => Q rs ∗ F) s rs (Heap.union h hF) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_frame H hd hf

/-- **Atomic invariant access** (generic one-step rule). -/
theorem safe_atomic {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (hs : s ≠ .skip) (hτ : ∀ s' rs', ¬ TStep s rs none s' rs')
    (hl : ∀ l s' rs', TStep s rs (some l) s' rs' → s' = .skip ∧ LabOk I (Q rs') l h) :
    Safe I Q s rs h := Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_atomic hs hτ hl

/-- **Owned non-atomic load.** -/
theorem safe_load_na {Q : Regs → HProp} {d : Silmaril.X86.Reg} {sz : Nat} {fl : Flav}
    {a : Expr} {rs : Regs} {h : Heap} {v : Nat} (hv : h (a.eval rs).toNat = some v)
    (hq : Q (rs.set d (BitVec.ofNat 64 v)) h) : Safe I Q (.load d .na sz fl a) rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_load_na hv hq

/-- **Owned non-atomic store.** -/
theorem safe_store_na {Q : Regs → HProp} {sz : Nat} {fl : Flav} {a v : Expr} {rs : Regs}
    {h : Heap} (ha : (h (a.eval rs).toNat).isSome)
    (hq : Q rs
      ((.wr .na fl (a.eval rs).toNat sz ((v.eval rs).toNat % 2 ^ (8 * sz)) : Lab).updH h)) :
    Safe I Q (.store .na sz fl a v) rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_store_na ha hq

/-- **`lift_sequential`**: a `local(B)` block over owned cells is a valid CSL step whose only
obligation is its sequential contract `B.spec`; nothing about the block is re-proved, and the
step is safe whatever the other threads do. -/
theorem lift_sequential {Q : Regs → HProp} {b : Block} {rs : Regs} {h : Heap}
    (hin : ∀ c ∈ b.ins, (h c.1).isSome) (hout : ∀ c ∈ b.outs, (h c.1).isSome)
    (hq : ∀ ivs rvs ovs, ivs.length = b.ins.length → rvs.length = b.rout.length →
      ovs.length = b.outs.length →
      b.spec (b.rin.map (fun r => (rs r).toNat) ++ ivs) (rvs ++ ovs) →
      (∀ c ∈ cellVals b.ins ivs, h c.1 = some c.2.2) →
      Q (rs.setMany b.rout rvs)
        ((.blk b.name (cellVals b.ins ivs) (cellVals b.outs ovs) rvs : Lab).updH h)) :
    Safe I Q (.local b) rs h := Silmaril.Proofs.X86.Concurrency.Cir.Csl.safe_local hin hout hq

/-! ## Program-level results -/

variable {Q : Nat → Regs → HProp} {N : Nat}

/-- **CSL soundness on the SC machine** (parallel composition and adequacy): from a `GInv`
start, every SC-reachable configuration satisfies `GInv`, and a finished one satisfies every
thread's postcondition on disjoint parts of memory, next to the invariant. -/
theorem csl_sc {C0 C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C0 hs hI)
    (hr : ScReach N C0 C) :
    (∃ hs' hI', GInv I Q N C hs' hI') ∧
    (C.Done N → ∃ (hs' : Nat → Heap) (hI' : Heap), (∀ t < N, Q t (C.ts t).2 (hs' t)) ∧ I hI' ∧
      (∀ t u, t ≠ u → Heap.Disjoint (hs' t) (hs' u)) ∧ (∀ t, Heap.Disjoint (hs' t) hI') ∧
      (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem) := by
  obtain ⟨hs', hI', G'⟩ := Silmaril.Proofs.X86.Concurrency.Cir.Csl.ginv_reach hr G
  exact ⟨⟨hs', hI', G'⟩, fun hd =>
    ⟨hs', hI', Silmaril.Proofs.X86.Concurrency.Cir.Csl.ginv_done G' hd⟩⟩

/-- **Owned non-atomic accesses never race**: in every SC-reachable configuration of a
CSL-certified program, no non-atomic access of one thread touches a cell any access of another
thread touches. -/
theorem no_race {C0 C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C0 hs hI)
    (hr : ScReach N C0 C) : ¬ Race N C := by
  obtain ⟨hs', hI', G'⟩ := Silmaril.Proofs.X86.Concurrency.Cir.Csl.ginv_reach hr G
  exact Silmaril.Proofs.X86.Concurrency.Cir.Csl.ginv_no_race G'

/-- **Weak stores need ownership**: an enabled `nt`/`str` store writes an owned cell. -/
theorem weak_owned {C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C hs hI) {t : Nat}
    (ht : t < N) {l : Lab} {s' : Stmt} {rs' : Regs}
    (st : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs') (hw : l.weakStore = true) :
    ∀ a, l.Touches a → (hs t a).isSome :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.ginv_weak_owned G ht st hw

/-- **Ownership ⇒ DRF ⇒ SC, under TSO and XL.** Every configuration the store-buffer machine
reaches from a CSL-certified start abstracts (each thread's buffered values installed) to an
SC-reachable configuration, and the buffered CSL invariant (`XInv`) holds there. -/
theorem drf_sc {M : OModel} {C0 : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C0 hs hI)
    {C : OCfg} (h : OReach M N C0.toO C) :
    ScReach N C0 (C.abs N) ∧ ∃ hs' hI', XInv I Q N C hs' hI' :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.drf_reach G h

/-- **Drained TSO/XL states are SC states** (the CIR restatement of `Pool.Task.drfTso`, with
resource invariants, proved). -/
theorem drf_sc_drained {M : OModel} {C0 : Cfg} {hs : Nat → Heap} {hI : Heap}
    (G : GInv I Q N C0 hs hI) {C : OCfg} (h : OReach M N C0.toO C) (hd : C.Drained) :
    ScReach N C0 ⟨C.ts, C.mem⟩ := by
  have := (Silmaril.Proofs.X86.Concurrency.Cir.Csl.drf_reach G h).1
  rwa [Silmaril.Proofs.X86.Concurrency.Cir.Csl.abs_drained hd] at this

/-- **Adequacy under TSO and XL**: a finished, drained configuration reached from a
CSL-certified start satisfies every postcondition on disjoint parts of the final memory. -/
theorem csl_buffered {M : OModel} {C0 : Cfg} {hs : Nat → Heap} {hI : Heap}
    (G : GInv I Q N C0 hs hI) {C : OCfg} (h : OReach M N C0.toO C) (hd : C.Drained)
    (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ (hs' : Nat → Heap) (hI' : Heap), (∀ t < N, Q t (C.ts t).2 (hs' t)) ∧ I hI' ∧
      (∀ t u, t ≠ u → Heap.Disjoint (hs' t) (hs' u)) ∧ (∀ t, Heap.Disjoint (hs' t) hI') ∧
      (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem :=
  (csl_sc G (drf_sc_drained G h hd)).2 hfin

/-- The TSO machine's steps are XL machine steps (FIFO flushes are allowed XL flushes). -/
theorem tso_le_xl_op {C C' : OCfg} (h : OStep .tso N C C') : OStep .xl N C C' := by
  cases h with
  | tau ht hs => exact .tau ht hs
  | buffered ht hs hm hd hc hok => exact .buffered ht hs hm hd hc hok
  | drained ht hs hm hd he hc hok => exact .drained ht hs hm hd he hc hok
  | flush ht hb hp _ => exact .flush ht hb hp (Or.inl rfl)

theorem tso_reach_xl {C C' : OCfg} (h : OReach .tso N C C') : OReach .xl N C C' := by
  induction h with
  | refl => exact Star.refl
  | step h _ ih => exact Star.step (tso_le_xl_op h) ih

/-- **From the axiomatic models (Task-conditional form, kept).** With the bridge
`Task.cirXlOpAx` (now proved: `cirXlOpAx_holds`; unconditional form `drf_behav`), every
axiomatic XL behaviour (so every TSO and SC behaviour) of a uniform, spawn-free CIR program
`P` whose CIR-native start is CSL-certified is a finished state of the SC machine, in which
every postcondition holds. -/
theorem drf_behav_of_bridge (hb : Task.cirXlOpAx) {P : Silmaril.X86.Concurrency.Cir.Prog}
    (hu : P.uniformB = true)
    (ht : (P.threads.all fun th => th.body.threadFree && th.body.posSizes && !th.spawned) = true)
    {Q : Nat → Regs → HProp} {hs : Nat → Heap} {hI : Heap}
    (G : GInv I Q P.threads.length (progInit P) hs hI)
    {f : Silmaril.X86.MemoryModel.Litmus.Final}
    (hf : Silmaril.X86.Concurrency.Cir.Behav P Silmaril.X86.MemoryModel.Axiomatic.Exec.Xl f) :
    ∃ C : OCfg, ScReach P.threads.length (progInit P) ⟨C.ts, C.mem⟩ ∧
      (∀ t < P.threads.length, (C.ts t).1 = .skip ∧ f.regs t = (C.ts t).2) ∧
      (∀ l ∈ P.locs, Silmaril.X86.MemoryModel.Litmus.leValue f.mem l.addr l.size = C.mem l.addr) ∧
      ∃ (hs' : Nat → Heap) (hI' : Heap), (∀ t < P.threads.length, Q t (C.ts t).2 (hs' t)) ∧ I hI' ∧
        (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem := by
  obtain ⟨C, hr, hd, hfin, hm⟩ := hb P hu ht ⟨I, Q, hs, hI, G⟩ f hf
  obtain ⟨hs', hI', q, i, -, -, l1, l2⟩ := csl_buffered G hr hd fun t h => (hfin t h).1
  exact ⟨C, drf_sc_drained G hr hd, hfin, hm, hs', hI', q, i, l1, l2⟩

/-- **The bridge**: `Task.cirXlOpAx` holds.

Proof (`Silmaril/Proofs/X86/Concurrency/Cir/Csl/XlOp/`): a uniform candidate is tame, so it is
x86-TSO-consistent; the clock `κ` (copied) extends its `ghb` and puts each locked write one
tick after its read. Tick by tick the CIR-native configuration is given in closed form: a load,
a locked read-modify-write, a futex call or a block runs at the tick of its trigger (a block at
its last load), stores enter the buffer when their thread catches up and are flushed at their
own tick. A read sees its `rf` source (`H.readOK`). A block's earlier loads are not torn: a
write of another thread becoming visible between the block's first and last load would, in the
configuration the schedule reaches at that tick, have the block's thread about to run the block
(so owning the cell, by its CSL safety) while the writer buffers the cell or locks it, against
the disjointness of ownership (`Runs.interfere`, through `drf_sc`'s `XInv`). -/
theorem cirXlOpAx_holds : Task.cirXlOpAx := Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.cirXlOpAx

/-- **From the axiomatic models.** Every axiomatic XL behaviour (so every TSO and SC
behaviour) of a uniform, spawn-free CIR program `P` whose CIR-native start is CSL-certified is
a finished state of the SC machine, in which every postcondition holds. -/
theorem drf_behav {P : Silmaril.X86.Concurrency.Cir.Prog}
    (hu : P.uniformB = true)
    (ht : (P.threads.all fun th => th.body.threadFree && th.body.posSizes && !th.spawned) = true)
    {Q : Nat → Regs → HProp} {hs : Nat → Heap} {hI : Heap}
    (G : GInv I Q P.threads.length (progInit P) hs hI)
    {f : Silmaril.X86.MemoryModel.Litmus.Final}
    (hf : Silmaril.X86.Concurrency.Cir.Behav P Silmaril.X86.MemoryModel.Axiomatic.Exec.Xl f) :
    ∃ C : OCfg, ScReach P.threads.length (progInit P) ⟨C.ts, C.mem⟩ ∧
      (∀ t < P.threads.length, (C.ts t).1 = .skip ∧ f.regs t = (C.ts t).2) ∧
      (∀ l ∈ P.locs, Silmaril.X86.MemoryModel.Litmus.leValue f.mem l.addr l.size = C.mem l.addr) ∧
      ∃ (hs' : Nat → Heap) (hI' : Heap), (∀ t < P.threads.length, Q t (C.ts t).2 (hs' t)) ∧ I hI' ∧
        (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem :=
  drf_behav_of_bridge cirXlOpAx_holds hu ht G hf

/-- **The bridge needs ownership**. Without `Task.cirXlOpAx`'s CSL hypothesis the
bridge is false: `MP+block` (thread 0 stores `x` then `y`; thread 1's `local` block reads `x`
then `y`) is uniform and spawn-free, axiomatic SC (hence XL) has a behaviour with the torn read
`rax = 0`, `rbx = 1`, and no run of the XL store-buffer machine finishes with those registers,
because the CIR-native machines run a block in one step. -/
theorem cirXlOpAx_needs_csl : ∃ P : Silmaril.X86.Concurrency.Cir.Prog, P.uniformB = true ∧
    (P.threads.all fun th => th.body.threadFree && th.body.posSizes && !th.spawned) = true ∧
    ∃ f, Silmaril.X86.Concurrency.Cir.Behav P Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f ∧
      Silmaril.X86.Concurrency.Cir.Behav P Silmaril.X86.MemoryModel.Axiomatic.Exec.Xl f ∧
      ¬ ∃ C : OCfg, OReach .xl P.threads.length (progInit P).toO C ∧ C.Drained ∧
        (∀ t < P.threads.length, (C.ts t).1 = .skip ∧ f.regs t = (C.ts t).2) ∧
        ∀ l ∈ P.locs, Silmaril.X86.MemoryModel.Litmus.leValue f.mem l.addr l.size = C.mem l.addr := by
  open Silmaril.Proofs.X86.Concurrency.Cir.Csl.Bridge in
  obtain ⟨f, hf, h0, h1⟩ := behav_sc
  exact ⟨P, uniform, threads_ok, f, hf,
    Silmaril.X86.Concurrency.Cir.behav_mono Silmaril.X86.Concurrency.Cir.sc_le_xl hf,
    fun ⟨C, hr, _, hfin, _⟩ => not_reach f h0 h1 ⟨C, hr, hfin⟩⟩

/-! ## Non-vacuity: the example -/

/-- **The example's CSL certificate** (proved with `safe_seq`, `safe_store_na` and
`safe_atomic`). -/
theorem Ex.certified : GInv Ex.inv Ex.post 2 Ex.start Ex.own (Heap.single Ex.ctr 0) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex.ginv_start

/-- **DRF ⇒ SC on the example**: every finished, drained TSO/XL state holds `1` in cell `0`
and `2` in cell `8`. -/
theorem Ex.buffered {M : OModel} {C : OCfg} (h : OReach M 2 Ex.start.toO C) (hd : C.Drained)
    (hfin : ∀ t < 2, (C.ts t).1 = .skip) : C.mem 0 = some 1 ∧ C.mem 8 = some 2 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex.ex_buffered h hd hfin

/-- The example program's CIR-native start is the certified `Ex.start`. -/
theorem Ex.prog_init : progInit Ex.prog = Ex.start := by
  simp only [progInit, Ex.prog, Ex.start, Cfg.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext t
    rcases t with _ | _ | t
    · rfl
    · rfl
    · simp
  · funext a
    simp only [initHeap, List.find?, Ex.ctr]
    by_cases h0 : a = 0
    · subst h0; rfl
    · by_cases h8 : a = 8
      · subst h8; rfl
      · by_cases h16 : a = 16
        · subst h16; rfl
        · have e0 : (0 == a) = false := by simpa using Ne.symm h0
          have e8 : (8 == a) = false := by simpa using Ne.symm h8
          have e16 : (16 == a) = false := by simpa using Ne.symm h16
          simp [e0, e8, e16, h0, h8, h16]

/-- **The example under the axiomatic models** (by `drf_behav`): in every
axiomatic XL (hence TSO and SC) behaviour of `Ex.prog`, the two owned cells hold `1` and `2`
(little-endian, 8 bytes). The bridge makes the CSL certificate a statement about the byte-level
candidate executions, not only about the CIR-native machines. -/
theorem Ex.xl_behav {f : Silmaril.X86.MemoryModel.Litmus.Final}
    (hf : Silmaril.X86.Concurrency.Cir.Behav Ex.prog Silmaril.X86.MemoryModel.Axiomatic.Exec.Xl f) :
    Silmaril.X86.MemoryModel.Litmus.leValue f.mem 0 8 = some 1 ∧
      Silmaril.X86.MemoryModel.Litmus.leValue f.mem 8 8 = some 2 := by
  have G := Ex.certified
  rw [← Ex.prog_init] at G
  obtain ⟨C, -, -, hm, hs', hI', q, -, l1, -⟩ :=
    drf_behav (P := Ex.prog) (by decide) (by decide) G hf
  have h0 := q 0 (by decide)
  have h1 := q 1 (by decide)
  simp only [Ex.post] at h0 h1
  have m0 := l1 0 0 1 (by rw [h0]; simp [Heap.single])
  have m1 := l1 1 8 2 (by rw [h1]; simp [Heap.single])
  refine ⟨?_, ?_⟩
  · rw [hm ⟨"a", 0, 8, 0⟩ (by simp [Ex.prog])]; exact m0
  · rw [hm ⟨"b", 8, 8, 0⟩ (by simp [Ex.prog])]; exact m1

/-- **`Ex.xl_behav` is not vacuous**: `Ex.prog` has an axiomatic XL behaviour, and
every one of its XL behaviours holds the owned values. The enumerator finds an SC execution of
the example (`ExBehav.exAll_check`), and independently forbids an unwritten owned cell and a
lost counter increment under every model over the test's domain (`ExBehav.exLost_check`,
`ExBehav.exCtr_check`), agreeing with the bridge. -/
theorem Ex.xl_behav_some : ∃ f, Silmaril.X86.Concurrency.Cir.Behav Ex.prog
      Silmaril.X86.MemoryModel.Axiomatic.Exec.Xl f ∧
    Silmaril.X86.MemoryModel.Litmus.leValue f.mem 0 8 = some 1 ∧
      Silmaril.X86.MemoryModel.Litmus.leValue f.mem 8 8 = some 2 := by
  obtain ⟨f, hf⟩ := Silmaril.Proofs.X86.Concurrency.Cir.Csl.ExBehav.some_sc
  have hx := Silmaril.X86.Concurrency.Cir.behav_mono Silmaril.X86.Concurrency.Cir.sc_le_xl hf
  exact ⟨f, hx, Ex.xl_behav hx⟩

/-- **The buffered machines are weak**: TSO reaches `SB`'s both-zero outcome, drained. -/
theorem Ex.sb_weak : ∃ C : OCfg, OReach .tso 2 Ex.sbStart.toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ (C.ts 0).2 .rbx = 0 ∧ (C.ts 1).2 .rbx = 0 ∧
    C.mem 0 = some 1 ∧ C.mem 8 = some 1 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex.sb_weak

/-- **…and SC is not**: the CIR-native SC machine never finishes `SB` with both loads
`0`. With `Ex.sb_weak`, the buffered machines are strictly weaker than SC on CIR, so `drf_sc`
is not an identity. -/
theorem Ex.sb_sc : ¬ ∃ C : Cfg, ScReach 2 Ex.sbStart C ∧ C.Done 2 ∧ (C.ts 0).2 .rbx = 0 ∧
    (C.ts 1).2 .rbx = 0 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex.Sb.sb_sc

end Silmaril.X86.Concurrency.Cir.Csl
