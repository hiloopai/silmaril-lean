module

public import Silmaril.X86.Concurrency.Cir.Prim.Clients.Defs
public import Silmaril.X86.Concurrency.Cir.Prim.Mutants.Defs
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
public import Silmaril.X86.Concurrency.Cir.Csl.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Checks
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Csl
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Vacuity

/-!
# The synchronisation primitives, proved in CIR

Everything here is PROVED
(standard axioms; the Boolean checks by kernel `decide`).

## Translation validation (the binaries are CIR programs)

* `tv_ok`: the eight pinned gcc `-O2` functions check against their certificates.
* `refines`: for each of them, every x86 run of the bytes (any thread with that code, any start
  core, any read values) is a run of the CIR program, with the same memory actions and final
  registers, for every loop bound at least the run's length (`TvCfg.tvCfg_sound`).
* `mutants_rejected`, `allSc_accepted`: the checker rejects a flipped loop condition, an `xchg`
  replaced by a plain load, a dropped store, a missing end entry and a wrong slot address; it
  accepts the certificate with every mode `sc` (modes are not checked).

## CSL: acquire gives the resource

* `spinLock_acquire`: the CIR program of `spin_lock`, from an empty heap with `rdi` at the lock
  word, is CSL-safe under `lockInv l R` for every loop bound and ends owning `R`. With
  `drf_sc`/`csl_buffered`, this holds on the TSO and XL store-buffer machines for every client
  certified in the logic. (No such client can release the lock, because
  `spin_unlock` is a plain `mov` that the `LabOk` rejects; the transfer is therefore limited to
  clients that never unlock. `Csl.Rel` adds the release rule and proves
  `Task.spinMutexTso` with it, `Prim/Tasks/Thms.lean`.)

## The explorer on closed clients (TSO store buffers, `Csl.OStep .tso`)

Each statement is about every finished, drained configuration the CIR-native TSO machine reaches
from the client's start (`Clients`, loop bound `2`):

* `spin_mutex`, `tick_mutex`: the counter incremented by both critical sections is `2`;
* `spin_robust`, `tick_robust`: the final state is a final state of the SC machine (TSO
  robustness, checked);
* `seq_snapshot`: the seqlock reader returns a consistent snapshot; `seq_robust`;
  `torn_without_protocol`: a reader that skips the sequence check returns a torn snapshot;
* `spsc_fifo`: the SPSC ring returns the pushed values in order and its indices stay in range;
* `spsc_not_robust`: **the SPSC client is not TSO-robust**: a TSO final state (first pop got `1`,
  second pop found the ring empty, third push found it full) is not a final state of any SC run.
  So the ring's correctness on TSO (`spsc_fifo`) is a TSO-specific fact, not an SC fact
  transferred by robustness.

## Non-vacuity

The statements above quantify over finished, drained states within loop bound `2`.
`clients_finish` shows each client has such states with the interesting outcomes (the seqlock
reader returns the new pair and the old pair; the ring pops `1` then `2`), and `tts_loses` shows
that the test-then-set mutant of the spinlock (exchange split into a load and a store) loses an
increment on the same machine, so `spin_mutex` depends on the atomic exchange.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Prim

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.X86.Concurrency.Cir.Csl (OCfg Cfg OReach ScReach HProp Heap)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-! ## Translation validation -/

/-- **The eight certificates check against the pinned bytes.** -/
theorem tv_ok : ∀ p ∈ all, tvCfg (thr p.2.1) p.2.2 = true := by
  intro p hp
  simp only [all, List.mem_cons, List.not_mem_nil, or_false] at hp
  open Silmaril.Proofs.X86.Concurrency.Cir.Prim in
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_spinLock
  · exact tv_spinUnlock
  · exact tv_ticketLock
  · exact tv_ticketUnlock
  · exact tv_seqWrite
  · exact tv_seqRead
  · exact tv_spscPush
  · exact tv_spscPop

/-- **The binaries are their CIR programs**: for each pinned function, every x86 run of its bytes
is a run of its CIR program for every loop bound `L` at least the run's length. -/
theorem refines {name : String} {code : List (BitVec 8)} {c : GCert} (hp : (name, code, c) ∈ all)
    {t : Tv.XThread} (htc : t.code = code) {s0 s : Silmaril.X86.State} (h0 : s0.rip = t.base)
    {acc : List (List XAct)} (hr : XRun t s0 acc s) {L : Nat} (hL : acc.length ≤ L) :
    ∃ σ rs labs, TRun (c.body L) (regsOf s0) labs σ rs ∧ acc.flatten = labs.flatMap Lab.acts ∧
      regsOf s = rs ∧ (s.rip = t.endRip → σ = .skip) := by
  have h := tv_ok _ hp
  rw [tvCfg_code (t' := t) (by simp [thr, htc])] at h
  exact tvCfg_sound h h0 hr hL

/-- **The checker rejects the mutants.** -/
theorem mutants_rejected :
    tvCfg (thr Code.spinLock) Mutants.flipCond = false ∧
    tvCfg (thr Mutants.xchgToMov) SpinLock.cert = false ∧
    tvCfg (thr Code.seqWrite) Mutants.dropStore = false ∧
    tvCfg (thr Code.spinUnlock) Mutants.noEnd = false ∧
    tvCfg (thr Code.spscPush) Mutants.wrongAddr = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Modes are not checked: the all-`sc` certificate is accepted (control). -/
theorem allSc_accepted : tvCfg (thr Code.spinLock) Mutants.allSc = true := by decide +kernel

/-! ## CSL -/

/-- **Acquire gives the invariant's resource** (CSL, every loop bound). -/
theorem spinLock_acquire (l : Nat) (R : HProp) (L : Nat) (rs : Regs) (hl : (rs .rdi).toNat = l) :
    Csl.Safe (lockInv l R) (fun _ h => R h) (SpinLock.cert.body L) rs Heap.empty :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.spinLock_acquire l R L rs hl

/-! ## The clients on TSO -/

/-- A finished, drained configuration of `N` threads. -/
def Final (N : Nat) (C : OCfg) : Prop := C.Drained ∧ ∀ t < N, (C.ts t).1 = .skip

theorem final_of_check {c0 : CSt} {P : CSt → Bool} (h : tsoCheck 2 fuel c0 P = true) {C : OCfg}
    (hr : OReach .tso 2 c0.cfg.toO C) (hf : Final 2 C) : ∃ d, P d = true ∧ d.ocfg = C :=
  tsoCheck_sound h hr hf.1 hf.2

/-- **Mutual exclusion under TSO (spinlock)**: both increments are seen. -/
theorem spin_mutex {C : OCfg} (hr : OReach .tso 2 spinC.cfg.toO C) (hf : Final 2 C) :
    C.mem 0x200 = some 2 := by
  obtain ⟨d, hd, rfl⟩ :=
    final_of_check Silmaril.Proofs.X86.Concurrency.Cir.Prim.spin_count hr hf
  simpa [countIs2, CSt.ocfg] using hd

/-- **Mutual exclusion under TSO (ticket lock).** -/
theorem tick_mutex {C : OCfg} (hr : OReach .tso 2 tickC.cfg.toO C) (hf : Final 2 C) :
    C.mem 0x200 = some 2 := by
  obtain ⟨d, hd, rfl⟩ :=
    final_of_check Silmaril.Proofs.X86.Concurrency.Cir.Prim.tick_count hr hf
  simpa [countIs2, CSt.ocfg] using hd

/-- **The spinlock client is TSO-robust** (final states). -/
theorem spin_robust {C : OCfg} (hr : OReach .tso 2 spinC.cfg.toO C) (hf : Final 2 C) :
    ∃ C' : Cfg, ScReach 2 spinC.cfg C' ∧ C'.ts = C.ts ∧ C'.mem = C.mem :=
  robustB_sound Silmaril.Proofs.X86.Concurrency.Cir.Prim.spin_robust hr hf.1 hf.2

/-- **The ticket-lock client is TSO-robust** (final states). -/
theorem tick_robust {C : OCfg} (hr : OReach .tso 2 tickC.cfg.toO C) (hf : Final 2 C) :
    ∃ C' : Cfg, ScReach 2 tickC.cfg C' ∧ C'.ts = C.ts ∧ C'.mem = C.mem :=
  robustB_sound Silmaril.Proofs.X86.Concurrency.Cir.Prim.tick_robust hr hf.1 hf.2

/-- **The seqlock reader returns a consistent snapshot under TSO.** -/
theorem seq_snapshot {C : OCfg} (hr : OReach .tso 2 seqC.cfg.toO C) (hf : Final 2 C) :
    C.mem 0x200 = C.mem 0x204 := by
  obtain ⟨d, hd, rfl⟩ :=
    final_of_check Silmaril.Proofs.X86.Concurrency.Cir.Prim.seq_snapshot hr hf
  simpa [snapshotOk, CSt.ocfg] using hd

/-- **The seqlock client is TSO-robust** (final states). -/
theorem seq_robust {C : OCfg} (hr : OReach .tso 2 seqC.cfg.toO C) (hf : Final 2 C) :
    ∃ C' : Cfg, ScReach 2 seqC.cfg C' ∧ C'.ts = C.ts ∧ C'.mem = C.mem :=
  robustB_sound Silmaril.Proofs.X86.Concurrency.Cir.Prim.seq_robust hr hf.1 hf.2

/-- **Without the sequence check the snapshot tears** (non-vacuity of `seq_snapshot`). -/
theorem torn_without_protocol :
    ∃ C : OCfg, OReach .tso 2 tornC.cfg.toO C ∧ Final 2 C ∧ C.mem 0x200 ≠ C.mem 0x204 := by
  obtain ⟨d, hr, hd, hfin, hP⟩ := witness_of_any
    (by decide) (by decide) Silmaril.Proofs.X86.Concurrency.Cir.Prim.torn_witness
  refine ⟨d.ocfg, hr, ⟨hd, hfin⟩, ?_⟩
  simpa [snapshotOk, CSt.ocfg] using hP

/-- **FIFO under TSO**: the SPSC ring's successful pops return the first pushed values in order,
`head` counts them, and `head ≤ tail ≤ head + 2`. -/
theorem spsc_fifo {C : OCfg} (hr : OReach .tso 2 spscC.cfg.toO C) (hf : Final 2 C) :
    ∃ d : CSt, fifoOk d = true ∧ d.ocfg = C :=
  final_of_check Silmaril.Proofs.X86.Concurrency.Cir.Prim.spsc_fifo hr hf

/-- The store-buffering outcome of the SPSC client, on registers and memory. -/
def SbOut (C : OCfg) : Prop :=
  ((C.ts 0).2 .rax).toNat = 0 ∧ ((C.ts 1).2 .rax).toNat = 0 ∧ C.mem 0x200 = some 1

/-- **The SPSC client is not TSO-robust**: TSO reaches a finished, drained state with the
store-buffering outcome, and no finished SC state has it. -/
theorem spsc_not_robust :
    (∃ C : OCfg, OReach .tso 2 spscC.cfg.toO C ∧ Final 2 C ∧ SbOut C) ∧
    ∀ C' : Cfg, ScReach 2 spscC.cfg C' → (∀ t < 2, (C'.ts t).1 = .skip) →
      ¬ (((C'.ts 0).2 .rax).toNat = 0 ∧ ((C'.ts 1).2 .rax).toNat = 0 ∧ C'.mem 0x200 = some 1) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨d, hr, hd, hfin, hP⟩ := witness_of_any
      (by decide) (by decide) Silmaril.Proofs.X86.Concurrency.Cir.Prim.spsc_witness
    refine ⟨d.ocfg, hr, ⟨hd, hfin⟩, ?_⟩
    simp only [sbOutcome, Bool.and_eq_true, beq_iff_eq] at hP
    exact ⟨hP.1.1, hP.1.2, hP.2⟩
  · intro C' hr hfin hsb
    obtain ⟨d, hd, rfl⟩ := scCheck_sound Silmaril.Proofs.X86.Concurrency.Cir.Prim.spsc_sc hr hfin
    simp only [sbOutcome, CSt.cfg] at hd hsb
    simp_all

/-! ## Non-vacuity -/

theorem fin_of_any {c0 : CSt} {P : CSt → Bool} (hb : c0.buf.length = 2)
    (he : c0.buf.all List.isEmpty = true)
    (h : ((tsoStates 2 fuel c0).any fun c => c.doneB 2 && c.drainedB && P c) = true) :
    ∃ C : OCfg, OReach .tso 2 c0.cfg.toO C ∧ Final 2 C ∧ ∃ d : CSt, d.ocfg = C ∧ P d = true := by
  obtain ⟨d, hr, hd, hfin, hP⟩ := witness_of_any hb he h
  exact ⟨d.ocfg, hr, ⟨hd, hfin⟩, d, rfl, hP⟩

/-- **The client statements are not vacuous**: every client has finished, drained TSO states;
the seqlock reader can return both the written pair `(1, 1)` and the initial `(0, 0)`; the ring
can pop `1` and then `2`. -/
theorem clients_finish :
    (∃ C : OCfg, OReach .tso 2 spinC.cfg.toO C ∧ Final 2 C) ∧
    (∃ C : OCfg, OReach .tso 2 tickC.cfg.toO C ∧ Final 2 C) ∧
    (∃ C : OCfg, OReach .tso 2 seqC.cfg.toO C ∧ Final 2 C ∧
      C.mem 0x200 = some 1 ∧ C.mem 0x204 = some 1) ∧
    (∃ C : OCfg, OReach .tso 2 seqC.cfg.toO C ∧ Final 2 C ∧
      C.mem 0x200 = some 0 ∧ C.mem 0x204 = some 0) ∧
    (∃ C : OCfg, OReach .tso 2 spscC.cfg.toO C ∧ Final 2 C ∧
      C.mem 0x200 = some 1 ∧ C.mem 0x204 = some 2) := by
  open Silmaril.Proofs.X86.Concurrency.Cir.Prim in
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨C, hr, hf, -⟩ := fin_of_any (c0 := spinC) (by decide) (by decide) spin_fin
    exact ⟨C, hr, hf⟩
  · obtain ⟨C, hr, hf, -⟩ := fin_of_any (c0 := tickC) (by decide) (by decide) tick_fin
    exact ⟨C, hr, hf⟩
  · obtain ⟨C, hr, hf, d, rfl, hP⟩ := fin_of_any (c0 := seqC) (by decide) (by decide) seq_fin_new
    simp only [Bool.and_eq_true, beq_iff_eq] at hP
    exact ⟨_, hr, hf, hP.1, hP.2⟩
  · obtain ⟨C, hr, hf, d, rfl, hP⟩ := fin_of_any (c0 := seqC) (by decide) (by decide) seq_fin_old
    simp only [Bool.and_eq_true, beq_iff_eq] at hP
    exact ⟨_, hr, hf, hP.1, hP.2⟩
  · obtain ⟨C, hr, hf, d, rfl, hP⟩ := fin_of_any (c0 := spscC) (by decide) (by decide) spsc_fin_both
    simp only [Bool.and_eq_true, beq_iff_eq] at hP
    exact ⟨_, hr, hf, hP.1, hP.2⟩

/-- **The test-then-set mutant loses an increment on TSO**: with the exchange split into a load
and a store, a finished, drained state has the counter `1`. So `spin_mutex` is not vacuous. -/
theorem tts_loses :
    ∃ C : OCfg, OReach .tso 2 Mutants.ttsC.cfg.toO C ∧ Final 2 C ∧ C.mem 0x200 = some 1 := by
  obtain ⟨C, hr, hf, d, rfl, hP⟩ := fin_of_any (c0 := Mutants.ttsC) (by decide) (by decide)
    Silmaril.Proofs.X86.Concurrency.Cir.Prim.tts_lost
  simp only [beq_iff_eq] at hP
  exact ⟨_, hr, hf, hP⟩

/-- **Step-by-step refinement**: as `refines`, with each x86 step's actions those of
at most one CIR label (`TvCfg.tvCfg_steps`). -/
theorem refines_steps {name : String} {code : List (BitVec 8)} {c : GCert}
    (hp : (name, code, c) ∈ all) {t : Tv.XThread} (htc : t.code = code) {s0 s : Silmaril.X86.State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : XRun t s0 acc s) {L : Nat}
    (hL : acc.length ≤ L) :
    ∃ σ rs, ∃ los : List (Option Lab), TRun (c.body L) (regsOf s0) (los.filterMap id) σ rs ∧
      List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
      regsOf s = rs ∧ (s.rip = t.endRip → σ = .skip) := by
  have h := tv_ok _ hp
  rw [tvCfg_code (t' := t) (by simp [thr, htc])] at h
  exact tvCfg_steps h h0 hr hL

end Silmaril.X86.Concurrency.Cir.Prim
