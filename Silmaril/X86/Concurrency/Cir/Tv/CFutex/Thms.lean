module

public import Silmaril.X86.Concurrency.Cir.Tv.CFutex.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Sys.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex
import Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover
import Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexMutex

/-!
# Futex C litmus tests: what is proved

The per-test kernel checks are in
`Silmaril/Proofs/X86/Concurrency/Cir/TvCFutex.lean` (generated). For each program and each
compiler (gcc 13.3, clang 23.1.3):

* **Event flag** (`Flag`): `allOk`. For the compiled x86 code, under SC, TSO and XL, in every
  bounded behaviour (each thread within 60 instructions and one futex wait), **if the waiter
  finished it read the published data (`r0 = 1`), and if it blocked for ever, a wake came after
  its enqueue (queue byte `0`): no lost wake-up** (`flag_x86`). The same holds for the CIR
  program with blocking (`flag_cir`).
* **Event flag with the wake first** (`Flag-late`): `allOk` with an `allowed` verdict: the CIR
  program has a behaviour, already under SC, in which the waiter blocks for ever with no wake
  after its enqueue (`flagLate_lost`). The checker finds the lost wake-up.
* **Drepper's mutex** (`Mutex`): `tvOk`, so every bounded x86 behaviour is a CIR behaviour with
  the same memory (`mutex_refines`). The CIR verdict "`c = 2` in every XL behaviour" is
  `Task.mutexXl`, PROVED (`mutexXl`) without enumerating the about 44 000 trace
  combinations: a direct `ghbXl` argument over any candidate, plus one kernel `decide` per
  thread over its own 210 runs (`Silmaril/Proofs/X86/Concurrency/Cir/TvCFutexMutex.lean`). So
  the verdict holds for the x86 code under SC, TSO and XL (`mutex_x86`, unconditional).
* **Racy mutex** (`Mutex-racy`): `tvOk`, and one SC execution named by a trace per thread and a
  schedule (`schedOk`): the lost increment `c = 1` is a CIR behaviour under SC, TSO and XL
  (`mutexRacy_lost`).

`forbidden` verdicts transfer to x86 through `tvOk` (x86 traces ⊆ CIR traces). The converse check
`coverOk` (CIR traces ⊆ x86 traces, per thread, up to `normActs`)
passes for all 8 tests, so the bounded x86 behaviours *are* the CIR behaviours up to
registers. From it: the two bugs are x86 behaviours too (`flagLate_lost_x86`,
`mutexRacy_lost_x86`), and the x86 behaviour sets are not empty (`flag_x86_some`), so
`flag_x86` is not vacuous (an exploration budget too small to finish a thread gives no x86
traces and passes `tvOk`, but fails `coverOk`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv.CFutex

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus (Model Final Verdict Cond Atom)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- A `forbidden` verdict of a `forall` test: every behaviour satisfies the condition. -/
theorem forall_of_forbidden {t : Silmaril.X86.MemoryModel.Litmus.Test} (hq : t.quant = .forall_)
    {R : Final → Prop} (h : Verdict.forbidden.Holds t R) : ∀ f, R f → t.cond.eval f = true := by
  intro f hf
  cases hc : t.cond.eval f
  · exact (h ⟨f, hf, by simp [Silmaril.X86.MemoryModel.Litmus.Test.witness, hq, Cond.eval, hc]⟩).elim
  · rfl

/-- The event-flag tests pass every check. -/
theorem flag_ok : «Flag@gcc».allOk = true ∧ «Flag@clang».allOk = true :=
  ⟨Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Flag@gcc_ok»,
    Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Flag@clang_ok»⟩

/-- **The event flag, for the compiled code** (gcc and clang), under SC, TSO and XL: in every
bounded x86 behaviour, `done = 1 ∧ r0 = 1` or `done = 0 ∧ q = 0` (no lost wake-up). -/
theorem flag_x86 : ∀ c ∈ [«Flag@gcc», «Flag@clang»], ∀ (M : Model) f,
    c.XBehav M.Holds f → c.test.cond.eval f = true := by
  intro c hc M
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have hT : c.Transfer := by
    rcases hc with rfl | rfl
    · exact FTest.transfer_of_allOk flag_ok.1
    · exact FTest.transfer_of_allOk flag_ok.2
  have hv : c.verdict M = .forbidden := by rcases hc with rfl | rfl <;> cases M <;> rfl
  have hq : c.test.quant = .forall_ := by rcases hc with rfl | rfl <;> rfl
  exact forall_of_forbidden hq (hT.x86_forbidden M hv)

/-- **The event flag in CIR**, with blocking, under SC, TSO and XL. -/
theorem flag_cir : ∀ (M : Model) f, BBehavIn (Futex.Progs.flag 1) [0, 1] M.Holds f →
    «Flag@gcc».test.cond.eval f = true := by
  intro M f hf
  have hT := FTest.transfer_of_allOk flag_ok.1
  have hv : «Flag@gcc».verdict M = .forbidden := by cases M <;> rfl
  have := hT.cir M
  rw [hv] at this
  refine forall_of_forbidden rfl this f ?_
  have hok : «Flag@gcc».tvOk = true := by
    have := flag_ok.1; simp only [FTest.allOk, Bool.and_eq_true] at this; exact this.1
  exact (FTest.cbehav_iff hok).mpr hf

/-- **The lost wake-up is found**: with the wake before the flag store, the waiter can block
for ever with no wake after its enqueue (`done = 0 ∧ q = 1`), under SC, TSO and XL. -/
theorem flagLate_lost (M : Model) :
    ∃ f, BBehavIn (Futex.Progs.flagLate 1) [0, 1] M.Holds f ∧ «Flag-late@gcc».test.cond.eval f = true := by
  have h := Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Flag-late@gcc_ok»
  have hT := FTest.transfer_of_allOk h
  have hv : «Flag-late@gcc».verdict M = .allowed := by cases M <;> rfl
  have := hT.cir M
  rw [hv] at this
  obtain ⟨f, hf, hw⟩ := this
  have hok : «Flag-late@gcc».tvOk = true := by
    simp only [FTest.allOk, Bool.and_eq_true] at h; exact h.1
  exact ⟨f, (FTest.cbehav_iff hok).mp hf, hw⟩

/-- **Drepper's mutex: bounded x86 behaviours are CIR behaviours** (gcc and clang). -/
theorem mutex_refines : ∀ c ∈ [«Mutex@gcc», «Mutex@clang»], ∀ (M : Exec → Prop) f,
    c.XBehav M f → ∃ f', BehavIn (Futex.Progs.mutex 1) [0, 1, 2] M f' ∧ f'.mem = f.mem := by
  intro c hc M f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have hok : c.tvOk = true := by
    rcases hc with rfl | rfl
    · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Mutex@gcc_tv»
    · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Mutex@clang_tv»
  obtain ⟨f', hb, hm, -⟩ := FTest.refines hok hf
  have := (FTest.cbehav_iff hok).mp hb
  rcases hc with rfl | rfl <;> exact ⟨f', this, hm⟩

/-- **Mutual exclusion of Drepper's futex mutex, in CIR**: in every XL behaviour of the
two-thread program (one futex wait per thread, values `0`–`2`), the counter is `2`. PROVED as
`mutexXl` by plan (b), a direct argument: order the two acquiring locked writes of
the mutex word in coherence; the second acquire reads, by `rfe`, a `0` that the first thread's
unlock wrote after its counter store (atomicity excludes the initial value, `uniprocXl` the
second thread's own later writes), so the counter accesses are ordered by a `ghbXl` path. -/
def Task.mutexXl : Prop :=
  ∀ f, BehavIn (Futex.Progs.mutex 1) [0, 1, 2] Exec.Xl f →
    (Cond.atom (.mem Futex.Progs.cnt 4 2)).eval f = true

/-- **`Task.mutexXl` holds**. -/
theorem mutexXl : Task.mutexXl :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexMutex.mutex_xl

/-- **Drepper's mutex for the compiled code** (gcc and clang): in every bounded x86 behaviour
under SC, TSO or XL, the counter is `2`. -/
theorem mutex_x86 : ∀ c ∈ [«Mutex@gcc», «Mutex@clang»], ∀ (M : Model) f,
    c.XBehav M.Holds f → c.test.cond.eval f = true := by
  intro c hc M f hf
  have hT : Task.mutexXl := mutexXl
  have hxl : ∀ x, M.Holds x → Exec.Xl x := fun x hx => by
    cases M
    · exact tso_le_xl x (sc_le_tso x hx)
    · exact tso_le_xl x hx
    · exact hx
  obtain ⟨f', hb, hm⟩ := mutex_refines c hc M.Holds f hf
  have h2 := hT f' (Silmaril.X86.MemoryModel.Litmus.axReach_mono hxl hb)
  have hcond : c.test.cond = .atom (.mem Futex.Progs.cnt 4 2) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl
  rw [hcond]
  simpa [Cond.eval, Atom.eval, hm] using h2

/-- **Drepper's mutex has behaviours**: some SC (so TSO and XL)
behaviour of the CIR program exists, and it ends with `c = 2`. So `mutexXl` is not vacuous. -/
theorem mutex_some : ∃ f, BehavIn (Futex.Progs.mutex 1) [0, 1, 2] Exec.Sc f ∧
    (Cond.atom (.mem Futex.Progs.cnt 4 2)).eval f = true := by
  obtain ⟨f, hf, hw⟩ :=
    FTest.sched_allowed Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexMutex.mutexPos_sched .sc
  have hok := Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Mutex@gcc_tv»
  exact ⟨f, (FTest.cbehav_iff hok).mp hf, hw⟩

/-- **The racy mutex loses an increment** (`c = 1`), as a CIR behaviour under SC, TSO and XL. -/
theorem mutexRacy_lost (M : Model) :
    ∃ f, BehavIn (Futex.Progs.mutexRacy 1) [0, 1, 2] M.Holds f ∧
      (Cond.atom (.mem Futex.Progs.cnt 4 1)).eval f = true := by
  have hw := FTest.sched_allowed Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Mutex-racy@gcc_sched» M
  obtain ⟨f, hf, he⟩ := hw
  have hok := Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Mutex-racy@gcc_tv»
  exact ⟨f, (FTest.cbehav_iff hok).mp hf, he⟩

/-! ## The converse check -/

/-- Every test passes the converse trace check. -/
theorem cover_ok : ∀ c ∈ all, c.coverOk = true := by
  intro c hc
  simp only [all, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Flag@gcc_cover»
  · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Flag@clang_cover»
  · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Flag-late@gcc_cover»
  · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Flag-late@clang_cover»
  · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Mutex@gcc_cover»
  · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Mutex@clang_cover»
  · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Mutex-racy@gcc_cover»
  · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Mutex-racy@clang_cover»

/-- **The event flag's x86 behaviours exist** (gcc and clang): `flag_x86` is not vacuous; some
bounded x86 execution is SC, and so TSO and XL. -/
theorem flag_x86_some : ∀ c ∈ [«Flag@gcc», «Flag@clang»], ∀ M : Model, ∃ f, c.XBehav M.Holds f := by
  intro c hc M
  have hcv : c.coverOk = true := cover_ok c (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [all])
  have hT : c.Transfer := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact FTest.transfer_of_allOk flag_ok.1
    · exact FTest.transfer_of_allOk flag_ok.2
  obtain ⟨f, hf⟩ := hT.sc_some
  have hf' : c.CBehav M.Holds f := Silmaril.X86.MemoryModel.Litmus.axReach_mono (fun x hx => by
    cases M
    · exact hx
    · exact sc_le_tso x hx
    · exact tso_le_xl x (sc_le_tso x hx)) hf
  obtain ⟨f', hx, -⟩ := FTest.realizes hcv hf'
  exact ⟨f', hx⟩

/-- **Drepper's mutex has x86 behaviours** (gcc and clang): some bounded
x86 execution is SC, and so TSO and XL. So `mutex_x86` is not vacuous. -/
theorem mutex_x86_some : ∀ c ∈ [«Mutex@gcc», «Mutex@clang»], ∀ M : Model, ∃ f, c.XBehav M.Holds f := by
  intro c hc M
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have hcv : c.coverOk = true := by
    rcases hc with rfl | rfl
    · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Mutex@gcc_cover»
    · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexCover.«Mutex@clang_cover»
  have hok : c.tvOk = true := by
    rcases hc with rfl | rfl
    · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Mutex@gcc_tv»
    · exact Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Mutex@clang_tv»
  have hprog : c.prog = Futex.Progs.mutex 1 ∧ c.dom = [0, 1, 2] ∧ c.blk = false := by
    rcases hc with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨f, hf, -⟩ := mutex_some
  have hf' : BehavIn (Futex.Progs.mutex 1) [0, 1, 2] M.Holds f :=
    Silmaril.X86.MemoryModel.Litmus.axReach_mono (fun x hx => by
      cases M
      · exact hx
      · exact sc_le_tso x hx
      · exact tso_le_xl x (sc_le_tso x hx)) hf
  have hc' : c.CBehav M.Holds f := by
    rw [FTest.cbehav_iff hok, hprog.2.2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hprog.1, hprog.2.1]
    exact hf'
  obtain ⟨f', hx, -⟩ := FTest.realizes hcv hc'
  exact ⟨f', hx⟩

/-- **The lost wake-up is in the compiled code** (gcc and clang): some bounded x86 behaviour of
`Flag-late`, already under SC, has the waiter blocked for ever with no wake after its enqueue
(`done = 0 ∧ q = 1`). -/
theorem flagLate_lost_x86 : ∀ c ∈ [«Flag-late@gcc», «Flag-late@clang»], ∀ M : Model,
    c.test.Allowed (c.XBehav M.Holds) := by
  intro c hc M
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have hcv : c.coverOk = true := cover_ok c (by rcases hc with rfl | rfl <;> simp [all])
  apply FTest.x86_allowed hcv
  have hT : c.Transfer := by
    rcases hc with rfl | rfl
    · exact FTest.transfer_of_allOk Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Flag-late@gcc_ok»
    · exact FTest.transfer_of_allOk Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Flag-late@clang_ok»
  have hv : c.verdict M = .allowed := by rcases hc with rfl | rfl <;> cases M <;> rfl
  have := hT.cir M
  rw [hv] at this
  exact this

/-- **The racy mutex loses an increment in the compiled code** (gcc and clang): some bounded
x86 behaviour, already under SC, ends with `c = 1`. -/
theorem mutexRacy_lost_x86 : ∀ c ∈ [«Mutex-racy@gcc», «Mutex-racy@clang»], ∀ M : Model,
    c.test.Allowed (c.XBehav M.Holds) := by
  intro c hc M
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have hcv : c.coverOk = true := cover_ok c (by rcases hc with rfl | rfl <;> simp [all])
  apply FTest.x86_allowed hcv
  rcases hc with rfl | rfl
  · exact FTest.sched_allowed Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Mutex-racy@gcc_sched» M
  · exact FTest.sched_allowed Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex.«Mutex-racy@clang_sched» M

end Silmaril.X86.Concurrency.Cir.Tv.CFutex
