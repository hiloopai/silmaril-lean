module

public import Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Run
public import Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Ax
public import Silmaril.X86.MemoryModel.OpAx.Thms

/-!
# Recorded pool runs: per-thread runs, and the composition with the litmus bridge

* `runA_chain`: each thread's history in a recorded run is a run of that thread (`Chain`),
  from its initial core to its current core, each step an `Atomic9.step` on the thread's view
  with `StepActs` actions.
* `poolProg_eq`, `threadsOk_poolProg`, `tracesOk_pool`: the store-buffer program of a recorded run
  is
  `traceX` of the threads' traces, its events name their threads, and the traces' actions are
  `ActOk` (from `Shape`).
* `explains_of_runA` (pieces (4) + (5) of `Task.tsoRunCir`'s plan): with `ThreadCells`, a
  drained recorded run is explained by a TSO candidate with paired `rmw`s
  (`run_explains_tso_paired`);
* `axReach_of_runA` (pieces (4) + (5) + (6)): its final state is then an `AxReach` final state
  of any test whose trace sets contain the threads' traces, for the run's registers, when no
  unit tears and the test's initial memory agrees with the run's on the bytes read.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun

open Silmaril.X86 (State)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (SeqStep Act)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Test actX traceX AxReach finalOf)
open Silmaril.X86.MemoryModel.Tso (XEvent)
open Silmaril.X86.Pool (TPool TsoFlush overlay atomic9Ev Drained)
open Silmaril.X86.Concurrency.Bridge.PoolRun

/-! ## Per-thread runs -/

theorem Chain.snoc {c c₁ : State} {os : List Obs} {o : Obs} (h : Chain c os c₁) (hpre : o.pre = c₁)
    (hs : Atomic9.step ⟨c₁, o.q.pre⟩ = some ⟨o.q.post, o.q.mem⟩)
    (ha : ∃ i n, MemEvent.atomic9Fetch o.q.pre c₁.rip.toNat = some (i, n) ∧
      StepActs o.acts i c₁ n o.q) : Chain c (os ++ [o]) o.q.post := by
  induction h with
  | nil c => exact .cons hpre hs ha (.nil _)
  | cons hpre' hs' ha' _ ih => exact .cons hpre' hs' ha' (ih hpre hs ha)

theorem a9step_of {c c' : State} {m m' : Memory} {i : Atomic9.Instr} {n : Nat}
    (hf : atomic9Ev.fetch m c.rip.toNat = some (i, n)) (hx : atomic9Ev.exec i c m n = .ok c' m') :
    Atomic9.step ⟨c, m⟩ = some ⟨c', m'⟩ := by
  rw [← Silmaril.X86.Pool.atomic9Ev_step, Silmaril.X86.Pool.EvMachine.step, hf]
  show Silmaril.X86.Open.ofResult (atomic9Ev.exec i c m n) = _
  rw [hx]; rfl

theorem stepA_chain {Fin : Nat → State → Prop} {p : TPool Nat} {t : Nat} {o : Obs}
    {p' : TPool Nat} (h : StepA Fin p t o p') :
    ∃ c, p.threads t = some c ∧ o.pre = c ∧ p'.threads t = some o.q.post ∧
      Atomic9.step ⟨c, o.q.pre⟩ = some ⟨o.q.post, o.q.mem⟩ ∧
      ∃ i n, MemEvent.atomic9Fetch o.q.pre c.rip.toNat = some (i, n) ∧
        StepActs o.acts i c n o.q := by
  cases h with
  | @sync c c' i n mem' acts ht hnf hf hs he hx ha =>
    rw [he] at hf
    exact ⟨c, ht, rfl, by simp, a9step_of hf hx, i, n, hf, ha⟩
  | @buffered c c' i n view' acts ht hnf hf hs hx ha =>
    exact ⟨c, ht, rfl, by simp, a9step_of hf hx, i, n, hf, ha⟩

/-- **Each thread's history is a run of the thread**, from its initial core to its current
core. -/
theorem runA_chain {Fin : Nat → State → Prop} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) (t : Nat) :
    (∀ c₀, p₀.threads t = some c₀ → ∃ c, p.threads t = some c ∧ Chain c₀ (H t) c) ∧
      (p₀.threads t = none → p.threads t = none ∧ H t = []) := by
  induction h with
  | refl => exact ⟨fun c₀ h => ⟨c₀, h, .nil _⟩, fun h => ⟨h, rfl⟩⟩
  | @step H p₁ t' o p₂ _ hs ih =>
    obtain ⟨c, hc, hpre, hpost, hst, ha⟩ := stepA_chain hs
    have hoth := (stepA_threads hs).2
    by_cases htt : t = t'
    · subst htt
      refine ⟨fun c₀ h0 => ?_, fun h0 => ?_⟩
      · obtain ⟨c₁, hc₁, hch⟩ := ih.1 c₀ h0
        rw [hc] at hc₁; cases hc₁
        refine ⟨o.q.post, hpost, ?_⟩
        rw [Function.update_self]
        exact Chain.snoc hch hpre hst (hpre ▸ ha)
      · rw [(ih.2 h0).1] at hc; cases hc
    · rw [Function.update_of_ne htt, hoth t htt]
      exact ih
  | @flush H p₁ p₂ _ hf ih =>
    rw [tsoFlush_threads hf]; exact ih

theorem runA_shape {Fin : Nat → State → Prop} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) : ∀ t, ∀ o ∈ H t, Shape o.acts := by
  induction h with
  | refl => intro t o ho; cases ho
  | @step H p₁ t' o' p₂ _ hs ih =>
    intro t o ho
    by_cases htt : t = t'
    · subst htt
      rw [Function.update_self, List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | rfl
      · exact ih t o ho
      · obtain ⟨-, -, -, -, -, -, -, -, hsh, -⟩ := stepA_chain hs
        exact hsh
    · rw [Function.update_of_ne htt] at ho; exact ih t o ho
  | flush _ _ ih => exact ih

/-! ## The program and the traces -/

theorem shape_actOk {acts : List XAct} (h : Shape acts) : ∀ a ∈ acts, ActOk a := by
  rcases h with hf | ⟨a, rfl, hnf, hl, hst, hpos, hrd, hwr⟩
  · intro a ha
    obtain ⟨⟨k, hk⟩, -, -⟩ := hf a ha
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hk, MemEvent.Kind.reads, MemEvent.Kind.writes]
  · intro b hb
    rw [List.mem_singleton] at hb; subst hb
    exact ⟨hl, hst, hrd, hwr, fun _ => hpos⟩

theorem traceX_trace (k : Nat) (os : List Obs) (fin : State) :
    traceX k (Obs.trace os fin) = histX k os := by
  simp [traceX, Obs.trace, histX, Silmaril.X86.Litmus.Trace.acts, List.flatMap_map]

theorem poolProg_eq (N : Nat) (H : Nat → List Obs) (fin : Nat → State) :
    poolProg N H = (poolTraces N H fin).mapIdx traceX := by
  apply List.ext_getElem (by simp [poolProg, poolTraces])
  intro i h1 h2
  simp only [poolProg, poolTraces, List.getElem_mapIdx, List.getElem_map, List.getElem_range,
    traceX_trace]

theorem threadsOk_poolProg (N : Nat) (H : Nat → List Obs) :
    Silmaril.X86.MemoryModel.OpAx.ThreadsOk (poolProg N H) := by
  intro i es hi ev hev
  simp only [poolProg, List.getElem?_map] at hi
  rcases Nat.lt_or_ge i N with hiN | hiN
  · rw [List.getElem?_range hiN] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    subst hi
    simp only [histX, List.mem_flatMap] at hev
    obtain ⟨a, -, hev⟩ := hev
    simp only [actX] at hev
    split at hev
    · simp at hev; subst hev; rfl
    · simp at hev; subst hev; rfl
    · split at hev
      · simp at hev; subst hev; rfl
      · simp at hev; rcases hev with rfl | rfl <;> rfl
    · split at hev
      · simp at hev; subst hev; rfl
      · simp at hev
  · rw [List.getElem?_eq_none (by simpa using hiN)] at hi; cases hi

theorem tracesOk_pool {Fin : Nat → State → Prop} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) (N : Nat) (fin : Nat → State) :
    TracesOk (poolTraces N H fin) := by
  intro tr htr a ha
  simp only [poolTraces, List.mem_map, List.mem_range] at htr
  obtain ⟨k, -, rfl⟩ := htr
  simp only [Obs.trace, Silmaril.X86.Litmus.Trace.acts, List.flatMap_map,
    List.mem_flatMap] at ha
  obtain ⟨o, ho, ha⟩ := ha
  exact shape_actOk (runA_shape h k o ho) a ha

/-! ## Composition -/

/-- **(4) + (5)**: a drained recorded run whose threads have cells is explained by an x86-TSO
candidate over the store-buffer machine units of its program, with paired locked read-modify-writes.
-/
theorem explains_of_runA {Fin : Nat → State → Prop} {N : Nat} {p₀ : TPool Nat}
    {H : Nat → List Obs} {p : TPool Nat} (h : RunA Fin p₀ H p) (hb : ∀ t, p₀.buffer t = [])
    (hN : ∀ t, N ≤ t → p₀.threads t = none) (hd : Drained p)
    (hC : Silmaril.X86.MemoryModel.OpAx.ThreadCells (poolProg N H)) :
    ∃ x, Silmaril.X86.MemoryModel.OpAx.Explains Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso
      (poolProg N H) (fun a => p₀.memory.bytes[a]?) p.toX x ∧
      Silmaril.X86.MemoryModel.OpAx.RmwPaired x :=
  Silmaril.X86.MemoryModel.OpAx.run_explains_tso_paired (threadsOk_poolProg N H) hC
    (opRun_of_runA h hb hN hd)

/-- **(4) + (5) + (6)**: the final memory of a drained recorded run is, on every byte some
access writes or whose initial value the run and the test share, the memory of an `AxReach`
final state (x86-TSO) of a test whose trace sets contain the threads' traces. -/
theorem axReach_of_runA {Fin : Nat → State → Prop} {N : Nat} {p₀ : TPool Nat}
    {H : Nat → List Obs} {p : TPool Nat} (h : RunA Fin p₀ H p) (hb : ∀ t, p₀.buffer t = [])
    (hN : ∀ t, N ≤ t → p₀.threads t = none) (hd : Drained p)
    (hC : Silmaril.X86.MemoryModel.OpAx.ThreadCells (poolProg N H)) (fin : Nat → State)
    {t : Test} {T : List (List XTrace)} (hT : List.Forall₂ (· ∈ ·) (poolTraces N H fin) T)
    (hnt : NoTear (poolTraces N H fin))
    (hI : InitReads t (fun a => p₀.memory.bytes[a]?) (poolTraces N H fin)) :
    ∃ m, AxReach t T Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso (finalOf (poolTraces N H fin) m) ∧
      ∀ y, m y = p.memory.bytes[y]? ∨
        (m y = t.initMem y ∧ p.memory.bytes[y]? = p₀.memory.bytes[y]?) := by
  obtain ⟨x, hx, hp⟩ := explains_of_runA h hb hN hd hC
  rw [poolProg_eq N H fin] at hx
  obtain ⟨m, hm, hy⟩ := axReach_of_explains hT (tracesOk_pool h N fin) hnt hI hx hp
  refine ⟨m, hm, fun y => ?_⟩
  have := hy y
  simpa [Silmaril.X86.Pool.TPool.toX] using this

end Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun
