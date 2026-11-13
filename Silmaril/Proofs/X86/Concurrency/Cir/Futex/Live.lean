module

public import Silmaril.X86.Concurrency.Cir.Futex.Live.Defs

/-!
# Futex liveness under fairness: the proof

`flag_live n`: in
every weakly fair run of the event flag `Futex.Progs.flag n` on the SC futex machine
(`Futex.Live.FStep`), the waiter reaches a state where it is awake and cannot step. This
discharges `Futex.Live.Task.flagLive n` for every `n`.

* **Measure** (`msr`): every thread step strictly decreases `msr` of the stepping thread's
  statement (`msr_lt`), and no step changes another thread's statement (`ts_other`); a
  spurious wake-up keeps it. So along a run, `msr` of each thread is non-increasing, and
  strictly decreases at each step of that thread while it is awake.
* **Descent** (`not_always_enabled`): a thread enabled from some point on would, by weak
  fairness, step infinitely often, each time decreasing its measure. So no thread is enabled
  for ever.
* **Invariant** (`Inv`): the setter (thread `0`) is at one of its six positions (`t0s`), never
  sleeps, and once it has stored the flag the flag is `1`; once it has finished, the waiter is
  awake. The waiter's statement only writes cells other than the flag and waits only on the
  flag expecting `0` (`wOk`), so it cannot go to sleep once the flag is `1` (the kernel's
  check, the SC form of `Exec.futex_dekker_xl`), and the setter's wake clears its sleep.
* **Non-vacuity** (`NonVacuous.flag_fair_run`): an explicit run (the setter runs to the end,
  then the waiter reads `1`, skips its loop and finishes, then nothing moves) is maximal and
  weakly fair (`run_fair_of`: a run that stays at a configuration where nothing can step is
  fair). So the hypotheses of `flag_live` are satisfiable.
* **Argument** (`flag_live`): the setter is enabled until it finishes, so it finishes; from
  then on the waiter is awake for ever; were it also able to step for ever, it would be
  enabled for ever.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.FutexLive

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Futex.Live
open Silmaril.X86.Concurrency.Cir.Futex.Progs

/-! ## The measure -/

/-- A measure that every thread step decreases. -/
def msr : Stmt → Nat
  | .skip => 0
  | .seq s t => msr s + msr t + 1
  | .ite _ s t => msr s + msr t + 1
  | .loop n _ b => n * (msr b + 3) + 1
  | _ => 1

theorem msr_lt {s : Stmt} {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep s rs l s' rs') : msr s' < msr s := by
  induction h with
  | loopT => simp only [msr, Nat.succ_mul]; omega
  | seq _ ih => simp only [msr]; omega
  | _ => simp only [msr]; omega

/-! ## The waiter's statements -/

/-- The waiter's statements: plain loads and fences, stores to cells other than the flag, and
waits on the flag expecting `0`. -/
def wOk : Stmt → Bool
  | .skip | .assign .. | .load .. | .fence _ => true
  | .store _ _ _ (.lit a) _ => decide (a < 2 ^ 64) && a != flagW
  | .futexWait _ (.lit a) (.lit v) => a == flagW && v == 0
  | .seq s t | .ite _ s t => wOk s && wOk t
  | .loop _ _ b => wOk b
  | _ => false

/-- The waiter's labels: no futex call and no write of the flag, or a wait on the flag
expecting `0`. -/
def LabOk (l : Lab) : Prop :=
  (l.isFutex = false ∧ l.wval flagW = none) ∨ ∃ s r, l = .fwait flagW 0 s r

theorem tstep_wOk {s : Stmt} {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep s rs l s' rs') (hw : wOk s = true) : wOk s' = true ∧ ∀ lab, l = some lab → LabOk lab := by
  induction h with
  | assign => simp [wOk]
  | load => simp [wOk, LabOk, Lab.isFutex, Lab.wval]
  | store =>
    rename_i a v rs
    cases a <;> simp only [wOk, reduceCtorEq] at hw
    rename_i a0
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hw
    refine ⟨by simp [wOk], ?_⟩
    rintro lab ⟨⟩
    left
    simp only [Lab.isFutex, Lab.wval, Expr.eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw.1, true_and]
    simp [hw.2]
  | rmw => simp [wOk] at hw
  | fence => simp [wOk, LabOk, Lab.isFutex, Lab.wval]
  | fwait =>
    rename_i a v rs seen r _ _
    cases a <;> cases v <;> simp only [wOk, reduceCtorEq] at hw
    rename_i a0 v0
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨by simp [wOk], ?_⟩
    rintro lab ⟨⟩
    right
    exact ⟨seen, r, by simp [Expr.eval, flagW]⟩
  | fwake => simp [wOk] at hw
  | spawn => simp [wOk] at hw
  | join => simp [wOk] at hw
  | blk => simp [wOk] at hw
  | seq _ ih =>
    simp only [wOk, Bool.and_eq_true] at hw ⊢
    obtain ⟨h1, h2⟩ := ih hw.1
    exact ⟨⟨h1, hw.2⟩, h2⟩
  | seqSkip => simp only [wOk, Bool.and_eq_true] at hw; exact ⟨hw.2, by simp⟩
  | iteT => simp only [wOk, Bool.and_eq_true] at hw; exact ⟨hw.1, by simp⟩
  | iteF => simp only [wOk, Bool.and_eq_true] at hw; exact ⟨hw.2, by simp⟩
  | loopT => simp only [wOk, Bool.and_eq_true] at hw ⊢; exact ⟨⟨hw, hw⟩, by simp⟩
  | loopF => simp [wOk]

/-! ## The setter's statements -/

/-- `data = 1`. -/
def stA : Stmt := .store .na 4 .wb (.lit data) (.lit 1)

/-- `flag :=rel 1`. -/
def stB : Stmt := .store .rel 4 .wb (.lit flagW) (.lit 1)

/-- `wake(flag, 1)`. -/
def wk : Stmt := .futexWake (.lit flagW) (.lit 1)

/-- The setter's six positions. -/
def t0s : Nat → Stmt
  | 0 => .seq stA (.seq stB wk)
  | 1 => .seq .skip (.seq stB wk)
  | 2 => .seq stB wk
  | 3 => .seq .skip wk
  | 4 => wk
  | _ => .skip

/-- The label of the setter's step from each position. -/
def t0ok : Nat → Option Lab → Prop
  | 0, l => ∃ v, l = some (.wr .na .wb data 4 v)
  | 1, l => l = none
  | 2, l => l = some (.wr .rel .wb flagW 4 1)
  | 3, l => l = none
  | 4, l => ∃ q, l = some (.fwake flagW 1 q)
  | _, _ => False

theorem t0_step {k : Nat} {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep (t0s k) rs l s' rs') : s' = t0s (k + 1) ∧ t0ok k l := by
  match k, h with
  | 0, h =>
    simp only [t0s, stA, stB, wk] at h
    cases h with
    | seq h =>
      cases h
      exact ⟨rfl, _, by rw [show (Expr.eval rs (Expr.lit data)).toNat = data by simp [Expr.eval, data]]⟩
  | 1, h =>
    simp only [t0s, stB, wk] at h
    cases h with
    | seq h => cases h
    | seqSkip => exact ⟨rfl, rfl⟩
  | 2, h =>
    simp only [t0s, stB, wk] at h
    cases h with
    | seq h => cases h; exact ⟨rfl, by simp [t0ok, Expr.eval, flagW]⟩
  | 3, h =>
    simp only [t0s, wk] at h
    cases h with
    | seq h => cases h
    | seqSkip => exact ⟨rfl, rfl⟩
  | 4, h =>
    simp only [t0s, wk] at h
    cases h
    exact ⟨rfl, _, by
      rw [show (Expr.eval rs (Expr.lit flagW)).toNat = flagW by simp [Expr.eval, flagW],
        show (Expr.eval rs (Expr.lit 1)).toNat = 1 by simp [Expr.eval]]⟩
  | k + 5, h => simp only [t0s] at h; cases h

theorem t0ok_none {k : Nat} (h : t0ok k none) : k = 1 ∨ k = 3 := by
  match k, h with
  | 0, ⟨_, h⟩ => cases h
  | 1, _ => exact Or.inl rfl
  | 2, h => cases h
  | 3, _ => exact Or.inr rfl
  | 4, ⟨_, h⟩ => cases h
  | _ + 5, h => exact h.elim

theorem t0ok_some {k : Nat} {l : Lab} (h : t0ok k (some l)) :
    (k = 0 ∧ ∃ v, l = .wr .na .wb data 4 v) ∨ (k = 2 ∧ l = .wr .rel .wb flagW 4 1) ∨
      (k = 4 ∧ ∃ q, l = .fwake flagW 1 q) := by
  match k, h with
  | 0, ⟨v, h⟩ => exact Or.inl ⟨rfl, v, Option.some.inj h⟩
  | 1, h => cases h
  | 2, h => exact Or.inr (Or.inl ⟨rfl, Option.some.inj h⟩)
  | 3, h => cases h
  | 4, ⟨q, h⟩ => exact Or.inr (Or.inr ⟨rfl, q, Option.some.inj h⟩)
  | _ + 5, h => exact h.elim

theorem t0s_skip {k : Nat} (hk : k ≤ 5) (h : t0s k = .skip) : k = 5 := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [t0s, wk] at h
  | 5, _ => rfl

/-! ## The invariant -/

/-- **The invariant** of the event flag's runs. -/
def Inv (C : FCfg) : Prop :=
  (∃ k ≤ 5, (C.cfg.ts 0).1 = t0s k ∧ (3 ≤ k → C.cfg.mem flagW = some 1) ∧
    (k = 5 → C.sleep 1 = none)) ∧
  C.sleep 0 = none ∧ (C.sleep 1 = none ∨ C.sleep 1 = some flagW) ∧ wOk (C.cfg.ts 1).1 = true ∧
  (C.cfg.mem data).isSome ∧ (C.cfg.mem flagW).isSome

theorem upd_ne {α : Type} (f : Nat → α) {t u : Nat} (x : α) (h : u ≠ t) : upd f t x u = f u := by
  simp [upd, h]

theorem upd_eq {α : Type} (f : Nat → α) (t : Nat) (x : α) : upd f t x t = x := by
  simp [upd]

theorem isSome_updH {H : Csl.Heap} (l : Lab) {a : Nat} (h : (H a).isSome) : (l.updH H a).isSome := by
  simp only [Lab.updH]
  cases l.wval a <;> simp [h]

theorem updH_of_none {H : Csl.Heap} {l : Lab} {a : Nat} (h : l.wval a = none) : l.updH H a = H a := by
  simp [Lab.updH, h]

theorem inv_init (n : Nat) : Inv (finit (Silmaril.X86.Concurrency.Cir.Futex.Progs.flag n)) := by
  refine ⟨⟨0, by omega, rfl, by omega, by omega⟩, rfl, Or.inl rfl, ?_, rfl, rfl⟩
  simp [finit, progInit, Silmaril.X86.Concurrency.Cir.Futex.Progs.flag, waiter, th, Stmt.block, wOk, ld,
    st, eq, r0, done, flagW]

theorem inv_step {C C' : FCfg} {t : Nat} (h : FStep 2 C t C') (hI : Inv C) : Inv C' := by
  obtain ⟨⟨k, hk, h0, hfl, hfin⟩, hs0, hs1, hw1, hd, hf⟩ := hI
  have ht : t = 0 ∨ t = 1 := by cases h <;> omega
  rcases ht with rfl | rfl
  · -- the setter
    cases h with
    | tau _ _ hs =>
      rw [h0] at hs
      obtain ⟨rfl, hl⟩ := t0_step hs
      have hk13 := t0ok_none hl
      refine ⟨⟨k + 1, by omega, by simp [FCfg.move, upd_eq], fun h3 => hfl (by omega),
        fun h5 => by omega⟩, hs0, hs1, ?_, hd, hf⟩
      simpa [FCfg.move, upd_ne] using hw1
    | lab _ _ hs _ hfu _ _ =>
      rw [h0] at hs
      obtain ⟨rfl, hl⟩ := t0_step hs
      rcases t0ok_some hl with ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, q, rfl⟩
      · refine ⟨⟨1, by omega, by simp [upd_eq], fun h3 => by omega, fun h5 => by omega⟩, hs0, hs1,
          ?_, by dsimp only; exact isSome_updH _ hd,
          by dsimp only; exact isSome_updH _ hf⟩
        simpa [upd_ne] using hw1
      · refine ⟨⟨3, by omega, by simp [upd_eq], fun _ => by simp [Lab.updH, Lab.wval],
          fun h5 => by omega⟩, hs0, hs1, ?_, by dsimp only; exact isSome_updH _ hd,
          by dsimp only; exact isSome_updH _ hf⟩
        simpa [upd_ne] using hw1
      · simp [Lab.isFutex] at hfu
    | again _ _ hs =>
      rw [h0] at hs
      obtain ⟨-, hl⟩ := t0_step hs
      rcases t0ok_some hl with ⟨-, _, h⟩ | ⟨-, h⟩ | ⟨-, _, h⟩ <;> cases h
    | sleep _ _ hs =>
      rw [h0] at hs
      obtain ⟨-, hl⟩ := t0_step hs
      rcases t0ok_some hl with ⟨-, _, h⟩ | ⟨-, h⟩ | ⟨-, _, h⟩ <;> cases h
    | wake _ _ hs _ =>
      rw [h0] at hs
      obtain ⟨rfl, hl⟩ := t0_step hs
      rcases t0ok_some hl with ⟨-, _, h⟩ | ⟨-, h⟩ | ⟨rfl, q, hq⟩
      · cases h
      · cases h
      · simp only [Lab.fwake.injEq] at hq
        obtain ⟨rfl, rfl, rfl⟩ := hq
        have hs1' : (if 0 < 1 ∧ C.sleep 1 = some flagW then none else C.sleep 1) = none := by
          rcases hs1 with h | h <;> simp [h]
        refine ⟨⟨5, le_refl _, by simp [FCfg.move, upd_eq, t0s], fun _ => hfl (by omega),
          fun _ => hs1'⟩, by simp [hs0], Or.inl hs1', ?_, hd, hf⟩
        simpa [FCfg.move, upd_ne] using hw1
    | spurious _ hw => rw [hs0] at hw; cases hw
  · -- the waiter
    have h0' : ∀ (ts : Nat → Stmt × Regs) (x : Stmt × Regs), (upd ts 1 x 0).1 = (ts 0).1 :=
      fun ts x => by simp [upd]
    cases h with
    | tau _ _ hs =>
      obtain ⟨hw', -⟩ := tstep_wOk hs hw1
      exact ⟨⟨k, hk, by simp [FCfg.move, h0', h0], hfl, hfin⟩, hs0, hs1,
        by simpa [FCfg.move, upd_eq] using hw', hd, hf⟩
    | lab _ _ hs _ hfu _ _ =>
      obtain ⟨hw', hl⟩ := tstep_wOk hs hw1
      have hfl' : _ := hl _ rfl
      rcases hfl' with ⟨-, hwv⟩ | ⟨s, r, rfl⟩
      · refine ⟨⟨k, hk, by simp [h0', h0], ?_, hfin⟩, hs0, hs1, by simpa [upd_eq] using hw',
          by dsimp only; exact isSome_updH _ hd,
          by dsimp only; exact isSome_updH _ hf⟩
        intro h3; dsimp only; rw [updH_of_none hwv]; exact hfl h3
      · simp [Lab.isFutex] at hfu
    | again _ _ hs _ _ =>
      obtain ⟨hw', -⟩ := tstep_wOk hs hw1
      exact ⟨⟨k, hk, by simp [FCfg.move, h0', h0], hfl, hfin⟩, hs0, hs1,
        by simpa [FCfg.move, upd_eq] using hw', hd, hf⟩
    | sleep _ _ hs hok =>
      obtain ⟨hw', hl⟩ := tstep_wOk hs hw1
      rcases hl _ rfl with ⟨hfu, -⟩ | ⟨s, r, hq⟩
      · simp [Lab.isFutex] at hfu
      · simp only [Lab.fwait.injEq] at hq
        obtain ⟨rfl, rfl, -, -⟩ := hq
        have hk3 : k < 3 := by
          by_contra hk3
          rw [hfl (by omega)] at hok; cases hok
        refine ⟨⟨k, hk, by simp [FCfg.move, h0', h0], fun h => by omega, fun h => by omega⟩,
          by simp [upd_ne, hs0], Or.inr (by simp [upd_eq]), by simpa [FCfg.move, upd_eq] using hw',
          hd, hf⟩
    | wake _ _ hs _ =>
      obtain ⟨-, hl⟩ := tstep_wOk hs hw1
      rcases hl _ rfl with ⟨hfu, -⟩ | ⟨s, r, hq⟩
      · simp [Lab.isFutex] at hfu
      · cases hq
    | spurious _ _ =>
      exact ⟨⟨k, hk, h0, hfl, fun _ => by simp [upd_eq]⟩, by simp [upd_ne, hs0],
        Or.inl (by simp [upd_eq]), hw1, hd, hf⟩


/-! ## Steps and runs -/

/-- A step of thread `t` leaves every other thread's state alone. -/
theorem ts_other {N : Nat} {C C' : FCfg} {t u : Nat} (h : FStep N C t C') (hu : u ≠ t) :
    C'.cfg.ts u = C.cfg.ts u := by
  cases h <;> simp [FCfg.move, upd_ne _ _ hu]

/-- Each position of a run steps, or stays. -/
def Steps (N : Nat) (run : Nat → FCfg) : Prop :=
  ∀ k, (∃ t, FStep N (run k) t (run (k + 1))) ∨ run (k + 1) = run k

theorem steps_of_isRun {N : Nat} {run : Nat → FCfg} (h : IsRun N run) : Steps N run :=
  fun k => (h k).imp id And.right

theorem steps_of_isRunAwake {N : Nat} {run : Nat → FCfg} (h : IsRunAwake N run) : Steps N run :=
  fun k => (h k).imp (fun ⟨t, _, ht⟩ => ⟨t, ht⟩) And.right

/-- A step of thread `t` does not increase its measure, and decreases it if `t` was awake. -/
theorem msr_step {N : Nat} {C C' : FCfg} {t : Nat} (h : FStep N C t C') :
    msr (C'.cfg.ts t).1 ≤ msr (C.cfg.ts t).1 ∧
      (C.sleep t = none → msr (C'.cfg.ts t).1 < msr (C.cfg.ts t).1) := by
  cases h with
  | tau _ _ hs | again _ _ hs | sleep _ _ hs | wake _ _ hs =>
    have := msr_lt hs
    simp only [FCfg.move, upd_eq]
    exact ⟨by omega, fun _ => this⟩
  | lab _ _ hs =>
    have := msr_lt hs
    simp only [upd_eq]
    exact ⟨by omega, fun _ => this⟩
  | spurious _ hw => exact ⟨le_refl _, fun h => by rw [h] at hw; cases hw⟩

theorem msr_succ {N : Nat} {run : Nat → FCfg} (hR : Steps N run) (u j : Nat) :
    msr ((run (j + 1)).cfg.ts u).1 ≤ msr ((run j).cfg.ts u).1 := by
  rcases hR j with ⟨t, ht⟩ | he
  · by_cases hu : u = t
    · subst hu; exact (msr_step ht).1
    · rw [ts_other ht hu]
  · rw [he]

theorem msr_anti {N : Nat} {run : Nat → FCfg} (hR : Steps N run) (u : Nat) {j k : Nat} (h : j ≤ k) :
    msr ((run k).cfg.ts u).1 ≤ msr ((run j).cfg.ts u).1 := by
  induction k with
  | zero => have : j = 0 := by omega
            subst this; exact le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h' | h'
    · exact (msr_succ hR u k).trans (ih (by omega))
    · have : j = k + 1 := by omega
      subst this; exact le_refl _

/-- **Descent**: under weak fairness, no thread is enabled for ever. -/
theorem not_always_enabled {N : Nat} {run : Nat → FCfg} (hR : Steps N run) (hF : Fair N run)
    {u : Nat} (hu : u < N) {k : Nat} (hE : ∀ j, k ≤ j → Enabled N (run j) u) : False := by
  suffices ∀ m, ∀ k', k ≤ k' → msr ((run k').cfg.ts u).1 ≤ m → False from this _ k le_rfl le_rfl
  intro m
  induction m with
  | zero =>
    intro k' hk' hg
    obtain ⟨j, hj, hs⟩ := hF u hu k' (fun j hj => hE j (le_trans hk' hj))
    have h1 := (msr_step hs).2 (hE j (by omega)).1
    have h2 := msr_anti hR u hj
    omega
  | succ m ih =>
    intro k' hk' hg
    obtain ⟨j, hj, hs⟩ := hF u hu k' (fun j hj => hE j (le_trans hk' hj))
    have h1 := (msr_step hs).2 (hE j (by omega)).1
    have h2 := msr_anti hR u hj
    exact ih (j + 1) (by omega) (by omega)

theorem inv_run {run : Nat → FCfg} (hR : Steps 2 run) (h0 : Inv (run 0)) : ∀ j, Inv (run j) := by
  intro j
  induction j with
  | zero => exact h0
  | succ j ih =>
    rcases hR j with ⟨t, ht⟩ | he
    · exact inv_step ht ih
    · rw [he]; exact ih

/-! ## The setter -/

/-- The setter can step until it finishes. -/
theorem t0_enabled {C : FCfg} (hI : Inv C) (hne : (C.cfg.ts 0).1 ≠ .skip) : Enabled 2 C 0 := by
  obtain ⟨⟨k, hk, h0, -, -⟩, hs0, -, -, hd, hf⟩ := hI
  refine ⟨hs0, ?_⟩
  match k, hk with
  | 0, _ =>
    have hs : TStep (C.cfg.ts 0).1 (C.cfg.ts 0).2 (some (.wr .na .wb data 4 1)) (t0s 1) (C.cfg.ts 0).2 := by
      rw [h0]
      have := TStep.seq (t := .seq stB wk) (TStep.store (m := .na) (sz := 4) (fl := .wb) (a := .lit data)
        (v := .lit 1) (rs := (C.cfg.ts 0).2))
      simpa [Expr.eval, data, stA, t0s] using this
    refine ⟨_, FStep.lab (by omega) hs0 hs rfl rfl ?_ ?_⟩
    · intro a ha
      rcases ha with ⟨v, hv⟩ | hv
      · simp [Lab.reads] at hv
      · simp only [Lab.wval] at hv
        by_cases h : data = a
        · subst h; exact hd
        · simp [h] at hv
    · simp [Lab.okH, Lab.reads]
  | 1, _ =>
    have hs : TStep (C.cfg.ts 0).1 (C.cfg.ts 0).2 none (t0s 2) (C.cfg.ts 0).2 := by
      rw [h0]; exact TStep.seqSkip
    exact ⟨_, FStep.tau (by omega) hs0 hs⟩
  | 2, _ =>
    have hs : TStep (C.cfg.ts 0).1 (C.cfg.ts 0).2 (some (.wr .rel .wb flagW 4 1)) (t0s 3) (C.cfg.ts 0).2 := by
      rw [h0]
      have := TStep.seq (t := wk) (TStep.store (m := .rel) (sz := 4) (fl := .wb) (a := .lit flagW)
        (v := .lit 1) (rs := (C.cfg.ts 0).2))
      simpa [Expr.eval, flagW, stB, t0s] using this
    refine ⟨_, FStep.lab (by omega) hs0 hs rfl rfl ?_ ?_⟩
    · intro a ha
      rcases ha with ⟨v, hv⟩ | hv
      · simp [Lab.reads] at hv
      · simp only [Lab.wval] at hv
        by_cases h : flagW = a
        · subst h; exact hf
        · simp [h] at hv
    · simp [Lab.okH, Lab.reads]
  | 3, _ =>
    have hs : TStep (C.cfg.ts 0).1 (C.cfg.ts 0).2 none (t0s 4) (C.cfg.ts 0).2 := by
      rw [h0]; exact TStep.seqSkip
    exact ⟨_, FStep.tau (by omega) hs0 hs⟩
  | 4, _ =>
    have hs : TStep (C.cfg.ts 0).1 (C.cfg.ts 0).2 (some (.fwake flagW 1 0)) .skip (C.cfg.ts 0).2 := by
      rw [h0]
      have := TStep.fwake (a := .lit flagW) (n := .lit 1) (rs := (C.cfg.ts 0).2) (q := 0) (by omega)
      simpa [Expr.eval, flagW, wk, t0s] using this
    exact ⟨_, FStep.wake (by omega) hs0 hs hf⟩
  | 5, _ => exact (hne h0).elim

/-- A finished setter takes no step. -/
theorem t0_stuck {C C' : FCfg} (hI : Inv C) (h0 : (C.cfg.ts 0).1 = .skip) (h : FStep 2 C 0 C') : False := by
  cases h with
  | tau _ _ hs | lab _ _ hs | again _ _ hs | sleep _ _ hs | wake _ _ hs => rw [h0] at hs; cases hs
  | spurious _ hw => rw [hI.2.1] at hw; cases hw

/-! ## Liveness -/

/-- **The event flag's waiter finishes under weak fairness** (every loop bound `n`): in every
fair run, the waiter reaches a state where it is awake and cannot step. -/
theorem flag_live_steps (n : Nat) : ∀ run : Nat → FCfg,
    run 0 = finit (Silmaril.X86.Concurrency.Cir.Futex.Progs.flag n) → Steps 2 run → Fair 2 run →
    ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' := by
  intro run h0 hR hF
  have hI := inv_run hR (h0 ▸ inv_init n)
  -- The setter finishes.
  obtain ⟨k0, hk0⟩ : ∃ k0, ((run k0).cfg.ts 0).1 = .skip := by
    by_contra hne
    push Not at hne
    exact not_always_enabled hR hF (u := 0) (by omega) (k := 0) fun j _ => t0_enabled (hI j) (hne j)
  -- Then it stays finished.
  have hstay : ∀ j, k0 ≤ j → ((run j).cfg.ts 0).1 = .skip := by
    intro j hj
    induction j with
    | zero => have : k0 = 0 := by omega
              subst this; exact hk0
    | succ j ih =>
      rcases Nat.lt_or_ge k0 (j + 1) with h' | h'
      · have ih := ih (by omega)
        rcases hR j with ⟨t, ht⟩ | he
        · by_cases t0 : t = 0
          · subst t0; exact (t0_stuck (hI j) ih ht).elim
          · rw [ts_other ht (Ne.symm t0)]; exact ih
        · rw [he]; exact ih
      · have : k0 = j + 1 := by omega
        subst this; exact hk0
  -- So the waiter is awake from then on.
  have hawake : ∀ j, k0 ≤ j → (run j).sleep 1 = none := by
    intro j hj
    obtain ⟨⟨k, hk, h0', -, hfin⟩, -⟩ := hI j
    exact hfin (t0s_skip hk (h0'.symm.trans (hstay j hj)))
  -- And it cannot step for ever.
  by_contra hne
  push Not at hne
  exact not_always_enabled hR hF (u := 1) (by omega) (k := k0)
    fun j hj => ⟨hawake j hj, hne j (hawake j hj)⟩


theorem flag_live (n : Nat) : ∀ run : Nat → FCfg,
    run 0 = finit (Silmaril.X86.Concurrency.Cir.Futex.Progs.flag n) → IsRun 2 run → Fair 2 run →
    ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' :=
  fun run h0 hR hF => flag_live_steps n run h0 (steps_of_isRun hR) hF

/-- **The same without spurious wake-ups being forced**: in every weakly fair run
in which only awake threads step and which stops only when no awake thread can step
(`IsRunAwake`), the waiter of the event flag reaches a state where it is awake and cannot step.
Unlike `flag_live`, this is not implied by maximality alone: `flagLate` has such a run in which
the waiter sleeps for ever (`LateRun.flagLate_sleeps`). -/
theorem flag_live_awake (n : Nat) : ∀ run : Nat → FCfg,
    run 0 = finit (Silmaril.X86.Concurrency.Cir.Futex.Progs.flag n) → IsRunAwake 2 run → Fair 2 run →
    ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' :=
  fun run h0 hR hF => flag_live_steps n run h0 (steps_of_isRunAwake hR) hF

/-! ## The statement holds without fairness, for any two-thread program

`Task.flagLive`'s conclusion ("the waiter is awake and cannot step") follows from maximality
alone. `phi` (twice each thread's `msr`, plus one per sleeping thread) drops at every `FStep`:
a thread step drops its `msr` by at least one and may put only itself to sleep; a spurious
wake-up keeps every statement and wakes one thread. So a maximal run reaches a configuration
where nothing steps; there no thread sleeps (a sleeper could wake spuriously). This holds for
the lost-wake-up program `flagLate` too, so the Task does not separate it from `flag`. -/

namespace Review

/-- `1` if thread `u` sleeps. -/
def sl (C : FCfg) (u : Nat) : Nat := if C.sleep u = none then 0 else 1

/-- The measure of a two-thread configuration. -/
def phi (C : FCfg) : Nat :=
  2 * msr (C.cfg.ts 0).1 + sl C 0 + (2 * msr (C.cfg.ts 1).1 + sl C 1)

theorem sl_le (C : FCfg) (u : Nat) : sl C u ≤ 1 := by unfold sl; split <;> omega

theorem step_cases {N : Nat} {C C' : FCfg} {t : Nat} (h : FStep N C t C') :
    (C.sleep t = none ∧ ∀ u, u ≠ t → sl C' u ≤ sl C u) ∨
      (C'.cfg = C.cfg ∧ sl C t = 1 ∧ sl C' t = 0 ∧ ∀ u, u ≠ t → sl C' u = sl C u) := by
  cases h with
  | tau _ hw _ => exact Or.inl ⟨hw, fun _ _ => le_refl _⟩
  | lab _ hw _ _ _ _ _ => exact Or.inl ⟨hw, fun _ _ => le_refl _⟩
  | again _ hw _ _ _ => exact Or.inl ⟨hw, fun _ _ => le_refl _⟩
  | sleep _ hw _ _ =>
    refine Or.inl ⟨hw, fun u hu => ?_⟩
    simp only [sl, upd_ne _ _ hu, le_refl]
  | @wake a n _ _ _ _ hw _ _ =>
    refine Or.inl ⟨hw, fun u _ => ?_⟩
    by_cases h1 : 0 < n ∧ C.sleep u = some a
    · simp only [sl, h1, and_self, ↓reduceIte]; split <;> omega
    · simp only [sl, h1, ↓reduceIte, le_refl]
  | @spurious a _ hw =>
    refine Or.inr ⟨rfl, by simp [sl, hw], by simp [sl, upd_eq], fun u hu => ?_⟩
    simp only [sl, upd_ne _ _ hu]

/-- Every step decreases `phi`. -/
theorem phi_lt {C C' : FCfg} {t : Nat} (h : FStep 2 C t C') : phi C' < phi C := by
  have ht : t < 2 := by cases h <;> assumption
  have h01 : t = 0 ∨ t = 1 := by omega
  have a0 := sl_le C' 0
  have a1 := sl_le C' 1
  rcases step_cases h with ⟨hw, hs⟩ | ⟨hc, h1, h2, ho⟩
  · have hm := (msr_step h).2 hw
    have hst : sl C t = 0 := by simp [sl, hw]
    unfold phi
    rcases h01 with rfl | rfl
    · rw [ts_other h (u := 1) (by decide)]
      have := hs 1 (by decide)
      omega
    · rw [ts_other h (u := 0) (by decide)]
      have := hs 0 (by decide)
      omega
  · unfold phi
    rw [hc]
    rcases h01 with rfl | rfl
    · have := ho 1 (by decide)
      omega
    · have := ho 0 (by decide)
      omega

/-- A maximal two-thread run reaches a configuration where nothing can step. -/
theorem dead_reached {run : Nat → FCfg} (hR : IsRun 2 run) :
    ∃ k, ∀ t C', ¬ FStep 2 (run k) t C' := by
  by_cases hd : ∃ k, ∀ t C', ¬ FStep 2 (run k) t C'
  · exact hd
  exfalso
  have hstep : ∀ k, ∃ t, FStep 2 (run k) t (run (k + 1)) := fun k => by
    rcases hR k with h | ⟨h1, -⟩
    · exact h
    · exact absurd ⟨k, h1⟩ hd
  have hdec : ∀ k, phi (run k) + k ≤ phi (run 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨t, ht⟩ := hstep k
      have := phi_lt ht
      omega
  have := hdec (phi (run 0) + 1)
  omega

/-- **`Task.flagLive`'s conclusion from maximality alone**, for any two-thread program. -/
theorem awake_stuck {run : Nat → FCfg} (hR : IsRun 2 run) :
    ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' := by
  obtain ⟨k, hk⟩ := dead_reached hR
  refine ⟨k, ?_, fun C' => hk 1 C'⟩
  cases hs : (run k).sleep 1 with
  | none => rfl
  | some a => exact absurd (FStep.spurious (by decide) hs) (hk 1 _)

end Review

/-! ## Non-vacuity: a weakly fair run exists -/

namespace NonVacuous

/-- A configuration after thread `t` moves to `(s', rs')`, doing `l`, with sleep map `sl`. -/
def stepC (C : FCfg) (t : Nat) (s' : Stmt) (rs' : Regs) (l : Option Lab) (sl : Nat → Option Nat) : FCfg :=
  ⟨⟨upd C.cfg.ts t (s', rs'), match l with | some l => l.updH C.cfg.mem | none => C.cfg.mem⟩, sl⟩

def L1 : Stmt := ld .rax .acq flagW
def LP (n : Nat) : Stmt :=
  .loop n (eq .rax 0) (Stmt.block [.futexWait .rcx (.lit flagW) (.lit 0), ld .rax .acq flagW])
def L3 : Stmt := ld .rbx .na data
def S4 : Stmt := st .na r0 (.reg .rbx)
def S5 : Stmt := st .na done (.lit 1)
def rs1 : Regs := Regs.zero.set .rax (BitVec.ofNat 64 1)
def rs2 : Regs := rs1.set .rbx (BitVec.ofNat 64 1)
def wake1 (sl : Nat → Option Nat) : Nat → Option Nat :=
  fun u => if 0 < 1 ∧ sl u = some flagW then none else sl u

def c0 (n : Nat) : FCfg := finit (flag n)
def c1 (n : Nat) : FCfg := stepC (c0 n) 0 (t0s 1) Regs.zero (some (.wr .na .wb data 4 1)) (c0 n).sleep
def c2 (n : Nat) : FCfg := stepC (c1 n) 0 (t0s 2) Regs.zero none (c1 n).sleep
def c3 (n : Nat) : FCfg := stepC (c2 n) 0 (t0s 3) Regs.zero (some (.wr .rel .wb flagW 4 1)) (c2 n).sleep
def c4 (n : Nat) : FCfg := stepC (c3 n) 0 (t0s 4) Regs.zero none (c3 n).sleep
def c5 (n : Nat) : FCfg := stepC (c4 n) 0 .skip Regs.zero none (wake1 (c4 n).sleep)
def c6 (n : Nat) : FCfg := stepC (c5 n) 1 (.seq .skip (.seq (LP n) (.seq L3 (.seq S4 S5)))) rs1
  (some (.rd .acq .wb flagW 4 1)) (c5 n).sleep
def c7 (n : Nat) : FCfg := stepC (c6 n) 1 (.seq (LP n) (.seq L3 (.seq S4 S5))) rs1 none (c6 n).sleep
def c8 (n : Nat) : FCfg := stepC (c7 n) 1 (.seq .skip (.seq L3 (.seq S4 S5))) rs1 none (c7 n).sleep
def c9 (n : Nat) : FCfg := stepC (c8 n) 1 (.seq L3 (.seq S4 S5)) rs1 none (c8 n).sleep
def c10 (n : Nat) : FCfg := stepC (c9 n) 1 (.seq .skip (.seq S4 S5)) rs2 (some (.rd .na .wb data 4 1)) (c9 n).sleep
def c11 (n : Nat) : FCfg := stepC (c10 n) 1 (.seq S4 S5) rs2 none (c10 n).sleep
def c12 (n : Nat) : FCfg := stepC (c11 n) 1 (.seq .skip S5) rs2 (some (.wr .na .wb r0 4 1)) (c11 n).sleep
def c13 (n : Nat) : FCfg := stepC (c12 n) 1 S5 rs2 none (c12 n).sleep
def c14 (n : Nat) : FCfg := stepC (c13 n) 1 .skip rs2 (some (.wr .na .wb done 4 1)) (c13 n).sleep

/-- One fair run of the event flag: the setter runs to the end, then the waiter reads the flag
`1`, skips the loop and finishes; then nothing moves. -/
def frun (n : Nat) : Nat → FCfg
  | 0 => c0 n | 1 => c1 n | 2 => c2 n | 3 => c3 n | 4 => c4 n | 5 => c5 n | 6 => c6 n
  | 7 => c7 n | 8 => c8 n | 9 => c9 n | 10 => c10 n | 11 => c11 n | 12 => c12 n | 13 => c13 n
  | _ => c14 n

theorem lab_of {C : FCfg} {t : Nat} {s : Stmt} {rs : Regs} {l : Lab} {s' : Stmt} {rs' : Regs}
    (h0 : C.cfg.ts t = (s, rs)) (hs : TStep s rs (some l) s' rs') (ht : t < 2) (hw : C.sleep t = none)
    (hm : l.isMem = true) (hf : l.isFutex = false) (hc : ∀ a, l.Touches a → (C.cfg.mem a).isSome)
    (hok : l.okH C.cfg.mem) : FStep 2 C t (stepC C t s' rs' (some l) C.sleep) := by
  have hs' : TStep (C.cfg.ts t).1 (C.cfg.ts t).2 (some l) s' rs' := by rw [h0]; exact hs
  exact FStep.lab ht hw hs' hm hf hc hok

theorem tau_of {C : FCfg} {t : Nat} {s : Stmt} {rs : Regs} {s' : Stmt} {rs' : Regs}
    (h0 : C.cfg.ts t = (s, rs)) (hs : TStep s rs none s' rs') (ht : t < 2) (hw : C.sleep t = none) :
    FStep 2 C t (stepC C t s' rs' none C.sleep) := by
  have hs' : TStep (C.cfg.ts t).1 (C.cfg.ts t).2 none s' rs' := by rw [h0]; exact hs
  exact FStep.tau ht hw hs'

/-- A label on one cell touches only that cell. -/
theorem touches_wr {m : Mode} {fl : Flav} {a0 sz v a : Nat} (h : (Lab.wr m fl a0 sz v).Touches a) : a = a0 := by
  rcases h with ⟨w, hw⟩ | hw
  · simp [Lab.reads] at hw
  · simp only [Lab.wval] at hw
    by_cases h : a0 = a
    · exact h.symm
    · simp [h] at hw

theorem touches_rd {m : Mode} {fl : Flav} {a0 sz v a : Nat} (h : (Lab.rd m fl a0 sz v).Touches a) : a = a0 := by
  rcases h with ⟨w, hw⟩ | hw
  · simp [Lab.reads] at hw; exact hw.1
  · simp [Lab.wval] at hw

theorem hs0 : TStep (t0s 0) Regs.zero (some (.wr .na .wb data 4 1)) (t0s 1) Regs.zero := by
  have := TStep.seq (t := .seq stB wk) (TStep.store (m := .na) (sz := 4) (fl := .wb) (a := .lit data)
    (v := .lit 1) (rs := Regs.zero))
  simpa [Expr.eval, data, stA, t0s] using this

theorem hs2 : TStep (t0s 2) Regs.zero (some (.wr .rel .wb flagW 4 1)) (t0s 3) Regs.zero := by
  have := TStep.seq (t := wk) (TStep.store (m := .rel) (sz := 4) (fl := .wb) (a := .lit flagW)
    (v := .lit 1) (rs := Regs.zero))
  simpa [Expr.eval, flagW, stB, t0s] using this

theorem hs4 : TStep (t0s 4) Regs.zero (some (.fwake flagW 1 0)) .skip Regs.zero := by
  have := TStep.fwake (a := .lit flagW) (n := .lit 1) (rs := Regs.zero) (q := 0) (by omega)
  simpa [Expr.eval, flagW, wk, t0s] using this

theorem hs6 (n : Nat) : TStep (.seq L1 (.seq (LP n) (.seq L3 (.seq S4 S5)))) Regs.zero
    (some (.rd .acq .wb flagW 4 1)) (.seq .skip (.seq (LP n) (.seq L3 (.seq S4 S5)))) rs1 := by
  have := TStep.seq (t := .seq (LP n) (.seq L3 (.seq S4 S5))) (TStep.load (d := .rax) (m := .acq) (sz := 4)
    (fl := .wb) (a := .lit flagW) (rs := Regs.zero) (v := 1) (by omega))
  simpa [Expr.eval, flagW, L1, ld, rs1] using this

theorem hs8 (n : Nat) : TStep (.seq (LP n) (.seq L3 (.seq S4 S5))) rs1 none
    (.seq .skip (.seq L3 (.seq S4 S5))) rs1 := by
  refine TStep.seq (TStep.loopF ?_)
  decide

theorem hs10 : TStep (.seq L3 (.seq S4 S5)) rs1 (some (.rd .na .wb data 4 1)) (.seq .skip (.seq S4 S5)) rs2 := by
  have := TStep.seq (t := .seq S4 S5) (TStep.load (d := .rbx) (m := .na) (sz := 4)
    (fl := .wb) (a := .lit data) (rs := rs1) (v := 1) (by omega))
  simpa [Expr.eval, data, L3, ld, rs2] using this

theorem hs12 : TStep (.seq S4 S5) rs2 (some (.wr .na .wb r0 4 1)) (.seq .skip S5) rs2 := by
  have := TStep.seq (t := S5) (TStep.store (m := .na) (sz := 4) (fl := .wb) (a := .lit r0)
    (v := .reg .rbx) (rs := rs2))
  have h1 : (rs2 .rbx).toNat % 4294967296 = 1 := by decide
  simpa [Expr.eval, r0, S4, st, h1] using this

theorem hs14 : TStep S5 rs2 (some (.wr .na .wb done 4 1)) .skip rs2 := by
  have := TStep.store (m := .na) (sz := 4) (fl := .wb) (a := .lit done) (v := .lit 1) (rs := rs2)
  simpa [Expr.eval, done, S5, st] using this

theorem wake_of {C : FCfg} {t : Nat} {s : Stmt} {rs : Regs} {a n q : Nat} {s' : Stmt} {rs' : Regs}
    (h0 : C.cfg.ts t = (s, rs)) (hs : TStep s rs (some (.fwake a n q)) s' rs') (ht : t < 2)
    (hw : C.sleep t = none) (hc : (C.cfg.mem a).isSome) :
    FStep 2 C t (stepC C t s' rs' none fun u => if 0 < n ∧ C.sleep u = some a then none else C.sleep u) := by
  have hs' : TStep (C.cfg.ts t).1 (C.cfg.ts t).2 (some (.fwake a n q)) s' rs' := by rw [h0]; exact hs
  exact FStep.wake ht hw hs' hc

theorem okH_rd {H : Csl.Heap} {m : Mode} {fl : Flav} {a sz v : Nat} (h : H a = some v) :
    (Lab.rd m fl a sz v).okH H := by
  intro p hp; simp [Lab.reads] at hp; rw [hp]; exact h

theorem okH_wr {H : Csl.Heap} {m : Mode} {fl : Flav} {a sz v : Nat} : (Lab.wr m fl a sz v).okH H := by
  intro p hp; simp [Lab.reads] at hp

theorem step0 (n : Nat) : FStep 2 (c0 n) 0 (c1 n) :=
  lab_of (s := t0s 0) (rs := Regs.zero) rfl hs0 (by decide) rfl rfl rfl
    (fun a h => by rw [touches_wr h]; rfl) okH_wr
theorem step1 (n : Nat) : FStep 2 (c1 n) 0 (c2 n) :=
  tau_of (s := t0s 1) (rs := Regs.zero) rfl (TStep.seqSkip : TStep (t0s 1) _ _ (t0s 2) _) (by decide) rfl
theorem step2 (n : Nat) : FStep 2 (c2 n) 0 (c3 n) :=
  lab_of (s := t0s 2) (rs := Regs.zero) rfl hs2 (by decide) rfl rfl rfl
    (fun a h => by rw [touches_wr h]; rfl) okH_wr
theorem step3 (n : Nat) : FStep 2 (c3 n) 0 (c4 n) :=
  tau_of (s := t0s 3) (rs := Regs.zero) rfl (TStep.seqSkip : TStep (t0s 3) _ _ (t0s 4) _) (by decide) rfl
theorem step4 (n : Nat) : FStep 2 (c4 n) 0 (c5 n) :=
  wake_of (s := t0s 4) (rs := Regs.zero) rfl hs4 (by decide) rfl rfl
theorem step5 (n : Nat) : FStep 2 (c5 n) 1 (c6 n) :=
  lab_of (s := .seq L1 (.seq (LP n) (.seq L3 (.seq S4 S5)))) (rs := Regs.zero) rfl (hs6 n) (by decide)
    rfl rfl rfl (fun a h => by rw [touches_rd h]; rfl) (okH_rd rfl)
theorem step6 (n : Nat) : FStep 2 (c6 n) 1 (c7 n) :=
  tau_of (s := .seq .skip (.seq (LP n) (.seq L3 (.seq S4 S5)))) (rs := rs1) rfl TStep.seqSkip (by decide) rfl
theorem step7 (n : Nat) : FStep 2 (c7 n) 1 (c8 n) :=
  tau_of (s := .seq (LP n) (.seq L3 (.seq S4 S5))) (rs := rs1) rfl (hs8 n) (by decide) rfl
theorem step8 (n : Nat) : FStep 2 (c8 n) 1 (c9 n) :=
  tau_of (s := .seq .skip (.seq L3 (.seq S4 S5))) (rs := rs1) rfl TStep.seqSkip (by decide) rfl
theorem step9 (n : Nat) : FStep 2 (c9 n) 1 (c10 n) :=
  lab_of (s := .seq L3 (.seq S4 S5)) (rs := rs1) rfl hs10 (by decide) rfl rfl rfl
    (fun a h => by rw [touches_rd h]; rfl) (okH_rd rfl)
theorem step10 (n : Nat) : FStep 2 (c10 n) 1 (c11 n) :=
  tau_of (s := .seq .skip (.seq S4 S5)) (rs := rs2) rfl TStep.seqSkip (by decide) rfl
theorem step11 (n : Nat) : FStep 2 (c11 n) 1 (c12 n) :=
  lab_of (s := .seq S4 S5) (rs := rs2) rfl hs12 (by decide) rfl rfl rfl
    (fun a h => by rw [touches_wr h]; rfl) okH_wr
theorem step12 (n : Nat) : FStep 2 (c12 n) 1 (c13 n) :=
  tau_of (s := .seq .skip S5) (rs := rs2) rfl TStep.seqSkip (by decide) rfl
theorem step13 (n : Nat) : FStep 2 (c13 n) 1 (c14 n) :=
  lab_of (s := S5) (rs := rs2) rfl hs14 (by decide) rfl rfl rfl
    (fun a h => by rw [touches_wr h]; rfl) okH_wr

theorem stuck14 (n : Nat) : ∀ t C', ¬ FStep 2 (c14 n) t C' := by
  intro t C' h
  have ht : t = 0 ∨ t = 1 := by cases h <;> omega
  have h0 : ((c14 n).cfg.ts t).1 = .skip := by rcases ht with rfl | rfl <;> rfl
  have hw : (c14 n).sleep t = none := by rcases ht with rfl | rfl <;> rfl
  cases h with
  | tau _ _ hs | lab _ _ hs | again _ _ hs | sleep _ _ hs | wake _ _ hs => rw [h0] at hs; cases hs
  | spurious _ h' => rw [hw] at h'; cases h'

/-- A run that reaches a configuration where nothing can step, and stays there, is maximal and
weakly fair. -/
theorem run_fair_of {N : Nat} {f : Nat → FCfg} {m : Nat} (hstep : ∀ j < m, ∃ t, FStep N (f j) t (f (j + 1)))
    (hend : ∀ j, m ≤ j → f j = f m) (hstuck : ∀ t C', ¬ FStep N (f m) t C') : IsRun N f ∧ Fair N f := by
  refine ⟨fun k => ?_, fun t _ k hE => ?_⟩
  · rcases Nat.lt_or_ge k m with h | h
    · exact Or.inl (hstep k h)
    · refine Or.inr ⟨fun t C' => by rw [hend k h]; exact hstuck t C', ?_⟩
      rw [hend k h, hend (k + 1) (by omega)]
  · obtain ⟨-, C', hC⟩ := hE (max k m) (le_max_left _ _)
    rw [hend _ (le_max_right _ _)] at hC
    exact (hstuck _ _ hC).elim

theorem frun_end (n : Nat) : ∀ j, 14 ≤ j → frun n j = frun n 14 := by
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 14 := ⟨j - 14, by omega⟩
  rfl

/-- **A weakly fair run of the event flag exists** (for every loop bound): `Task.flagLive`'s
hypotheses are satisfiable, so the liveness theorem is not vacuous. In this run the waiter
finishes (its statement is `skip`). -/
theorem flag_fair_run (n : Nat) : ∃ run : Nat → FCfg,
    run 0 = finit (flag n) ∧ IsRun 2 run ∧ Fair 2 run ∧ ∃ k, ((run k).cfg.ts 1).1 = .skip := by
  refine ⟨frun n, rfl, ?_⟩
  have hstep : ∀ j < 14, ∃ t, FStep 2 (frun n j) t (frun n (j + 1)) := fun j hj =>
    match j, hj with
    | 0, _ => ⟨0, step0 n⟩ | 1, _ => ⟨0, step1 n⟩ | 2, _ => ⟨0, step2 n⟩ | 3, _ => ⟨0, step3 n⟩
    | 4, _ => ⟨0, step4 n⟩ | 5, _ => ⟨1, step5 n⟩ | 6, _ => ⟨1, step6 n⟩ | 7, _ => ⟨1, step7 n⟩
    | 8, _ => ⟨1, step8 n⟩ | 9, _ => ⟨1, step9 n⟩ | 10, _ => ⟨1, step10 n⟩ | 11, _ => ⟨1, step11 n⟩
    | 12, _ => ⟨1, step12 n⟩ | 13, _ => ⟨1, step13 n⟩
  have h := run_fair_of hstep (frun_end n) (stuck14 n)
  exact ⟨h.1, h.2, 14, rfl⟩

/-- The same run takes only steps of awake threads, so it is also an `IsRunAwake` run: the
hypotheses of `flag_live_awake` are satisfiable. -/
theorem flag_awake_run (n : Nat) : ∃ run : Nat → FCfg,
    run 0 = finit (flag n) ∧ IsRunAwake 2 run ∧ Fair 2 run ∧ ∃ k, ((run k).cfg.ts 1).1 = .skip := by
  refine ⟨frun n, rfl, fun k => ?_, (run_fair_of (m := 14) (fun j hj => ?_) (frun_end n) (stuck14 n)).2,
    14, rfl⟩
  · rcases Nat.lt_or_ge k 14 with h | h
    · refine Or.inl ?_
      match k, h with
      | 0, _ => exact ⟨0, rfl, step0 n⟩ | 1, _ => exact ⟨0, rfl, step1 n⟩
      | 2, _ => exact ⟨0, rfl, step2 n⟩ | 3, _ => exact ⟨0, rfl, step3 n⟩
      | 4, _ => exact ⟨0, rfl, step4 n⟩ | 5, _ => exact ⟨1, rfl, step5 n⟩
      | 6, _ => exact ⟨1, rfl, step6 n⟩ | 7, _ => exact ⟨1, rfl, step7 n⟩
      | 8, _ => exact ⟨1, rfl, step8 n⟩ | 9, _ => exact ⟨1, rfl, step9 n⟩
      | 10, _ => exact ⟨1, rfl, step10 n⟩ | 11, _ => exact ⟨1, rfl, step11 n⟩
      | 12, _ => exact ⟨1, rfl, step12 n⟩ | 13, _ => exact ⟨1, rfl, step13 n⟩
    · refine Or.inr ⟨fun t C' _ => by rw [frun_end n k h]; exact stuck14 n t C', ?_⟩
      rw [frun_end n k h, frun_end n (k + 1) (by omega)]
  · match j, hj with
    | 0, _ => exact ⟨0, step0 n⟩ | 1, _ => exact ⟨0, step1 n⟩ | 2, _ => exact ⟨0, step2 n⟩
    | 3, _ => exact ⟨0, step3 n⟩ | 4, _ => exact ⟨0, step4 n⟩ | 5, _ => exact ⟨1, step5 n⟩
    | 6, _ => exact ⟨1, step6 n⟩ | 7, _ => exact ⟨1, step7 n⟩ | 8, _ => exact ⟨1, step8 n⟩
    | 9, _ => exact ⟨1, step9 n⟩ | 10, _ => exact ⟨1, step10 n⟩ | 11, _ => exact ⟨1, step11 n⟩
    | 12, _ => exact ⟨1, step12 n⟩ | 13, _ => exact ⟨1, step13 n⟩

end NonVacuous

/-! ## The lost wake-up, as a liveness failure

With the wake before the flag store (`flagLate`), the run "setter stores data and wakes (nobody
sleeps yet); the waiter reads `flag = 0`, enters the loop and sleeps; the setter stores the flag
and finishes" ends with the waiter asleep and no awake thread able to step. It is a maximal run
of awake steps (`IsRunAwake`) and weakly fair, and the waiter sleeps for ever. So
`flag_live_awake` separates `flag` from `flagLate`, which `Task.flagLive` does not. -/

namespace LateRun

open NonVacuous

/-- The setter of `flagLate`, after its first and third steps. -/
def u0 : Stmt := .seq stA (.seq wk stB)
def R : Stmt := .seq L3 (.seq S4 S5)
def B : Stmt := .seq (.futexWait .rcx (.lit flagW) (.lit 0)) L1
def rsA : Regs := Regs.zero.set .rax (BitVec.ofNat 64 0)
def rsB : Regs := rsA.set .rcx (BitVec.ofNat 64 0)

def d0 (m : Nat) : FCfg := finit (flagLate (m + 1))
def d1 (m : Nat) : FCfg := stepC (d0 m) 0 (.seq .skip (.seq wk stB)) Regs.zero (some (.wr .na .wb data 4 1)) (d0 m).sleep
def d2 (m : Nat) : FCfg := stepC (d1 m) 0 (.seq wk stB) Regs.zero none (d1 m).sleep
def d3 (m : Nat) : FCfg := stepC (d2 m) 0 (.seq .skip stB) Regs.zero none (wake1 (d2 m).sleep)
def d4 (m : Nat) : FCfg := stepC (d3 m) 0 stB Regs.zero none (d3 m).sleep
def d5 (m : Nat) : FCfg := stepC (d4 m) 1 (.seq .skip (.seq (LP (m + 1)) R)) rsA
  (some (.rd .acq .wb flagW 4 0)) (d4 m).sleep
def d6 (m : Nat) : FCfg := stepC (d5 m) 1 (.seq (LP (m + 1)) R) rsA none (d5 m).sleep
def d7 (m : Nat) : FCfg := stepC (d6 m) 1 (.seq (.seq B (LP m)) R) rsA none (d6 m).sleep
def d8 (m : Nat) : FCfg := stepC (d7 m) 1 (.seq (.seq (.seq .skip L1) (LP m)) R) rsB none
  (upd (d7 m).sleep 1 (some flagW))
def d9 (m : Nat) : FCfg := stepC (d8 m) 0 .skip Regs.zero (some (.wr .rel .wb flagW 4 1)) (d8 m).sleep

def lrun (m : Nat) : Nat → FCfg
  | 0 => d0 m | 1 => d1 m | 2 => d2 m | 3 => d3 m | 4 => d4 m | 5 => d5 m | 6 => d6 m
  | 7 => d7 m | 8 => d8 m | _ => d9 m

theorem g0 : TStep u0 Regs.zero (some (.wr .na .wb data 4 1)) (.seq .skip (.seq wk stB)) Regs.zero := by
  have := TStep.seq (t := .seq wk stB) (TStep.store (m := .na) (sz := 4) (fl := .wb) (a := .lit data)
    (v := .lit 1) (rs := Regs.zero))
  simpa [Expr.eval, data, stA, u0] using this

theorem g2 : TStep (.seq wk stB) Regs.zero (some (.fwake flagW 1 0)) (.seq .skip stB) Regs.zero := by
  have := TStep.seq (t := stB) (TStep.fwake (a := .lit flagW) (n := .lit 1) (rs := Regs.zero) (q := 0) (by omega))
  simpa [Expr.eval, flagW, wk] using this

theorem g4 : TStep stB Regs.zero (some (.wr .rel .wb flagW 4 1)) .skip Regs.zero := by
  have := TStep.store (m := .rel) (sz := 4) (fl := .wb) (a := .lit flagW) (v := .lit 1) (rs := Regs.zero)
  simpa [Expr.eval, flagW, stB] using this

theorem g5 (n : Nat) : TStep (.seq L1 (.seq (LP n) R)) Regs.zero
    (some (.rd .acq .wb flagW 4 0)) (.seq .skip (.seq (LP n) R)) rsA := by
  have := TStep.seq (t := .seq (LP n) R) (TStep.load (d := .rax) (m := .acq) (sz := 4)
    (fl := .wb) (a := .lit flagW) (rs := Regs.zero) (v := 0) (by omega))
  simpa [Expr.eval, flagW, L1, ld, rsA] using this

theorem g7 (m : Nat) : TStep (.seq (LP (m + 1)) R) rsA none (.seq (.seq B (LP m)) R) rsA := by
  refine TStep.seq (TStep.loopT ?_)
  decide

theorem g8 (m : Nat) : TStep (.seq (.seq B (LP m)) R) rsA (some (.fwait flagW 0 0 0))
    (.seq (.seq (.seq .skip L1) (LP m)) R) rsB := by
  have := TStep.seq (t := R) (TStep.seq (t := LP m) (TStep.seq (t := L1)
    (TStep.fwait (d := .rcx) (a := .lit flagW) (v := .lit 0) (rs := rsA) (seen := 0) (r := 0)
      (by omega) (by omega))))
  simpa [Expr.eval, flagW, B, rsB] using this

theorem sleep_of {C : FCfg} {t : Nat} {s : Stmt} {rs : Regs} {a e r : Nat} {s' : Stmt} {rs' : Regs}
    (h0 : C.cfg.ts t = (s, rs)) (hs : TStep s rs (some (.fwait a e e r)) s' rs') (ht : t < 2)
    (hw : C.sleep t = none) (hok : C.cfg.mem a = some e) :
    FStep 2 C t (stepC C t s' rs' none (upd C.sleep t (some a))) := by
  have hs' : TStep (C.cfg.ts t).1 (C.cfg.ts t).2 (some (.fwait a e e r)) s' rs' := by rw [h0]; exact hs
  exact FStep.sleep ht hw hs' hok

theorem e0 (m : Nat) : FStep 2 (d0 m) 0 (d1 m) :=
  lab_of (s := u0) (rs := Regs.zero) rfl g0 (by decide) rfl rfl rfl
    (fun a h => by rw [touches_wr h]; rfl) okH_wr
theorem e1 (m : Nat) : FStep 2 (d1 m) 0 (d2 m) :=
  tau_of (s := .seq .skip (.seq wk stB)) (rs := Regs.zero) rfl TStep.seqSkip (by decide) rfl
theorem e2 (m : Nat) : FStep 2 (d2 m) 0 (d3 m) :=
  wake_of (s := .seq wk stB) (rs := Regs.zero) rfl g2 (by decide) rfl rfl
theorem e3 (m : Nat) : FStep 2 (d3 m) 0 (d4 m) :=
  tau_of (s := .seq .skip stB) (rs := Regs.zero) rfl TStep.seqSkip (by decide) rfl
theorem e4 (m : Nat) : FStep 2 (d4 m) 1 (d5 m) :=
  lab_of (s := .seq L1 (.seq (LP (m + 1)) R)) (rs := Regs.zero) rfl (g5 _) (by decide)
    rfl rfl rfl (fun a h => by rw [touches_rd h]; rfl) (okH_rd rfl)
theorem e5 (m : Nat) : FStep 2 (d5 m) 1 (d6 m) :=
  tau_of (s := .seq .skip (.seq (LP (m + 1)) R)) (rs := rsA) rfl TStep.seqSkip (by decide) rfl
theorem e6 (m : Nat) : FStep 2 (d6 m) 1 (d7 m) :=
  tau_of (s := .seq (LP (m + 1)) R) (rs := rsA) rfl (g7 m) (by decide) rfl
theorem e7 (m : Nat) : FStep 2 (d7 m) 1 (d8 m) :=
  sleep_of (s := .seq (.seq B (LP m)) R) (rs := rsA) rfl (g8 m) (by decide) rfl rfl
theorem e8 (m : Nat) : FStep 2 (d8 m) 0 (d9 m) :=
  lab_of (s := stB) (rs := Regs.zero) rfl g4 (by decide) rfl rfl rfl
    (fun a h => by rw [touches_wr h]; rfl) okH_wr

theorem sleeps9 (m : Nat) : (d9 m).sleep 1 = some flagW := rfl

/-- At the end, no awake thread can step (the setter is done, the waiter sleeps). -/
theorem stuck9 (m : Nat) : ∀ t C', (d9 m).sleep t = none → ¬ FStep 2 (d9 m) t C' := by
  intro t C' hw h
  have ht : t = 0 ∨ t = 1 := by cases h <;> omega
  rcases ht with rfl | rfl
  · have h0 : ((d9 m).cfg.ts 0).1 = .skip := rfl
    cases h with
    | tau _ _ hs | lab _ _ hs | again _ _ hs | sleep _ _ hs | wake _ _ hs => rw [h0] at hs; cases hs
    | spurious _ h' => rw [hw] at h'; cases h'
  · rw [sleeps9] at hw; cases hw

/-- **The lost wake-up as a liveness failure** (every loop bound `m + 1`): a run of `flagLate`
that is maximal over awake steps and weakly fair, in which the waiter sleeps for ever. -/
theorem lrun_props (m : Nat) :
    lrun m 0 = finit (flagLate (m + 1)) ∧ IsRunAwake 2 (lrun m) ∧ Fair 2 (lrun m) ∧
      ∀ k, 8 ≤ k → (lrun m k).sleep 1 = some flagW := by
  have hend : ∀ j, 9 ≤ j → lrun m j = d9 m := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 9 := ⟨j - 9, by omega⟩
    rfl
  have hstep : ∀ j < 9, ∃ t, (lrun m j).sleep t = none ∧ FStep 2 (lrun m j) t (lrun m (j + 1)) :=
    fun j hj => match j, hj with
    | 0, _ => ⟨0, rfl, e0 m⟩ | 1, _ => ⟨0, rfl, e1 m⟩ | 2, _ => ⟨0, rfl, e2 m⟩
    | 3, _ => ⟨0, rfl, e3 m⟩ | 4, _ => ⟨1, rfl, e4 m⟩ | 5, _ => ⟨1, rfl, e5 m⟩
    | 6, _ => ⟨1, rfl, e6 m⟩ | 7, _ => ⟨1, rfl, e7 m⟩ | 8, _ => ⟨0, rfl, e8 m⟩
  refine ⟨rfl, fun k => ?_, fun t _ k hE => ?_, fun k hk => ?_⟩
  · rcases Nat.lt_or_ge k 9 with h | h
    · exact Or.inl (hstep k h)
    · refine Or.inr ⟨fun t C' => by rw [hend k h]; exact stuck9 m t C', ?_⟩
      rw [hend k h, hend (k + 1) (by omega)]
  · obtain ⟨hw, C', hC⟩ := hE (max k 9) (le_max_left _ _)
    rw [hend _ (le_max_right _ _)] at hw hC
    exact (stuck9 m _ _ hw hC).elim
  · rcases Nat.lt_or_ge k 9 with h | h
    · have : k = 8 := by omega
      subst this; rfl
    · rw [hend k h]; rfl

theorem flagLate_sleeps (m : Nat) : ∃ run : Nat → FCfg,
    run 0 = finit (flagLate (m + 1)) ∧ IsRunAwake 2 run ∧ Fair 2 run ∧
      ∀ k, 8 ≤ k → (run k).sleep 1 = some flagW :=
  ⟨lrun m, lrun_props m⟩

/-- In this run the waiter is never awake and stuck: before position `8` it can step, from
then on it sleeps. -/
theorem never_stuck (m : Nat) (k : Nat) :
    ¬ ((lrun m k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (lrun m k) 1 C') := by
  rintro ⟨hw, hn⟩
  have w0 : ∀ C : FCfg, C.cfg.ts 1 = (.seq L1 (.seq (LP (m + 1)) R), Regs.zero) → C.sleep 1 = none →
      C.cfg.mem flagW = some 0 → (C.cfg.mem flagW).isSome → ∃ C', FStep 2 C 1 C' :=
    fun C h0 hw' hm hc => ⟨_, lab_of h0 (g5 _) (by decide) hw' rfl rfl
      (fun a h => by rw [touches_rd h]; exact hc) (okH_rd hm)⟩
  match k with
  | 0 => obtain ⟨C', h⟩ := w0 (d0 m) rfl rfl rfl rfl; exact hn C' h
  | 1 => obtain ⟨C', h⟩ := w0 (d1 m) rfl rfl rfl rfl; exact hn C' h
  | 2 => obtain ⟨C', h⟩ := w0 (d2 m) rfl rfl rfl rfl; exact hn C' h
  | 3 => obtain ⟨C', h⟩ := w0 (d3 m) rfl rfl rfl rfl; exact hn C' h
  | 4 => exact hn _ (e4 m)
  | 5 => exact hn _ (e5 m)
  | 6 => exact hn _ (e6 m)
  | 7 => exact hn _ (e7 m)
  | 8 => exact absurd hw (by rw [show lrun m 8 = d8 m from rfl]; exact fun h => by cases h)
  | _ + 9 => exact absurd hw (by rw [show lrun m _ = d9 m from rfl, sleeps9]; exact fun h => by cases h)

/-- **`flag_live_awake`'s statement is false for `flagLate`** (every loop bound `m + 1`). -/
theorem not_late_live (m : Nat) : ¬ ∀ run : Nat → FCfg,
    run 0 = finit (flagLate (m + 1)) → IsRunAwake 2 run → Fair 2 run →
      ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' := by
  intro h
  obtain ⟨-, hR, hF, -⟩ := lrun_props m
  obtain ⟨k, hk⟩ := h (lrun m) rfl hR hF
  exact never_stuck m k hk

end LateRun

end Silmaril.Proofs.X86.Concurrency.Cir.FutexLive
