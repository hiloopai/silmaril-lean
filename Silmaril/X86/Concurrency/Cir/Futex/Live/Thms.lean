module

public import Silmaril.X86.Concurrency.Cir.Futex.Live.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Futex.Live

/-!
# Futex liveness under fairness: what is proved

The proof is in
`Silmaril/Proofs/X86/Concurrency/Cir/Futex/Live.lean`.

* `flagLive n`: **`Task.flagLive n` holds for every loop bound `n`.** In every weakly fair run
  of the event flag on the SC futex machine, the waiter reaches a state where it is awake and
  cannot step (finished, or out of its CIR loop bound).
* `not_always_enabled`: under weak fairness no thread is enabled for ever (every thread step
  decreases a measure of the thread's statement, `msr`). This holds for every CIR program on
  `FStep`, not only the event flag.
* `flag_fair_run n`: the hypotheses are satisfiable: an explicit maximal weakly fair run of the
  event flag exists, and in it the waiter finishes. So `flagLive` is not vacuous.

Scope, as stated in `Futex.Live.Defs`: SC only.

**Finding**: the statement is much weaker than its docstring suggests.
* `awake_stuck`: in every *maximal* run of *any* two-thread program (fair or not), thread `1`
  reaches a configuration where it is awake and cannot step: every step decreases a measure
  (statements plus sleepers), and a sleeper can always wake spuriously, so a maximal run ends
  where nothing can step and nobody sleeps. Hence `flagLive_of_isRun`: `Task.flagLive` needs
  neither fairness nor the event flag's protocol.
* `flagLate_live`: the same statement holds for `Progs.flagLate`, the lost-wake-up program. So
  `Task.flagLive` does not separate the correct flag from the buggy one; the lost wake-up is
  only visible on the axiomatic side (`Tv.CFutex.flagLate_lost`).
* The separating statement (added later): `flagLive_awake` is the same conclusion over
  `IsRunAwake` runs (only awake threads step; the run stops when no awake thread can step, so a
  sleeper is never forced to wake). It holds for the event flag (`flagLive_awake`, by the same
  fairness argument), its hypotheses are satisfiable (`flag_awake_run`), and it **fails** for
  `flagLate`: `flagLate_sleeps` is an `IsRunAwake`, weakly fair run in which the waiter sleeps
  for ever (the setter wakes before the waiter sleeps, then stores the flag).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Futex.Live

/-- **Weak fairness forces progress**: in a weakly fair run (of any CIR program on the SC futex
machine), no thread is enabled from some point on for ever. -/
theorem not_always_enabled {N : Nat} {run : Nat → FCfg} (hR : IsRun N run) (hF : Fair N run)
    {u : Nat} (hu : u < N) {k : Nat} (hE : ∀ j, k ≤ j → Enabled N (run j) u) : False :=
  Silmaril.Proofs.X86.Concurrency.Cir.FutexLive.not_always_enabled
    (Silmaril.Proofs.X86.Concurrency.Cir.FutexLive.steps_of_isRun hR) hF hu hE

/-- **`Task.flagLive n` holds**: the event flag's waiter finishes under weak
fairness, for every loop bound `n`. -/
theorem flagLive (n : Nat) : Task.flagLive n :=
  Silmaril.Proofs.X86.Concurrency.Cir.FutexLive.flag_live n

/-- **A weakly fair run of the event flag exists** (every loop bound `n`): `Task.flagLive`'s
hypotheses are satisfiable. In this run the waiter's statement reaches `skip`. -/
theorem flag_fair_run (n : Nat) : ∃ run : Nat → FCfg,
    run 0 = finit (Futex.Progs.flag n) ∧ IsRun 2 run ∧ Fair 2 run ∧ ∃ k, ((run k).cfg.ts 1).1 = .skip :=
  Silmaril.Proofs.X86.Concurrency.Cir.FutexLive.NonVacuous.flag_fair_run n

/-- **Maximality alone gives `Task.flagLive`'s conclusion**, for any two-thread
program: in every maximal run, thread `1` reaches a configuration where it is awake and cannot
step. No fairness is used. -/
theorem awake_stuck {run : Nat → FCfg} (hR : IsRun 2 run) :
    ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' :=
  Silmaril.Proofs.X86.Concurrency.Cir.FutexLive.Review.awake_stuck hR

/-- `Task.flagLive n` without the fairness hypothesis. -/
theorem flagLive_of_isRun (n : Nat) : ∀ run : Nat → FCfg, run 0 = finit (Futex.Progs.flag n) →
    IsRun 2 run → ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' :=
  fun _ _ hR => awake_stuck hR

/-- **The lost-wake-up program satisfies the same statement**: `Task.flagLive`'s
statement, for `Progs.flagLate n`, holds. So the Task does not detect the lost wake-up. -/
theorem flagLate_live (n : Nat) : ∀ run : Nat → FCfg, run 0 = finit (Futex.Progs.flagLate n) →
    IsRun 2 run → Fair 2 run → ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' :=
  fun _ _ hR _ => awake_stuck hR

/-- **Liveness of the event flag, sleepers never forced awake**: in every weakly
fair `IsRunAwake` run of the event flag, the waiter reaches a state where it is awake and cannot
step. -/
theorem flagLive_awake (n : Nat) : ∀ run : Nat → FCfg, run 0 = finit (Futex.Progs.flag n) →
    IsRunAwake 2 run → Fair 2 run → ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' :=
  Silmaril.Proofs.X86.Concurrency.Cir.FutexLive.flag_live_awake n

/-- `flagLive_awake` is not vacuous: a weakly fair `IsRunAwake` run of the event flag exists, and
in it the waiter's statement reaches `skip`. -/
theorem flag_awake_run (n : Nat) : ∃ run : Nat → FCfg,
    run 0 = finit (Futex.Progs.flag n) ∧ IsRunAwake 2 run ∧ Fair 2 run ∧
      ∃ k, ((run k).cfg.ts 1).1 = .skip :=
  Silmaril.Proofs.X86.Concurrency.Cir.FutexLive.NonVacuous.flag_awake_run n

/-- **The lost wake-up is a liveness failure** (every loop bound `m + 1`): some weakly fair
`IsRunAwake` run of `flagLate` has the waiter asleep from position `8` on, for ever. So
`flagLive_awake` fails for `flagLate`: it separates the correct flag from the buggy one. -/
theorem flagLate_sleeps (m : Nat) : ∃ run : Nat → FCfg,
    run 0 = finit (Futex.Progs.flagLate (m + 1)) ∧ IsRunAwake 2 run ∧ Fair 2 run ∧
      ∀ k, 8 ≤ k → (run k).sleep 1 = some Futex.Progs.flagW :=
  Silmaril.Proofs.X86.Concurrency.Cir.FutexLive.LateRun.flagLate_sleeps m

/-- The `flagLive_awake` statement is false for `flagLate` (every loop bound `m + 1`). -/
theorem not_flagLate_awake (m : Nat) : ¬ ∀ run : Nat → FCfg,
    run 0 = finit (Futex.Progs.flagLate (m + 1)) → IsRunAwake 2 run → Fair 2 run →
      ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C' :=
  Silmaril.Proofs.X86.Concurrency.Cir.FutexLive.LateRun.not_late_live m

end Silmaril.X86.Concurrency.Cir.Futex.Live
