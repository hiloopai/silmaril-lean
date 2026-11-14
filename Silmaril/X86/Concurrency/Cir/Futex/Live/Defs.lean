module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs
public import Silmaril.X86.Concurrency.Cir.Futex.Progs.Defs

/-!
# Futex liveness under fairness: the statement

The axiomatic futex semantics (`Cir.Futex`) is about finite
executions: a blocked waiter is a trace that stops, and a lost wake-up is a final state
(queue byte `1` after a blocked waiter). Whether a waiter is *eventually* woken is a liveness
property, so it needs infinite runs, a kernel that really puts threads to sleep, and fairness.

This module states it on the SC interleaving machine (`Csl.ScStep`, CIR's small steps over a
cell heap), extended with an explicit futex **sleep map** (`FCfg.sleep`):

* `again`: a wait whose check finds a different value returns at once (EAGAIN);
* `sleep`: a wait whose check finds the expected value puts the thread to sleep on the word, in
  the same step (the kernel checks and enqueues under the bucket lock);
* `wake`: a wake with `n > 0` wakes every thread sleeping on the word (exact when at most `n`
  threads sleep there, as in the event-flag test);
* `spurious`: a sleeping thread may wake by itself (Linux allows it); fairness never forces it.

A thread is **enabled** when it is awake and can step. A run is **fair** when every thread that
is enabled from some point on takes a step after that point. `Task.flagLive` says that in every
fair run of the event flag, the waiter reaches a state where it is awake and cannot step: it
has finished, or it has used up the CIR loop bound (spurious wake-ups can exhaust any bound).
It is proved for every `n` in `Futex.Live.Thms`.

Scope: SC only. Under TSO or XL the same statement needs the store-buffer machine and a
fairness condition on buffer flushes; this is not stated here.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Futex.Live

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-- A futex label. -/
def _root_.Silmaril.X86.Concurrency.Cir.Lab.isFutex : Lab → Bool
  | .fwait .. | .fwake .. | .fblock .. => true
  | _ => false

/-- A configuration with a futex sleep map: the word each thread sleeps on, if any. -/
structure FCfg where
  cfg : Cfg
  sleep : Nat → Option Nat

/-- The configuration after thread `t` steps to `(s', rs')`. -/
def FCfg.move (C : FCfg) (t : Nat) (s' : Stmt) (rs' : Regs) : Cfg := ⟨upd C.cfg.ts t (s', rs'), C.cfg.mem⟩

/-- **Steps of thread `t`** (SC, with a futex kernel). -/
inductive FStep (N : Nat) : FCfg → Nat → FCfg → Prop
  | tau {C t s' rs'} (ht : t < N) (hw : C.sleep t = none)
      (hs : TStep (C.cfg.ts t).1 (C.cfg.ts t).2 none s' rs') :
      FStep N C t ⟨C.move t s' rs', C.sleep⟩
  | lab {C t l s' rs'} (ht : t < N) (hw : C.sleep t = none)
      (hs : TStep (C.cfg.ts t).1 (C.cfg.ts t).2 (some l) s' rs') (hm : l.isMem = true)
      (hf : l.isFutex = false) (hc : ∀ a, l.Touches a → (C.cfg.mem a).isSome) (hok : l.okH C.cfg.mem) :
      FStep N C t ⟨⟨upd C.cfg.ts t (s', rs'), l.updH C.cfg.mem⟩, C.sleep⟩
  /-- The check finds another value: return `EAGAIN`. -/
  | again {C t a e seen r s' rs'} (ht : t < N) (hw : C.sleep t = none)
      (hs : TStep (C.cfg.ts t).1 (C.cfg.ts t).2 (some (.fwait a e seen r)) s' rs') (hne : seen ≠ e)
      (hok : C.cfg.mem a = some seen) :
      FStep N C t ⟨C.move t s' rs', C.sleep⟩
  /-- The check finds the expected value: go to sleep on `a` (returning `0` once awake). -/
  | sleep {C t a e r s' rs'} (ht : t < N) (hw : C.sleep t = none)
      (hs : TStep (C.cfg.ts t).1 (C.cfg.ts t).2 (some (.fwait a e e r)) s' rs')
      (hok : C.cfg.mem a = some e) :
      FStep N C t ⟨C.move t s' rs', upd C.sleep t (some a)⟩
  /-- Wake every thread sleeping on `a` (if `n > 0`). -/
  | wake {C t a n q s' rs'} (ht : t < N) (hw : C.sleep t = none)
      (hs : TStep (C.cfg.ts t).1 (C.cfg.ts t).2 (some (.fwake a n q)) s' rs')
      (hc : (C.cfg.mem a).isSome) :
      FStep N C t ⟨C.move t s' rs', fun u => if 0 < n ∧ C.sleep u = some a then none else C.sleep u⟩
  /-- A spurious wake-up. -/
  | spurious {C t a} (ht : t < N) (hw : C.sleep t = some a) :
      FStep N C t ⟨C.cfg, upd C.sleep t none⟩

/-- Thread `t` is awake and can step. -/
def Enabled (N : Nat) (C : FCfg) (t : Nat) : Prop := C.sleep t = none ∧ ∃ C', FStep N C t C'

/-- A maximal run: every position steps, or nothing can step and the run stays. -/
def IsRun (N : Nat) (run : Nat → FCfg) : Prop :=
  ∀ k, (∃ t, FStep N (run k) t (run (k + 1))) ∨
    ((∀ t C', ¬ FStep N (run k) t C') ∧ run (k + 1) = run k)

/-- A maximal run **without forced spurious wake-ups**: every position
is a step of an awake thread, or no awake thread can step and the run stays. A sleeper is never
forced to wake by maximality (in `IsRun`, a configuration where only sleepers remain must take a
spurious wake-up, which makes `Task.flagLive` hold for every program). -/
def IsRunAwake (N : Nat) (run : Nat → FCfg) : Prop :=
  ∀ k, (∃ t, (run k).sleep t = none ∧ FStep N (run k) t (run (k + 1))) ∨
    ((∀ t C', (run k).sleep t = none → ¬ FStep N (run k) t C') ∧ run (k + 1) = run k)

/-- **Weak fairness**: a thread enabled from some point on steps after that point. -/
def Fair (N : Nat) (run : Nat → FCfg) : Prop :=
  ∀ t < N, ∀ k, (∀ j, k ≤ j → Enabled N (run j) t) → ∃ j, k ≤ j ∧ FStep N (run j) t (run (j + 1))

/-- The initial configuration of a program: nobody sleeps. -/
def finit (P : Prog) : FCfg := ⟨progInit P, fun _ => none⟩

/-- **Liveness of the event flag under fairness**. In every fair run of `Progs.flag n`
under SC with a futex kernel, the waiter (thread `1`) reaches a state where it is awake and
cannot step: it has finished, or (after `n` wake-ups) used up its CIR loop bound. PROVED for
every `n` as `Futex.Live.flagLive` (`Futex.Live.Thms`), along the plan below; the
measure is on statements only (`msr`, decreased by every thread step), so a thread enabled for
ever contradicts fairness, and the invariant carries the SC Dekker step (once the flag is `1`
the waiter's `sleep` check fails).

Plan: thread `0` has three labels and never sleeps, so by fairness it finishes; after its
`wake`, the waiter is awake unless it went to sleep later, which `sleep`'s check excludes
(memory then holds `flag = 1`: the SC form of `Exec.futex_dekker_xl`). An awake waiter is
enabled until it finishes or is stuck at the bound, so by fairness it steps; each loop
iteration after `flag = 1` exits. A well-founded measure on (thread `0`'s remaining labels,
the waiter's remaining loop bound, its position) decreases along the fair run's relevant
steps.

**This statement is weak.** In an `IsRun` run a configuration where only sleepers
can move must take a spurious wake-up, and every step decreases a measure, so the conclusion
holds for every maximal run of every two-thread program, fair or not (`Futex.Live.awake_stuck`),
including the lost-wake-up program `flagLate` (`Futex.Live.flagLate_live`). The separating
statement is `Futex.Live.flagLive_awake`, over `IsRunAwake` runs. -/
def Task.flagLive (n : Nat) : Prop :=
  ∀ run : Nat → FCfg, run 0 = finit (Progs.flag n) → IsRun 2 run → Fair 2 run →
    ∃ k, (run k).sleep 1 = none ∧ ∀ C', ¬ FStep 2 (run k) 1 C'

end Silmaril.X86.Concurrency.Cir.Futex.Live
