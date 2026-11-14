module

public import Silmaril.Process.Mt.Pthread.Defs

/-!
# Proofs: sanity checks of the POSIX thread specifications

The proofs of `Silmaril.Process.Mt.Pthread.Thms` (by unfolding the specifications).
-/

@[expose] public section

namespace Silmaril.Process.Mt.Pthread.Proofs.Sanity


theorem normal_relock_deadlocks {t a r : Nat} {m m' : PSt} (hk : (m.mtx a).kind = .normal)
    (ho : (m.mtx a).owner = some t) : ¬ mutexLock.step t [a] m r m' := by
  simp [mutexLock, arg, ho, hk]

theorem errorcheck_relock {t a r : Nat} {m m' : PSt} (hk : (m.mtx a).kind = .errorcheck)
    (ho : (m.mtx a).owner = some t) : mutexLock.step t [a] m r m' ↔ r = EDEADLK ∧ m' = m := by
  simp [mutexLock, arg, ho, hk]

theorem recursive_relock {t a : Nat} {m : PSt} (hk : (m.mtx a).kind = .recursive)
    (ho : (m.mtx a).owner = some t) (hd : (m.mtx a).depth < depthMax) :
    mutexLock.step t [a] m 0
      { m with mtx := set m.mtx a { m.mtx a with depth := (m.mtx a).depth + 1 } } := by
  simp [mutexLock, arg, ho, hk, hd]

theorem trylock_busy {t u a : Nat} {m : PSt} (hk : (m.mtx a).kind = .normal)
    (ho : (m.mtx a).owner = some u) : mutexTrylock.step t [a] m EBUSY m := by
  simp [mutexTrylock, arg, ho, hk, EBUSY]

theorem lock_owner {t a r : Nat} {m m' : PSt} (h : mutexLock.step t [a] m r m') (hr : r = 0) :
    (m'.mtx a).owner = some t := by
  simp only [mutexLock, arg, List.getD_cons_zero] at h
  rcases h with ⟨-, -, rfl⟩ | ⟨ho, -, -, -, rfl⟩ | ⟨-, -, -, e, -⟩ | ⟨-, -, e, -⟩
  · simp [set, MutexSt.take]
  · simp [set, ho]
  · subst hr; simp [EAGAIN] at e
  · subst hr; simp [EDEADLK] at e

theorem unlock_normal_ub {t a : Nat} {m : PSt} (hk : (m.mtx a).kind = .normal)
    (ho : (m.mtx a).owner ≠ some t) : mutexUnlock.fault t [a] m := ⟨hk, ho⟩

theorem unlock_errorcheck_eperm {t a : Nat} {m : PSt} (hk : (m.mtx a).kind = .errorcheck)
    (ho : (m.mtx a).owner ≠ some t) : mutexUnlock.step t [a] m EPERM m := by
  simp [mutexUnlock, arg, ho, hk]

theorem condWait_releases {t c a : Nat} {m m' : PSt} (h : condWait.step t [c, a] m 0 m') :
    (m'.mtx a).owner = none ∧ t ∈ m'.cnd c := by
  simp only [condWait, arg, List.getD_cons_zero, List.getD_cons_succ] at h
  rcases h with ⟨-, hd, -, rfl⟩ | ⟨-, -, e, -⟩
  · simp [set, MutexSt.drop, hd]
  · simp [EPERM] at e

theorem condResume_needs_free {t c a r : Nat} {m m' : PSt}
    (h : condResume.step t [c, a] m r m') :
    (m.mtx a).owner = none ∧ (m'.mtx a).owner = some t := by
  simp only [condResume, arg, List.getD_cons_zero, List.getD_cons_succ] at h
  obtain ⟨ho, -, rfl⟩ := h
  exact ⟨ho, by simp [set, MutexSt.take]⟩

theorem semWait_blocks {t s r : Nat} {m m' : PSt} (h0 : m.sem s = some 0) :
    ¬ semWait.step t [s] m r m' := by
  simp [semWait, arg, h0]

theorem semTrywait_eagain {t s : Nat} {m : PSt} (h0 : m.sem s = some 0) :
    semTrywait.step t [s] m EAGAIN m := by
  simp [semTrywait, arg, h0]

theorem once_claim {t o : Nat} {m m' : PSt} (h : onceBegin.step t [o] m 1 m') :
    m.once o = .init ∧ m'.once o = .running t := by
  simp only [onceBegin, arg, List.getD_cons_zero] at h
  rcases h with ⟨-, e, -⟩ | ⟨hi, -, rfl⟩
  · cases e
  · exact ⟨hi, by simp [set]⟩

theorem barrier_last {t b : Nat} {m : PSt}
    (hc : ((m.bar b).waiting.length + 1 = (m.bar b).count)) :
    barArrive.step t [b] m serialThread
      { m with bar := set m.bar b { m.bar b with waiting := [] } } := by
  simp [barArrive, arg, hc]

theorem join_self {t : Nat} {m : PSt} : join.step t [t] m EDEADLK m := by
  simp [join, arg]

theorem join_running_blocks {t u r : Nat} {m m' : PSt} (hu : u ≠ t)
    (hr : ∀ e, m.thr u = some e → e.life = .running) : ¬ join.step t [u] m r m' := by
  simp only [join, arg, List.getD_cons_zero]
  rintro (⟨e, -⟩ | ⟨-, -, v, hv, -⟩)
  · exact hu e
  · have := hr _ hv; cases this

end Silmaril.Process.Mt.Pthread.Proofs.Sanity
