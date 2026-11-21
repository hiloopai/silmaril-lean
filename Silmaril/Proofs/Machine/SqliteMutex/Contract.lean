module

public import Silmaril.Machine.SqliteMutex.Defs

public section

namespace Silmaril.Proofs.Machine.SqliteMutex

open Silmaril.Machine SqliteMutex Behaviour Observable

theorem safe_iff_admitted (env : Context) (mutex : Handle) :
    Safe ((contract env).spec mutex) ↔ env.Admits mutex := by
  constructor
  · intro safe
    by_contra invalid
    exact safe [] (by rw [Observable.Contract.spec_of_not_pre invalid]; rfl)
  · intro admitted trace
    rw [Observable.Contract.spec_of_pre admitted]
    change ¬ (⟨trace, .undefined⟩ : Obs) = candidate mutex
    by_cases isNull : mutex = 0#64 <;> simp [candidate, isNull]

theorem release_only {env : Context} {mutex : Handle} {obs : Obs}
    (safe : Safe ((contract env).spec mutex)) (run : obs ∈ (contract env).spec mutex) :
    (mutex = 0#64 ∧ obs = ⟨[], .returned .callerReturn⟩) ∨
    (mutex ≠ 0#64 ∧ env.live mutex ∧ env.ownedByCaller mutex ∧ env.leaveInstalled ∧
      obs = ⟨[.leave mutex], .returned .handlerEntry⟩) := by
  have admitted := (safe_iff_admitted env mutex).mp safe
  rw [Observable.Contract.spec_of_pre admitted] at run
  change obs = candidate mutex at run
  by_cases isNull : mutex = 0#64
  · exact Or.inl ⟨isNull, by simpa [candidate, isNull] using run⟩
  · obtain ⟨live, owned, installed⟩ := admitted.resolve_left isNull
    exact Or.inr ⟨isNull, live, owned, installed, by simpa [candidate, isNull] using run⟩

end Silmaril.Proofs.Machine.SqliteMutex
