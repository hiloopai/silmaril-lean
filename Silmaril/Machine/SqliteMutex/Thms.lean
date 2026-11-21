module

public import Silmaril.Machine.SqliteMutex.Defs
import Silmaril.Proofs.Machine.SqliteMutex.Contract

@[expose] public section

namespace Silmaril.Machine.SqliteMutex

open Behaviour Observable

theorem safe_iff_admitted (env : Context) (mutex : Handle) :
    Safe ((contract env).spec mutex) ↔ env.Admits mutex :=
  Proofs.Machine.SqliteMutex.safe_iff_admitted env mutex

/-- A defined run returns silently on null or dispatches exactly one release
for a live mutex owned by the caller. No handler return is assumed. -/
theorem release_only {env : Context} {mutex : Handle} {obs : Obs}
    (safe : Safe ((contract env).spec mutex)) (run : obs ∈ (contract env).spec mutex) :
    (mutex = 0#64 ∧ obs = ⟨[], .returned .callerReturn⟩) ∨
    (mutex ≠ 0#64 ∧ env.live mutex ∧ env.ownedByCaller mutex ∧ env.leaveInstalled ∧
      obs = ⟨[.leave mutex], .returned .handlerEntry⟩) :=
  Proofs.Machine.SqliteMutex.release_only safe run

theorem ub_is_top {env : Context} {mutex : Handle} (invalid : ¬ env.Admits mutex) :
    close .forbidden ((contract env).spec mutex) = Set.univ :=
  close_eq_univ (by rw [Observable.Contract.spec_of_not_pre invalid]; rfl)

end Silmaril.Machine.SqliteMutex
