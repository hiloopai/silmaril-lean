module

public import Silmaril.Machine.SqliteRead.Defs
import Silmaril.Proofs.Machine.SqliteRead.Contract

@[expose] public section

namespace Silmaril.Machine.SqliteRead

open Behaviour Observable

theorem status_roundtrip (code : BitVec 32) : (Status.ofCode code).code = code :=
  Proofs.Machine.SqliteRead.status_roundtrip code

theorem safe_iff_admitted (env : Context) (req : Request) :
    Safe ((contract env).spec req) ↔ env.Admits req :=
  Proofs.Machine.SqliteRead.safe_iff_admitted env req

theorem dispatch_only {env : Context} {req : Request} {obs : Obs}
    (safe : Safe ((contract env).spec req)) (run : obs ∈ (contract env).spec req) :
    obs = dispatch req :=
  Proofs.Machine.SqliteRead.dispatch_only safe run

theorem ub_is_top {env : Context} {req : Request} (invalid : ¬ env.Admits req) :
    close .forbidden ((contract env).spec req) = Set.univ :=
  close_eq_univ (by rw [Observable.Contract.spec_of_not_pre invalid]; rfl)

/-- On a short read, the entire unread suffix is initialized to zero and the
caller-visible bytes outside the request are unchanged. -/
theorem short_read {snapshot : List (BitVec 8)} {req : Request} {before after : BufferView}
    (result : Handler snapshot req before after .shortRead) :
    Framed req before after ∧ ∀ index, (available snapshot req).length ≤ index →
      index < req.amount.toNat → after (req.buffer.toNat + index) = some 0 :=
  Proofs.Machine.SqliteRead.short_read result

end Silmaril.Machine.SqliteRead
