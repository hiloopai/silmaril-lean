module

public import Silmaril.Machine.SqliteRead.Defs

public section

namespace Silmaril.Proofs.Machine.SqliteRead

open Silmaril.Machine SqliteRead Behaviour Observable

theorem status_roundtrip (code : BitVec 32) : (Status.ofCode code).code = code := by
  unfold Status.ofCode
  split
  · rename_i zero
    exact zero.symm
  · split <;> rename_i short
    · exact short.symm
    · rfl

theorem safe_iff_admitted (env : Context) (req : Request) :
    Safe ((contract env).spec req) ↔ env.Admits req := by
  constructor
  · intro safe
    by_contra invalid
    exact safe [] (by rw [Observable.Contract.spec_of_not_pre invalid]; rfl)
  · intro admitted trace
    rw [Observable.Contract.spec_of_pre admitted]
    change ¬ (⟨trace, .undefined⟩ : Obs) = dispatch req
    simp [dispatch]

theorem dispatch_only {env : Context} {req : Request} {obs : Obs}
    (safe : Safe ((contract env).spec req)) (run : obs ∈ (contract env).spec req) : obs = dispatch req := by
  rw [Observable.Contract.spec_of_pre ((safe_iff_admitted _ _).mp safe)] at run
  exact run

theorem short_read {snapshot : List (BitVec 8)} {req : Request} {before after : BufferView}
    (result : Handler snapshot req before after .shortRead) :
    Framed req before after ∧ ∀ index, (available snapshot req).length ≤ index →
      index < req.amount.toNat → after (req.buffer.toNat + index) = some 0 := by
  obtain ⟨frame, short, writes⟩ := result
  refine ⟨frame, fun index lower upper => ?_⟩
  have bound : index < ((available snapshot req) ++
      List.replicate (req.amount.toNat - (available snapshot req).length) (0 : BitVec 8)).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [writes index bound, List.getElem?_append_right lower, List.getElem?_replicate_of_lt (by omega)]

end Silmaril.Proofs.Machine.SqliteRead
