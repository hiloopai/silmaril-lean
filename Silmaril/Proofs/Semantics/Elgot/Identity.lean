module

public import Silmaril.Semantics.Elgot.Defs
public import Silmaril.Proofs.Semantics.Elgot.Basic
import all Silmaril.Proofs.Semantics.Elgot.Basic
import Batteries.Tactic.Alias

/-!
# Identity: proofs

Proofs for `Silmaril.Semantics.Elgot.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot

universe u

private theorem not_nonempty_iterate_id : ¬ Nonempty (Iterate (Id : Type u → Type u)) := by
  rintro ⟨inst⟩
  let := inst
  exact PEmpty.elim (iter (m := Id) (A := PUnit.{u + 1}) (B := PEmpty.{u + 1})
    Sum.inr PUnit.unit)
alias _root_.Silmaril.Proofs.Semantics.Elgot.not_nonempty_iterate_id := Silmaril.Elgot.not_nonempty_iterate_id

end Silmaril.Elgot
