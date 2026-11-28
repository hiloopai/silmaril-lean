module

public import Silmaril.Logic.SAT.Institution.Generalized.Thms
import Silmaril.Proofs.Logic.SAT.Institution.Examples

@[expose] public section

namespace Silmaril.Logic.SAT.Institution.Examples

open CategoryTheory Silmaril.Logic.ManyValued

/-- Identifying the two atoms of `p ∨ ¬q` removes every falsifying completion.
The resulting `p ∨ ¬p` still evaluates to unknown compositionally at an unknown atom. -/
theorem identification_counterexample :
    let F : Problem Bool := [[⟨false, true⟩, ⟨true, false⟩]]
    let f : Bool → Unit := fun _ => ()
    ¬ Function.Injective f ∧
      F.superEval (reduct f (fun _ => none)) = none ∧
      (F.rename f).superEval (fun _ => none) = some true ∧
      (F.rename f).evalK3 (fun _ => K3.unknown) = K3.unknown ∧
      (F.rename f).evalK3Option (fun _ => none) = none :=
  Proofs.Logic.SAT.Institution.identification_counterexample

/-- A one-atom problem preserves a conflict as well as a gap in evidence. -/
theorem conflict_and_gap :
    let F : Problem Unit := [[⟨(), true⟩]]
    F.evalEvidence (fun _ => FDE.both) = FDE.both ∧
      F.evalEvidence (fun _ => FDE.neither) = FDE.neither := ⟨rfl, rfl⟩

/-- A negative literal agrees across the typed and legacy boundaries. FDE can also
carry conflicting evidence through that literal. -/
theorem typed_and_legacy :
    let F : Problem Unit := [[⟨(), false⟩]]
    let v : PartialValuation Unit := fun _ => some false
    kleeneExact.eval Unit (Discrete.mk v) F = K3.ofBool true ∧
      F.evalK3Option v = some true ∧
      evidenceExact.eval Unit (Discrete.mk (fun _ => FDE.both)) F = FDE.both :=
  ⟨rfl, rfl, rfl⟩

end Silmaril.Logic.SAT.Institution.Examples
