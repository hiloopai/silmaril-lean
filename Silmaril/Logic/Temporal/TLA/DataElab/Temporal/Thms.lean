module

public import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Defs
public import Silmaril.Logic.Temporal.TLA.Thms

namespace Silmaril.Logic.Temporal.TLA.DataElab.Temporal

public section

universe u

variable {V : Type u} {signature : ExternalSignature} {fragment : Fragment}
    (I : Interpretation V signature fragment) (ρ : RigidEnv V)
    (p : Predicate signature fragment) (obs : Observation signature fragment) (s t : State V)

theorem unchanged_iff :
    (Predicate.unchanged obs).toAction I ρ s t ↔ obs.eval I ρ t = obs.eval I ρ s :=
  I.booleans.holds_ofProp _

theorem square_iff :
    (p.bracket .square obs).toAction I ρ s t ↔ p.toAction I ρ s t ∨ obs.eval I ρ t = obs.eval I ρ s :=
  I.booleans.holds_ofProp _

theorem angle_iff :
    (p.bracket .angle obs).toAction I ρ s t ↔ p.toAction I ρ s t ∧ obs.eval I ρ t ≠ obs.eval I ρ s :=
  I.booleans.holds_ofProp _

/-- ENABLED uses an independent successor over all flexible assignments. -/
theorem enabled_iff : p.enabled.toStatePred I ρ s ↔ ∃ t, p.toAction I ρ s t :=
  I.booleans.holds_ofProp _

theorem CheckedFormula.sat_stutterInvariant (formula : CheckedFormula signature fragment) :
    StutterInvariant (formula.toFormula I ρ).Sat :=
  (formula.toFormula I ρ).sat_stutterInvariant

end
end Silmaril.Logic.Temporal.TLA.DataElab.Temporal
