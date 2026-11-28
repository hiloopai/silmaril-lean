module

public import Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Defs
import Silmaril.Proofs.Logic.Temporal.TLA.ProofFrontEnd.Soundness

namespace Silmaril.Logic.Temporal.TLA.ProofFrontEnd

universe u

/-- Exact fact reuse and certified rule applications establish the denoted
judgment in every interpretation. -/
public theorem ExactCertificate.sound {V : Type u} {obligation : Obligation}
    (certificate : ExactCertificate obligation) (model : Interpretation V) :
    obligation.Valid model :=
  Proofs.Logic.Temporal.TLA.ProofFrontEnd.exact_sound certificate model

end Silmaril.Logic.Temporal.TLA.ProofFrontEnd
