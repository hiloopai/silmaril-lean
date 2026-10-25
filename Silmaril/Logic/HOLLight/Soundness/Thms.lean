module

public import Silmaril.Logic.HOLLight.Soundness.Defs
import Silmaril.Proofs.Logic.HOLLight.Soundness

@[expose] public section

/-! # Soundness of the HOL Light inference rules

A derivation is valid in every supplied model satisfying its explicit object
theory, at every type valuation and free-term valuation. The constructed model
and consistency theorem are provided separately by `HOLLight.Consistency`.
-/

namespace Silmaril.Logic.HOLLight

universe u

theorem Derives.sound {sig : Signature} {theory : Theory} {H : Hyps} {p : Tm}
    (proof : Derives sig theory H p) (M : Model.{u} sig) (model : Models M theory) :
    Entails M H p :=
  Silmaril.Proofs.Logic.HOLLight.derives_sound proof M model

end Silmaril.Logic.HOLLight
