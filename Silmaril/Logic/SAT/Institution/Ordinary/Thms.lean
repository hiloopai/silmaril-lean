module

public import Silmaril.Logic.SAT.Institution.Ordinary.Defs

@[expose] public section

namespace Silmaril.Logic.SAT.Institution

universe u v
variable {A : Type u} {B : Type v}

open CategoryTheory Set

theorem kleeneTruthInstitution_sat_iff_evalK3Option (v : PartialValuation A) (F : Problem A) :
    (kleeneTruthInstitution.obj A).Sat (Discrete.mk v) F ↔ F.evalK3Option v = some true :=
  (toOptionBool_eq_some_iff _ _).symm

theorem kleeneRefutationInstitution_sat_iff_evalK3Option (v : PartialValuation A) (F : Problem A) :
    (kleeneRefutationInstitution.obj A).Sat (Discrete.mk v) F ↔ F.evalK3Option v = some false :=
  (toOptionBool_eq_some_iff _ _).symm

/-- Target completions reduce into the source completion family. -/
theorem completion_reduct_image_subset (f : A → B) (v : PartialValuation B) :
    reduct f '' {t | Completes v t} ⊆ {s | Completes (reduct f v) s} :=
  fun {_} ⟨_, ht, h⟩ => h ▸ completes_reduct f ht

/-- Coverage makes the reduct image the entire source completion family. -/
theorem completion_reduct_image_eq_of_coverage (f : A → B) (v : PartialValuation B)
    (covers : CompletionCovers f v) :
    reduct f '' {t | Completes v t} = {s | Completes (reduct f v) s} :=
  Subset.antisymm (completion_reduct_image_subset f v) (fun {s} hs => covers s hs)

end Silmaril.Logic.SAT.Institution
