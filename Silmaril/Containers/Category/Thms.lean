module

public import Silmaril.Containers.Category.Defs
public import Silmaril.Containers.Adapter.Thms

public section
namespace Silmaril.Containers.RuntimeCat
open CategoryTheory
variable {A B : RuntimeCat}

theorem Hom.sat (f : A ⟶ B) {i : A.Image} {φ : Spec B.Event}
    (h : (B.runtime.beh (f.loading.image i)).Sat φ) :
    (A.runtime.beh i).Sat (f.observe.pull φ) := fun b hb => h _ (f.simulates i b hb)

/-- UB reflection is an additional certificate obligation, not a consequence of simulation. -/
theorem Hom.noUB (f : A ⟶ B) (hf : f.observe.ReflectsNoUB) {i : A.Image}
    (h : (B.runtime.beh (f.loading.image i)).Sat Spec.noUB) :
    (A.runtime.beh i).Sat Spec.noUB := fun b hb => hf b (h _ (f.simulates i b hb))

end Silmaril.Containers.RuntimeCat
