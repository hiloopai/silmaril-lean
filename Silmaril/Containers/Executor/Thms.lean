module

public import Silmaril.Containers.Executor.Defs

public section
namespace Silmaril.Containers.Executor
variable {G H C P E F : Type}

/-- Reuse a linked guest specification. Source noHostUB comes from its own obligation, so
an observation adapter cannot certify the executor by masking its faults. -/
theorem Certificate.sat {x : Executor G H C P E F} (cert : x.Certificate)
    {g h c} (hg : x.supported g) (hc : x.admits g h c) {φ : Spec F}
    (sat : (x.linked g h c).Sat φ) :
    (x.runtime.beh (g, h, c)).Sat (fun b => Spec.noUB b ∧ φ (x.observe.run b)) :=
  fun b hb => ⟨cert.noHostUB g h c hg hc b hb, sat _ (cert.simulates g h c hg hc b hb)⟩

end Silmaril.Containers.Executor
