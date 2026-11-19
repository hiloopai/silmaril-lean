module

public import Silmaril.Containers.Behaviour.Defs

/-! # Experimental observation adapters

Adapters act on whole behaviours. A stateful decoder may accumulate bytes and change the
number of events; it must also account for blocking, divergence and infinite observations.
`ReflectsNoUB` is deliberately separate from semantic simulation: masking a fault can preserve
a permissive refinement while destroying the right to certify the source. -/

@[expose] public section
namespace Silmaril.Containers

/-- An explicit observation map; not limited to renaming individual letters. -/
@[ext] structure Adapter (E F : Type) where
  run : Beh E → Beh F

namespace Adapter
variable {E F G : Type}

def id : Adapter E E := ⟨_root_.id⟩
def comp (f : Adapter E F) (g : Adapter F G) : Adapter E G := ⟨g.run ∘ f.run⟩
def pull (f : Adapter E F) (φ : Spec F) : Spec E := φ ∘ f.run
/-- The direct image includes every source run, faults included. -/
def image (f : Adapter E F) (M : Model E) : Model F := fun c => ∃ b, M b ∧ f.run b = c
/-- A certificate on the observed run can exclude UB in the source. -/
def ReflectsNoUB (f : Adapter E F) : Prop := ∀ b, Spec.noUB (f.run b) → Spec.noUB b
/-- The observation map does not introduce UB. This is the other direction. -/
def PreservesNoUB (f : Adapter E F) : Prop := ∀ b, Spec.noUB b → Spec.noUB (f.run b)

/-- UB-to-crash on the existing full behaviour type, retaining every emitted event. -/
def maskUB (signal : Nat) : Adapter E E := ⟨fun b => match b with
  | .done t (.undefined _) => .done t (.signaled signal)
  | _ => b⟩

end Adapter
end Silmaril.Containers
