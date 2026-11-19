module

public import Silmaril.Containers.Adapter.Examples.Defs
public import Silmaril.Containers.Runtime.Thms

public section
namespace Silmaril.Proofs.Containers.Adapter.Examples
open Silmaril.Containers Silmaril.Containers.Adapter.Examples

theorem abstract_safe :
    (abstractRuntime.beh manifest).Sat (fun b => Spec.noUB b ∧ b = .done [] (.exited 0)) := by
  intro b hb
  have hl : abstractRuntime.load manifest = .ok (.exit 0) := rfl
  obtain ⟨b₀, hs, ho⟩ := (Runtime.beh_ok hl b).mp hb
  change b₀ = .done [] (.exited 0) at hs
  change b₀ = b at ho
  have he : b = .done [] (.exited 0) := ho.symm.trans hs
  rw [he]
  exact ⟨trivial, rfl⟩

theorem toy_certificate : toyExecutor.Certificate := by
  constructor
  · exact ⟨true, trivial⟩
  · intro _ _; exact ⟨false, (), trivial⟩
  · intro _ _; trivial
  · intro g _ _ _ _; exact ⟨g, rfl⟩
  · intro g h c _ _
    exact ⟨.done [] (.exited (if g then 0 else 1)), _, rfl, rfl⟩
  · intro g h c _ _ b hb
    obtain ⟨_, rfl, rfl⟩ := hb
    trivial
  · intro g h c _ _ b hb
    obtain ⟨_, rfl, rfl⟩ := hb
    rfl

end Silmaril.Proofs.Containers.Adapter.Examples
