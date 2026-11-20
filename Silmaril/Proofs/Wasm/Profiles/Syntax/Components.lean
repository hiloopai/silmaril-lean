module

public import Silmaril.Wasm.Profiles.Syntax.Components.Defs
import Silmaril.Wasm.Component.IntrinsicWiring.Lift.Thms

public section

namespace Silmaril.Proofs.Wasm.Profiles.Syntax.Components

open Silmaril.Wasm
open Silmaril.Wasm.Profiles.Syntax
open Component.Validation Component.IntrinsicWiring

theorem limeCheckedBodies {feat : Component.Features}
    {interface : Component.Types.ComponentType Nat Component.Engine.CoreExternType}
    (term : Closed feat lime1Profile Lime.scalarPayloadInterface interface) :
    ValidComponentLime1 feat
      (term.map Lime.eraseScalarPayload (fun checked => checked)).erase interface := by
  refine ⟨(term.map Lime.eraseScalarPayload (fun checked => checked)).sound, ?_⟩
  have erased := term.erase_map (targets := lime1ModuleType) Lime.eraseScalarPayload (fun checked => checked)
  have bodies : ∀ mod ∈ (term.erase.map Lime.eraseScalarPayload).coreModules, Lime1.Validation.ModuleValid mod := by
    intro mod mem
    obtain ⟨payload, _, rfl⟩ := List.mem_map.mp ((Component.Syntax.Component.coreModules_map
      Lime.eraseScalarPayload term.erase) ▸ mem)
    exact LimeScalar.moduleWitness.sound payload
  exact erased.symm ▸ bodies

end Silmaril.Proofs.Wasm.Profiles.Syntax.Components
