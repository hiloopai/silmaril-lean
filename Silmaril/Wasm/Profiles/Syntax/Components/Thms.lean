module

public import Silmaril.Wasm.Profiles.Syntax.Components.Defs
public import Silmaril.Wasm.Component.IntrinsicWiring.Lift.Thms
import Silmaril.Proofs.Wasm.Profiles.Syntax.Components
import Silmaril.Wasm.Component.Reference.Validation.Defs.Thms

@[expose] public section

namespace Silmaril.Wasm.Profiles.Syntax

open Component (Features)
open Component.Validation Component.IntrinsicWiring

/-- Reference-checked Core payloads and scope-indexed flat wiring. This is
not a completeness assertion for arbitrary checked component definitions. -/
def Core.componentWitness (feat : Features) : Intrinsic (Core.componentSyntax feat) :=
  ⟨Closed feat core3Profile core3ModuleType?, Closed.erase,
    fun term => validComponentCore3_iff.mpr term.sound⟩

theorem Lime.scalarWiring_sound {feat : Features}
    {interface : Component.Types.ComponentType Nat Component.Engine.CoreExternType}
    (term : Closed feat lime1Profile Lime.scalarPayloadInterface interface) :
    ValidComponentLime1 feat (term.map Lime.eraseScalarPayload (fun checked => checked)).erase interface :=
  Proofs.Wasm.Profiles.Syntax.Components.limeCheckedBodies term

/-- Flat Lime wiring with native intrinsic scalar module payloads. Erasure
establishes the full reference judgment, including validity of every body. -/
def Lime.componentWitness (feat : Features) : Intrinsic (Lime.componentSyntax feat) :=
  ⟨Closed feat lime1Profile Lime.scalarPayloadInterface,
    fun term => (term.map Lime.eraseScalarPayload (fun checked => checked)).erase,
    Lime.scalarWiring_sound⟩

/-- Erasing the module bodies before or after erasing the typed wiring gives
exactly the same reference AST at the same named component interface. -/
theorem Lime.componentWitness_erase {feat : Features} {interface : (Lime.componentSyntax feat).Index}
    (term : Closed feat lime1Profile Lime.scalarPayloadInterface interface) :
    (Lime.componentWitness feat).erase term =
      term.erase.map Lime.eraseScalarPayload :=
  term.erase_map Lime.eraseScalarPayload (fun checked => checked)

end Silmaril.Wasm.Profiles.Syntax
