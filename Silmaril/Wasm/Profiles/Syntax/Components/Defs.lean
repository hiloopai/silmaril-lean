module

public import Silmaril.Wasm.Profiles.Syntax.LimeScalar.Thms
public import Silmaril.Wasm.Component.IntrinsicWiring.Lift.Defs

@[expose] public section

namespace Silmaril.Wasm.Profiles.Syntax

open Component (Features)
open Component.Validation

/-- The reference Core 3.0 component judgment, including validity of the embedded modules. -/
def Core.componentSyntax (feat : Features) : Family :=
  ⟨Component.Syntax.Component Wasm.Module, Component.Types.ComponentType Nat Core3Extern,
    ValidComponentCore3 feat⟩

/-- The reference native Lime judgment, not just the interface-only executable checker. -/
def Lime.componentSyntax (feat : Features) : Family :=
  ⟨Component.Syntax.Component Lime1.Module,
    Component.Types.ComponentType Nat Component.Engine.CoreExternType, ValidComponentLime1 feat⟩

def Lime.eraseScalarPayload (mod : LimeScalar.moduleWitness.Typed ()) : Lime1.Module :=
  LimeScalar.moduleWitness.erase mod

/-- At each payload declaration, compute the actual named interface of the
erased native witness. The witness separately guarantees native body validity. -/
def Lime.scalarPayloadInterface (mod : LimeScalar.moduleWitness.Typed ()) :=
  lime1ModuleType (Lime.eraseScalarPayload mod)

end Silmaril.Wasm.Profiles.Syntax
