module

public import Silmaril.Wasm.Component.Reference.WIT.Defs

public import Silmaril.Wasm.Types

/-!
# WIT value types

A structural presentation of the value-type families in the Component Model
WIT design. Named references and nominal resource identities are parameters;
`ClosedType` is the reference-free input used by the canonical ABI. This is not
a WIT text parser or a package-name resolver.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

universe u v

end Silmaril.Wasm.Component.WIT
