module

public import Silmaril.Wasm.Wac.EmitX.Defs
public import Silmaril.Wasm.JcoTool.RefSimple.Defs

/-!
# WAC packages that the reference machine runs as their algebra meaning

`Emit.binCompX S rd dflt b` reads the component a composition's bytes `b` denote in the algebra,
each package's meaning given by a package lowering `rd`. With `rd := RefSimple.rdRef`, a package
whose bytes are, in the reference syntax, the reference component `s.toRef` of a simple
component `s` in the soundness fragment (as `wasm-jco new --ref` writes them) means `s.toComp`,
and the reference machine (silmaril's instantiation and machine over Core 3.0) runs that
package as `s.toComp` (`RefSimple.rdRef_sound`, `Simple.sound`).

* `refComp S dflt b`: the component of a composition with these package meanings.

Theorems (`RefPkg.Thms`): `pkgMeaning_ref` (each leaf is `dflt`, or a package the reference
machine runs as its meaning) and `composeText_ref` (`wasm-wac compose --wasm` from WAC text and
package bytes: the component read off the output is the document's algebra term evaluated at
such leaves).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.RefPkg

open Silmaril.Wasm.Component (Comp)
open Silmaril.Wasm.Component.Reference (NumModule)

/-- **The component of a composition, packages read as simple components.** -/
def refComp (S : Nat → PkgSig) (dflt : Comp NumModule) (b : ByteArray) :
    Except String (Comp NumModule) :=
  Emit.binCompX S Silmaril.Wasm.JcoTool.RefSimple.rdRef dflt b

end Silmaril.Wasm.Wac.RefPkg
