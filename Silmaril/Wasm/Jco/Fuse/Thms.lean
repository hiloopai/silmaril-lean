module

public import Silmaril.Wasm.Jco.Fuse.Defs
public import Silmaril.Wasm.Jco.Fuse.Glue.Thms
import Silmaril.Proofs.Wasm.Jco.Fuse.Basic

/-!
# Fusing an adaptor and a core module: correctness

* `wrapper_adaptor`: **the wrapper-style single component denotes as the
  adaptor-style component** — for every core semantics `C`, the component
  with one instance of the fused module `JMod.fused m g` (semantics
  `fuseSem C`) and the component with an instance of `m` and an instance of
  the adaptor `g` (semantics `baseSem C`) have the same denotation, provided
  the import wiring is complete (`args.length` is the number of `m`'s imports)
  and scoped (it only calls the component's imports), the adaptor imports at
  most `m`'s exports, and the world exports at most the adaptor's.
* `simpleWrapper_simpleComp`: the same for the simple FFI style
  (`simpleAdaptor`, `simpleImports`), with no hypotheses.
* `fuseSem_fused`: the single core module behaves as the linking of `m` and
  the adaptor (the definition of `fuseSem`, restated).

The proof (`Silmaril.Proofs.Wasm.Jco.Fuse.Basic`) goes through the nested
component that has one instance of the two-instance component `inner m g`:
the fused instance is that nested instance, and flattening it
(`denU_flatten'`) gives the adaptor-style component.
-/

public section

namespace Silmaril.Wasm.Jco.Fuse

open Silmaril.Games
open Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- **Fusion is correct.** -/
theorem wrapper_adaptor (C : CoreSem M) (I W : Iface) (m : M) (g : Glue) (args : List Impl)
    (hlen : args.length = (CoreModule.imports m).length) (hsc : ScopedList I.length args)
    (hg : g.imports.length ≤ (CoreModule.exports m).length) (hW : W.length ≤ g.exports.length) :
    (wrapperComp I W m g args).denU (fuseSem C) = (adaptorComp I W m g args).denU (baseSem C) :=
  Silmaril.Proofs.Wasm.Jco.Fuse.wrapper_adaptor C I W m g args hlen hsc hg hW

/-- **Fusion is correct for the simple FFI style.** -/
theorem simpleWrapper_simpleComp (C : CoreSem M) (I W : Iface) (m : M) :
    (simpleWrapper I W m).denU (fuseSem C) = (simpleComp I W m).denU (baseSem C) :=
  Silmaril.Proofs.Wasm.Jco.Fuse.simpleWrapper_simpleComp C I W m

/-- The same at the interface sizes of the world. -/
theorem simpleWrapper_simpleComp_atSizes (C : CoreSem M) (I W : Iface) (m : M) :
    atSizes I.length W.length ((simpleWrapper I W m).denU (fuseSem C)) =
      atSizes I.length W.length ((simpleComp I W m).denU (baseSem C)) := by
  rw [simpleWrapper_simpleComp]

/-- The single core module behaves as the linking of its parts. -/
theorem fuseSem_fused (C : CoreSem M) (m : M) (g : Glue) :
    (fuseSem C).sem (.fused m g) = atSizes _ _ ((inner m g).denU (baseSem C)) := rfl

/-- The adaptor-style component of the simple FFI style does not depend on how
fused modules are interpreted. -/
theorem simpleComp_fuseSem (C : CoreSem M) (I W : Iface) (m : M) :
    (simpleComp I W m).denU (fuseSem C) = (simpleComp I W m).denU (baseSem C) :=
  Silmaril.Proofs.Wasm.Jco.Fuse.adaptor_fuseSem C I W m _ _

end Silmaril.Wasm.Jco.Fuse
