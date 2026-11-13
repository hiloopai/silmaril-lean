module

public import Silmaril.Wasm.Det.CompIR.Defs
public import Silmaril.Wasm.Det.Game.Instance.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs

/-!
# Determinism of components over the reference machine: definitions

Module-local hypotheses for the IR's Core 3.0 semantics `modSem P` of import-free numeric
modules (`Silmaril.Wasm.Component.Reference`): every instance of the module (`NumModule.IsInst`)
is `DetModule` (`ModDet`), resp. `StatelessModule` (`ModStateless`), on its export addresses,
at profile `P`. They are discharged by the executable checks of the subsets
(`Silmaril.Wasm.Det.NoMem`, `Silmaril.Wasm.Det.Stateless`) on the instance store.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.CompRef

open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
open Silmaril.Wasm.Numerics (Profile)

/-- Every instance of the module is deterministic modulo traps and imports. -/
def ModDet (P : Profile) (m : NumModule) : Prop :=
  ∀ I, m.IsInst I → DetModule P (entry I) I.store

/-- Every instance of the module is stateless modulo traps and imports. -/
def ModStateless (P : Profile) (m : NumModule) : Prop :=
  ∀ I, m.IsInst I → StatelessModule P (entry I) I.store

end Silmaril.Wasm.Det.CompRef
