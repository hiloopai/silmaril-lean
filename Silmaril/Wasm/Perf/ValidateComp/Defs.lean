module

public import Silmaril.Wasm.Perf.ValidateR.Defs
public import Silmaril.Wasm.Component.RefValid.Defs

/-!
# The reference component validator over the fast Core validators

The component half of `Perf.ValidateF` and `Perf.ValidateR`: the Core 3.0 component validator
`Silmaril.Wasm.Component.Reference.check?` checks every embedded core module with silmaril's
`validate?`; `checkCore3F` and `checkCore3R` are the same validator with `validateF` and
`validateR` (`core3ModuleTypeF`, `core3ModuleTypeR`: `core3ModuleType?` over them, copied
verbatim otherwise).

The Core validators themselves (`ValidateF`, `ValidateR`) depend on silmaril only; this module is
the part that depends on the component development.

`Thms.lean`: `checkCore3F_eq`, `checkCore3R_eq : checkCore3R = Reference.check?` (registered
with `@[csimp]`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.ValidateF

open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.Types

/-- `core3ModuleType?` over `validateF` (copied verbatim otherwise). -/
def core3ModuleTypeF (m : Silmaril.Wasm.Module) : Option (CoreModuleType Core3Extern) := do
  let mt ← validateF m
  let is ← (m.imports.zip mt.imports).mapM fun p =>
    (core3Ext? p.2).map ((p.1.moduleName, p.1.name), ·)
  let es ← (m.exports.zip mt.exports).mapM fun p => (core3Ext? p.2).map (p.1.name, ·)
  pure ⟨is, es⟩

/-- **The Core 3.0 component validator with `validateF`** (`checkCore3F_eq`). -/
def checkCore3F (feat : Silmaril.Wasm.Component.Features)
    (c : Silmaril.Wasm.Component.Reference.Core3Component) :
    Except ValidationError Silmaril.Wasm.Component.Reference.ComponentType :=
  check? feat core3Profile core3ModuleTypeF c

end Silmaril.Wasm.Perf.ValidateF

namespace Silmaril.Wasm.Perf.ValidateR

open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.Types

/-- `core3ModuleType?` over `validateR` (copied verbatim otherwise). -/
def core3ModuleTypeR (m : Silmaril.Wasm.Module) : Option (CoreModuleType Core3Extern) := do
  let mt ← validateR m
  let is ← (m.imports.zip mt.imports).mapM fun p =>
    (core3Ext? p.2).map ((p.1.moduleName, p.1.name), ·)
  let es ← (m.exports.zip mt.exports).mapM fun p => (core3Ext? p.2).map (p.1.name, ·)
  pure ⟨is, es⟩

/-- **The Core 3.0 component validator with `validateR`** (`checkCore3R_eq`). -/
def checkCore3R (feat : Silmaril.Wasm.Component.Features)
    (c : Silmaril.Wasm.Component.Reference.Core3Component) :
    Except ValidationError Silmaril.Wasm.Component.Reference.ComponentType :=
  check? feat core3Profile core3ModuleTypeR c

end Silmaril.Wasm.Perf.ValidateR
