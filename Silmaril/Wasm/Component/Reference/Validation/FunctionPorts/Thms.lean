module

public import Silmaril.Wasm.Component.Reference.Validation.FunctionPorts.Defs
import Silmaril.Proofs.Wasm.Component.Reference.Validation.FunctionPorts
import Silmaril.Wasm.V1.ToCore.DefTypes

public section

namespace Silmaril.Wasm.Component.Validation

open Component.Types
open Component.Engine (CoreExternType)

theorem core3OfFlat_eq_iff {left right : V1.FuncType} : core3OfFlat left = core3OfFlat right ↔ left = right :=
  ⟨fun eq => V1.FuncType.toDefType_injective (Wasm.Validation.CExternType.func.inj (congrArg Subtype.val eq)),
    congrArg core3OfFlat⟩

/-- The native Lime and validating Core resolvers have the same ordered
function ports after type translation. Names and position are retained, even
for repeated types or repeated import keys. Validity requires distinct export
names; consumers needing unique import lookup must separately require it. -/
theorem resolveLimeFunctionPorts {mod : Lime1.Module} (valid : Lime1.Validation.ModuleValid mod)
    (ports : LimeFunctionPorts mod) : ∃ signature : CoreModuleType V1.FuncType,
    lime1ModuleType mod = some (signature.mapX CoreExternType.func) ∧
    core3ModuleType? mod.toCore = some (signature.mapX core3OfFlat) :=
  Proofs.Wasm.Component.Reference.Validation.FunctionPorts.resolves valid ports

end Silmaril.Wasm.Component.Validation
