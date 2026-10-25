module

public import Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Instructions
public import Silmaril.Wasm.Binary.Extensions.Structured.Modules

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.LegacyExceptions

/-- The context shape includes every retained legacy try/catch body in wire
order when collecting data-index syntax. It is not an execution semantics. -/
def dataIdxs (body : Wasm.Extensions.LegacyExceptions.Expr) : List DataIdx :=
  Core.Expr.dataIdxs (Wasm.Extensions.Structured.Expr.contextShape
    Wasm.Extensions.LegacyExceptions.Leaf.contextShape body)

abbrev Module (F : Core.Forms) := Structured.Module F (Expr F) dataIdxs
abbrev Encodes := Module Core.Forms.all

end Silmaril.Wasm.Binary.Extensions.LegacyExceptions
