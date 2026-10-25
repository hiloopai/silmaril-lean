module

public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Instructions
public import Silmaril.Wasm.Binary.Extensions.Structured.Modules

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.BinaryenMemory

/-- Array-backed and ordered atomic leaves mention no data segments. Ordinary Core leaves and
nested structured bodies retain exactly their data-index syntax. -/
def dataIdxs (body : Wasm.Extensions.BinaryenMemory.Expr) : List DataIdx :=
  Core.Expr.dataIdxs (Wasm.Extensions.Structured.Expr.contextShape
    Wasm.Extensions.BinaryenMemory.Leaf.contextShape body)

abbrev Module (F : Core.Forms) := Structured.Module F (Expr F) dataIdxs
abbrev Encodes := Module Core.Forms.all

end Silmaril.Wasm.Binary.Extensions.BinaryenMemory
