module

public import Silmaril.Wasi.Versions.P2OverP3.Comp.Defs

/-!
# The Wasm components pilot: WASI 0.3 via 0.2, and 0.2 via 0.3 (definitions)

The parameters of the rows of `Silmaril.Project.WasmComponents.Relations.Thms`: the file contents
behind `read-via-stream` at which the row on WASI 0.3 over 0.2 is stated (the theorem holds for
every file contents), and the component of WASI 0.2 over 0.3 with a 4096-byte buffer as a
model of its world (imports `imp3`, exports `exp2`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Relations

/-- No files behind `read-via-stream`. -/
def noFiles : BitVec 32 → List (BitVec 8) := fun _ => []

/-- The world of WASI 0.2 over 0.3: the 0.3 imports (and the extra built-ins), the 0.2 exports. -/
def p2OverP3World : Silmaril.Wasi.World :=
  ⟨Silmaril.Wasi.Versions.P2OverP3.imp3, Silmaril.Wasi.Versions.P2OverP3.exp2⟩

/-- WASI 0.2 over 0.3 with a 4096-byte buffer, as a model of its world. -/
def p2OverP3Model : p2OverP3World.Model := Silmaril.Wasi.Versions.P2OverP3.p2OverP3 4096

end Silmaril.Project.WasmComponents.Relations

end
