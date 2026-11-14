module

public import Silmaril.Project.WasmComponents.Wac.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# The Wasm components pilot: the WAC source `pilot.wac`, read

`pilotDoc` is the document `examples/wasm-components/wac/pilot.wac` reads as under `wac.text`
(the verified `Wac.Text.parse`): `wac.pilot` is a certificate for it (`pilot_is`, one
definitional check by the kernel, about 8 s). Split off from
`Silmaril.Project.WasmComponents.Wac.Elab.Thms`, which elaborates `pilotDoc`, to keep each
module under 20 s.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Wac

open Silmaril.Wasm.Wac.Text

/-- The document of `pilot.wac`: `let provider = new silmaril:provider {};`,
`let b = new silmaril:comp-b { get: provider.get };`, `export b.run;`. -/
def pilotDoc : Document :=
  { docs := [],
    package := { name := "silmaril:pilot", version := none },
    targets := none,
    statements := [
      .let_ [] "provider" (.mk (.new { name := "silmaril:provider", version := none } []) []),
      .let_ [] "b" (.mk (.new { name := "silmaril:comp-b", version := none }
        [.named (.ident "get") (.mk (.ident "provider") [.access "get"])]) []),
      .export_ [] (.mk (.ident "b") [.access "run"]) .none] }

/-- **`pilot.wac` reads as `pilotDoc`.** -/
theorem pilot_is : silmaril.wasm_components.wac.pilot.Is pilotDoc := by
  show silmaril.wasm_components.wac.pilot.parse = some pilotDoc
  kernel_rfl

@[solves "silmaril.wasm_components.wac.pilot.parses"]
theorem pilot_text_parses : silmaril.wasm_components.wac.pilot.parses :=
  Silmaril.Project.Value.parses_of_is pilot_is

end Silmaril.Project.WasmComponents.Wac

end
