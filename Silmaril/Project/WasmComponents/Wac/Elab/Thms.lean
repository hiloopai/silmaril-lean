module

public import Silmaril.Project.WasmComponents.Wac.Text.Thms
public import Silmaril.Project.Shapes.Component.WacElab.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# The Wasm components pilot: `pilot.wac` composes to `Wac.pilot`, by WAC's elaborator

The row `silmaril.wasm_components.wac.pilot.composes` (shape
`silmaril.shapes.component.wac_composes`): the WAC source `examples/wasm-components/wac/pilot.wac`
(the value `wac.pilot`, format `wac.text`), elaborated against the registered packages
`silmaril:provider` (`gen.provider`) and `silmaril:comp-b` (`gen.comp_b`) by WAC's elaborator, encoded
by WAC's bridge and with the packages defined in place (`composeDefined`), is the file
`wac compose` wrote (`wac.pilot.composed`) without its two custom sections (`component-name`,
`producers`).

So the registry's `link` derivation (wac-cli 0.12.0, `silmaril/artifacts.toml`) is no longer
the only link between the source and the composition: Silmaril's pipeline computes the same
component from the source and the two package files. The proof is one definitional check by the
kernel (`pilotDoc_composes`, by `kernel_rfl` of `Silmaril.Wasm.Verify.Kernel`, about 1 s: the WIT
projection of both packages, the elaborator, the encoder and `defineDeps`, compared with
`stripCustom pilot`) on the document `pilotDoc` the source reads as
(`Silmaril.Project.WasmComponents.Wac.Text.Thms`, `pilot_is`: the verified WAC lexer and parser,
about 8 s); the rest is the certificates `composed_is`, `provider_is` and `compB_is`.

What this does not show: that wac-cli's own elaborator agrees with WAC's on other documents
(the differential of `docs/projects/wasm-wasi.md` tests that), or anything about the custom sections.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Wac

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Project.Shapes.Component
open Silmaril.Wasm.Component.Binary (Ast)

/-- The packages of `pilot.wac`, by package key: the registered component files. -/
def pilotPkgs : List (String × Value Ast) :=
  [("silmaril:provider", silmaril.wasm_components.gen.provider),
    ("silmaril:comp-b", silmaril.wasm_components.gen.comp_b)]

/-- The packages of `pilot.wac`, as components. -/
def pilotPkgAsts : List (String × Ast) :=
  [("silmaril:provider", provider), ("silmaril:comp-b", Binary.Example.compB)]

/-- **The composition of the source**, by the kernel's definitional check alone
(`kernel_rfl`). -/
theorem pilotDoc_composes :
    composeDefined pilotPkgAsts pilotDoc = .ok (Silmaril.Project.WasmComponents.stripCustom pilot) := by
  kernel_rfl

/-- **The source composes to `pilot` without its custom sections.** -/
theorem pilot_composes_ast : ∃ d, silmaril.wasm_components.wac.pilot.parse = some d ∧
    composeDefined pilotPkgAsts d = .ok (Silmaril.Project.WasmComponents.stripCustom pilot) :=
  ⟨pilotDoc, pilot_is, pilotDoc_composes⟩

theorem pilotPkgs_parse : parseAll pilotPkgs = some pilotPkgAsts := by
  have hp : silmaril.wasm_components.gen.provider.parse = some provider := provider_is
  have hb : silmaril.wasm_components.gen.comp_b.parse = some Binary.Example.compB :=
    Silmaril.Project.WasmComponents.compB_is
  simp only [parseAll, pilotPkgs, pilotPkgAsts, List.mapM_cons, List.mapM_nil, hp, hb]
  rfl

end Silmaril.Project.WasmComponents.Wac

end

silmaril instance silmaril.wasm_components.wac.pilot.composes (expect := "THM") :=
  silmaril.shapes.component.wac_composes (pkgs := Silmaril.Project.WasmComponents.Wac.pilotPkgs)
  (src := silmaril.wasm_components.wac.pilot) (out := silmaril.wasm_components.wac.pilot.composed)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Wac

/-- **`pilot.wac` composes to the file `wac compose` wrote**, up to its custom sections. -/
@[answers "silmaril.wasm_components.wac.pilot.composes" thm]
theorem row_composes : silmaril.wasm_components.wac.pilot.composes := by
  obtain ⟨d, hd, hc⟩ := pilot_composes_ast
  exact ⟨d, pilotPkgAsts, pilot, hd, pilotPkgs_parse, composed_is, hc⟩

end Silmaril.Project.WasmComponents.Wac

end
