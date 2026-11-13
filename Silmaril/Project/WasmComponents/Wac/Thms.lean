module

public import Silmaril.Project.WasmComponents.Thms
public import Silmaril.Project.WasmComponents.Wac.Defs
public import Silmaril.Project.Formats.Wac.Thms
public import Silmaril.Project.Shapes.Component.Wac.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# The Wasm components pilot: a WAC composition of Silmaril's components

The values (`silmaril/wasm-components/wac-values.toml`, registered by
`sil project components add`):

* `gen.provider`: `Wac.provider` (exports `get = 42`), encoded by `examples/wasm-components/wac/Gen.lean`;
* `wac.pilot`: the WAC source `examples/wasm-components/wac/pilot.wac` (format `wac.text`),
  which instantiates `silmaril:provider` and plugs its `get` into `silmaril:comp-b`
  (`Binary.Example.compB`), exporting `run`;
* `wac.pilot.composed`: what `wac compose` (wac-cli 0.12.0) writes for it (format
  `wac.composition`; the registry records the `link` derivation with its inputs and flags).

Proved here: the composed file is the encoding of `Wac.pilot`, so it reads as `Wac.pilot`
(`composed_is`, one definitional check of the encoder by the kernel, `kernel_rfl`; the parser
is not run in the kernel); the composition has the world `app` (`export run`, no imports) and
does not have the world `app-and-stop` (the rows agree with `wac targets` on `app.wit`,
checked by hand); it lowers to the IR component with no imports and the export `run : () -> u32`
(`composed_hasIRWorld`); the provider file is the encoding of `Wac.provider` (a certificate
under `wasm.component.binary`, with index scoping checked by the row `gen.provider.valid`).

The other WAC rows are in four modules, split off to keep each module under 20 s:

* `Silmaril.Project.WasmComponents.Wac.Text.Thms`: `pilot.wac` reads as `pilotDoc` (the row
  `wac.pilot.parses`);
* `Silmaril.Project.WasmComponents.Wac.Elab.Thms`: `pilot.wac` composes, by WAC's elaborator,
  to `Wac.pilot` (the row `wac.pilot.composes`);
* `Silmaril.Project.WasmComponents.Wac.Typed.Thms`: typed targets (component subtyping) and the
  behavioural equality of the composition and `Binary.Example.linked`;
* `Silmaril.Project.WasmComponents.Wac.Verdicts.Thms`: the verdict DAG
  (`silmaril/wasm-components/wac-dag.toml`).
-/

open Silmaril.Project (Value)

silmaril_artifacts_refresh "silmaril/artifacts.toml"
silmaril load "silmaril/wasm-components/wac-values.toml"

/-- The component `lean/provider.wasm`: `Wac.provider`, a certificate under
`wasm.component.binary` like the other Silmaril-generated components. -/
@[expose, value "silmaril.wasm_components.gen.provider" (format := wasm.component.binary)
  (source := silmaril.wasm_components.gen.provider.blob)
  (doc := "A component exporting get = 42 (Silmaril.Project.WasmComponents.Wac.provider)")]
public def Silmaril.Project.WasmComponents.Wac.providerCert : Silmaril.Wasm.Component.Binary.Ast :=
  Silmaril.Project.WasmComponents.Wac.provider

@[expose] public section

namespace Silmaril.Project.WasmComponents.Wac

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Project.Shapes.Component
open Silmaril.Wasm.Wit.Project (WorldType IRWorld)

/-- The world `app` of `examples/wasm-components/wac/app.wit`, at the level of names and sorts:
the export `run`, a function. -/
def appWorld : WorldType := [.inst (.export ↑"run" (.func 0))]

/-- The world `app-and-stop`: the exports `run` and `stop`. -/
def appAndStopWorld : WorldType :=
  [.inst (.export ↑"run" (.func 0)), .inst (.export ↑"stop" (.func 1))]

/-- The function world of the composition: no imports, the export `run : () -> u32`. -/
def pilotIRWorld : IRWorld := ⟨[], [("run", Binary.Example.ftU32)]⟩

theorem pilot_profile : Wac.Profile pilot := by decide +kernel

/-- The encoding of `pilot` is the composed file, by the kernel's definitional check alone
(`kernel_rfl`, about 0.1 s; `decide +kernel` on the same equation takes about 10 s). -/
theorem pilot_encodes :
    Binary.encode pilot = some silmaril.wasm_components.wac.pilot.composed.bytes.data := by
  kernel_rfl

/-- **The composed file reads as `pilot`.** -/
theorem composed_is : silmaril.wasm_components.wac.pilot.composed.Is pilot :=
  Formats.wacComposition_parse_iff.mpr
    ⟨Formats.wasmComponent_parse_eq.mpr (Binary.parse_encode pilot_encodes), pilot_profile⟩

theorem pilot_hasWorld : WacHasWorld pilot appWorld :=
  (wacHasWorld_iff _ _).mp (by decide +kernel)

theorem pilot_not_appAndStop : ¬ WacHasWorld pilot appAndStopWorld := fun h =>
  absurd ((wacHasWorld_iff _ _).mpr h) (by decide +kernel)

theorem pilot_hasIRWorld : WacHasIRWorld pilot pilotIRWorld :=
  (wacHasIRWorld_iff _ _).mp (by decide +kernel)

/-- `Binary.Example.linked` (producer and consumer linked by hand in one component) lowers to an
IR component with the same function world as the composition. -/
theorem linked_irWorld :
    (match Binary.lower Binary.Example.linked with
      | .ok m => Silmaril.Wasm.Wit.Project.compWorld m == pilotIRWorld
      | .error _ => false) = true := by
  decide +kernel

theorem provider_encodes :
    Binary.encode provider = some silmaril.wasm_components.gen.provider.bytes.data := by
  decide +kernel

end Silmaril.Project.WasmComponents.Wac

end


-- the rows
silmaril instance silmaril.wasm_components.wac.pilot.composed.has_world (expect := "THM") :=
  silmaril.shapes.component.wac_has_world (c := silmaril.wasm_components.wac.pilot.composed)
  (W := Silmaril.Project.WasmComponents.Wac.appWorld)
silmaril instance silmaril.wasm_components.wac.pilot.composed.app_and_stop (expect := "UNS") :=
  silmaril.shapes.component.wac_has_world (c := silmaril.wasm_components.wac.pilot.composed)
  (W := Silmaril.Project.WasmComponents.Wac.appAndStopWorld)
silmaril instance silmaril.wasm_components.wac.pilot.composed.has_ir_world (expect := "THM") :=
  silmaril.shapes.component.wac_has_ir_world (c := silmaril.wasm_components.wac.pilot.composed)
  (W := Silmaril.Project.WasmComponents.Wac.pilotIRWorld)
silmaril instance silmaril.wasm_components.gen.provider.valid (expect := "THM") :=
  silmaril.shapes.component.valid (c := Silmaril.Project.WasmComponents.Wac.providerCert)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Wac

@[answers "silmaril.wasm_components.wac.pilot.composed.has_world" thm]
theorem row_has_world : silmaril.wasm_components.wac.pilot.composed.has_world :=
  Silmaril.Project.Value.satisfies_of_is composed_is pilot_hasWorld

@[answers "silmaril.wasm_components.wac.pilot.composed.app_and_stop" uns]
theorem row_app_and_stop : ¬ silmaril.wasm_components.wac.pilot.composed.app_and_stop := fun h =>
  pilot_not_appAndStop ((Silmaril.Project.Value.Is.satisfies_iff composed_is).mp h)

@[answers "silmaril.wasm_components.wac.pilot.composed.has_ir_world" thm]
theorem row_has_ir_world : silmaril.wasm_components.wac.pilot.composed.has_ir_world :=
  Silmaril.Project.Value.satisfies_of_is composed_is pilot_hasIRWorld

@[solves "silmaril.wasm_components.gen.provider.is"]
theorem provider_is : silmaril.wasm_components.gen.provider.is :=
  is_of_encode rfl provider_encodes

@[answers "silmaril.wasm_components.gen.provider.valid" thm]
theorem row_provider_valid : silmaril.wasm_components.gen.provider.valid := by
  show Silmaril.Project.Shapes.Component.CompValid providerCert
  unfold Silmaril.Project.Shapes.Component.CompValid
  decide +kernel

@[solves "silmaril.wasm_components.wac.pilot.composed.parses"]
theorem composed_parses : silmaril.wasm_components.wac.pilot.composed.parses :=
  Silmaril.Project.Value.parses_of_is composed_is

@[solves "silmaril.wasm_components.gen.provider.parses"]
theorem provider_parses : silmaril.wasm_components.gen.provider.parses :=
  Silmaril.Project.Value.parses_of_is provider_is

end Silmaril.Project.WasmComponents.Wac

end

