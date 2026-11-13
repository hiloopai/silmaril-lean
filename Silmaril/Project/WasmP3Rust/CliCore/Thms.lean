module

public import Silmaril.Project.WasmP3Rust.CliCore.Defs
public import Silmaril.Project.WasmP3Rust.CliSpec.Thms
public import Silmaril.Project.WasmP3Rust.CoreLayerX.Thms

/-!
# `echo.wasm` and `cat.wasm` on the faithful core semantics: reductions

PROVED (standard axioms), conditional on the open targets of
`Silmaril.Project.WasmP3Rust.CliCore.Defs`:

* `echoCli_core`: `Task.echoLinesCore` gives `Task.echoCli (DenX.den coreKsX)` (the echo CLI
  spec through `p3View`, for every host of `echoCliTh`);
* `catCli_core`: `Task.catCopiesCore` gives `Task.catCli (DenX.den coreKsX)`;
* `echoLinesCore_of_echoCoreX`, `catCopiesCore_of_catCoreX`: the refinement forms imply the
  behavioural ones.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust

open Silmaril.Project.WasmP3Rust.CoreLayerX (coreKsX)

/-- **`echo.wasm` meets its CLI spec on the faithful core semantics**, given
`Task.echoLinesCore`. -/
theorem echoCli_core (h : Task.echoLinesCore) : Task.echoCli (DenX.den coreKsX) :=
  echoCli_of_lines h

/-- **`cat.wasm` meets its CLI spec on the faithful core semantics**, given
`Task.catCopiesCore`. -/
theorem catCli_core (h : Task.catCopiesCore) : Task.catCli (DenX.den coreKsX) :=
  catCli_of h

/-- The refinement form gives the behavioural one (`echo`). -/
theorem echoLinesCore_of_echoCoreX (h : Task.echoCoreX) : Task.echoLinesCore :=
  echoLines_of_core h

/-- The refinement form gives the behavioural one (`cat`). -/
theorem catCopiesCore_of_catCoreX (h : Task.catCoreX) : Task.catCopiesCore :=
  StdioK.cat_copies_of_core h

end Silmaril.Project.WasmP3Rust

end
