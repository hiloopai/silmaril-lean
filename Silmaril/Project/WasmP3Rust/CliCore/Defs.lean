module

public import Silmaril.Project.WasmP3Rust.CliSpec.Defs
public import Silmaril.Project.WasmP3Rust.StdioK.Thms
public import Silmaril.Project.WasmP3Rust.CoreLayerX.Defs

/-!
# `echo.wasm` and `cat.wasm` on the faithful core semantics: the targets

`Silmaril.Project.WasmP3Rust.CliSpec` states the CLI theorems of the pinned Rust components for
a core semantics `Ks` and proves them for the core models `stdioK echoPlan`, `stdioK catPlan`.
Its open targets for the real code (`Task.echoLines Ks`, `StdioK.Task.catCore Ks`) were stated
over arbitrary `Ks`; a degenerate `alloc` would make `Task.echoLines` vacuous. Here they are
stated for **the faithful core semantics** `CoreLayerX.coreKsX`: silmaril's Core 3.0
interpreter on the component's core layer, with `get-arguments` lowered through a re-entrant
`realloc` (a second interpreter thread on the same store).

| target | what it says | status |
|---|---|---|
| `Task.echoLinesCore` | `Task.echoLines coreKsX`: under `den coreKsX`, `echo.wasm` prints the line of its arguments, for every argument list and every host of `echoTh` | open (frozen); tested: `tools/cli-core-trace/tests/run.sh` |
| `Task.catCopiesCore` | `Task.catCopiesX (den coreKsX)`: `cat.wasm` copies stdin to stdout (`catGX`) for every host of `stdoutTh3x` | open (frozen); tested, same script |
| `Task.echoCoreX`, `Task.catCoreX` | `StdioK.Task.echoCore coreKsX`, `StdioK.Task.catCore coreKsX`: the denotations refine the models' play by play | open (frozen); expected false: the real code calls `future.read` before writing (`echo`: 4th call) or before `waitable-set.new` (`cat`), which the models do not (as `HelloCore.not_helloCore_core` for `hello`) |

The CLI theorems follow from the behavioural targets (`Silmaril.Project.WasmP3Rust.CliCore.Thms`).

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust

open Silmaril.Project.WasmP3Rust.CoreLayerX (coreKsX)

/-- **Open (frozen)**: under the faithful core semantics, `echo.wasm` prints the line of its
arguments, for every argument list. -/
def Task.echoLinesCore : Prop := Task.echoLines coreKsX

/-- **Open (frozen)**: under the faithful core semantics, `cat.wasm` copies stdin to stdout. -/
def Task.catCopiesCore : Prop := Task.catCopiesX (DenX.den coreKsX)

/-- Open (frozen; expected false): the faithful denotation of `echo.wasm` refines the model's. -/
def Task.echoCoreX : Prop := StdioK.Task.echoCore coreKsX

/-- Open (frozen; expected false): the faithful denotation of `cat.wasm` refines the model's. -/
def Task.catCoreX : Prop := StdioK.Task.catCore coreKsX

end Silmaril.Project.WasmP3Rust

end
