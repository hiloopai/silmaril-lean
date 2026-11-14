module

public import Silmaril.Wasm.Abstract.Module.Defs
public import Silmaril.Wasm.Abstract.Function.Thms
public import Silmaril.Games.Abstract.Module.Thms

/-!
# Core 3.0 modules as closed abstract modules: theorems

* `close_lift_wasmModule`: the open projection of a Core 3.0 module closes back
  to it. The square "module → open module → closed module" commutes.
* `image_wasmModule`: each function of the module agrees with the existing
  `behaviours` at its address.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {n : Nat} {addrs : Fin n → Nat}

/-- The open projection closes back to the module. -/
theorem close_lift_wasmModule :
    Silmaril.Games.Abstract.Shape.close (Silmaril.Games.Abstract.Shape.lift (wasmModule P host addrs)) = wasmModule P host addrs :=
  Silmaril.Games.Abstract.Shape.close_lift _

/-- Each function agrees with the existing behaviours. -/
theorem image_wasmModule (i : Fin n) (s : Store H) (vs : List Val) :
    (fun x => endToBehaviour x.2) '' wasmModule P host addrs i s vs =
      behaviours P host s (addrs i) vs :=
  image_wasmFun P host (addrs i) s vs

end Silmaril.Wasm.Abstract
