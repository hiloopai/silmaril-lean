module

public import Silmaril.Wasm.Wac.WorldExample.Defs
public import Silmaril.Wasm.Wac.World.Thms

/-!
# WAC: typed targets checking on the worked composition, checked

By kernel evaluation: the typed world of the composition, the verdicts of the typed and
untyped checks on the three worlds of `Silmaril.Wasm.Wac.WorldExample`, and `Targets.Fits`
for `world` obtained from the typed verdict by `World.fits_of_sat`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WorldExample

open Silmaril.Wasm.Wac.World

theorem profileWorld_ast :
    (profileWorld K imps Example.ast).toOption = some ([("host", hostK)], [("run", .func s0)]) := by
  decide +kernel

theorem checkTyped_world : (checkTyped K imps [] Example.ast world).toOption = some true := by
  decide +kernel

theorem checkTyped_worldPrintArg : (checkTyped K imps [] Example.ast worldPrintArg).toOption = some false := by
  decide +kernel

theorem checkTyped_worldMore : (checkTyped K imps [] Example.ast worldMore).toOption = some false := by
  decide +kernel

/-- The untyped check cannot see the type of `print`. -/
theorem fits_worldPrintArg : Targets.fits (Targets.surface Example.ast) worldPrintArg = true := by
  decide +kernel

theorem not_fits_worldMore : Targets.fits (Targets.surface Example.ast) worldMore = false := by
  decide +kernel

theorem targetKinds_world :
    (targetKinds [] world).toOption = some ([("host", hostK)], [("run", .func s0)]) := by
  decide +kernel

/-- The untyped verdict on `world`, derived from the typed one. -/
theorem fits_world : Targets.Fits (Targets.surface Example.ast) world := by
  have hs : Sat ([("host", hostK)], [("run", .func s0)]) ([("host", hostK)], [("run", .func s0)]) :=
    (sat_iff _ _).1 (by decide +kernel)
  have hp : profileWorld K imps Example.ast = .ok ([("host", hostK)], [("run", .func s0)]) := by
    have h := profileWorld_ast
    revert h
    cases profileWorld K imps Example.ast <;> simp [Except.toOption]
  exact fits_of_sat hp (by decide +kernel) (by decide +kernel) hs

end Silmaril.Wasm.Wac.WorldExample
