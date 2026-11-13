module

public import Silmaril.Wasm.Wasmi.Defs
public import Silmaril.Wasm.Models.Game.Defs

/-!
# wasmi 2.0.0, Core 3.0 and the loose model in the institution of game semantics

The GInst placement of `docs/projects/spectec/README.md` §4.3. The three models have the points (a store and
a host) and calls of the Core chart, so they share one closed game `game`, whose questions are
calls and whose answers are behaviours. Each point gives three observation strategies
(`Silmaril.Wasm.Models.obsStrat`):

* `coreStrat P x`: Core 3.0 (`Core.obs P x`);
* `wasmiStrat P x`: wasmi 2.0.0 (`Silmaril.Wasm.Wasmi.obs P x`, Core of the fused store);
* `looseStrat P x`: the loose model (`Silmaril.Wasm.Wasmi.Loose.obs P x`, Core plus
  `selectEither`).

`sen b`: the `◇` sentence "the reproducer call `f 5 1` may answer `b`"
(`GSen.diaPlay (callPlay reproCall b)`). The theorems are in `Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.GInst

open Silmaril.Games Silmaril.Wasm.Models Silmaril.Wasm.Atlas Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The closed game of the Core chart: calls answered by behaviours. -/
abbrev game : Game.{0} := ⟨Sig.empty, callSig Core.Call (Behaviour Val)⟩

/-- **The Core 3.0 strategy** of a point. -/
def coreStrat (P : Profile) (x : Core.Pt H) : game.Model := obsStrat (Core.obs P x)

/-- **The wasmi 2.0.0 strategy** of a point. -/
def wasmiStrat (P : Profile) (x : Core.Pt H) : game.Model := obsStrat (Silmaril.Wasm.Wasmi.obs P x)

/-- **The loose strategy** of a point. -/
def looseStrat (P : Profile) (x : Core.Pt H) : game.Model := obsStrat (Loose.obs P x)

/-- The `◇` sentence "`f 5 1` may answer `b`". -/
def sen (b : Behaviour Val) : GSen game.E game.F := GSen.diaPlay (callPlay reproCall b)

end Silmaril.Wasm.Wasmi.GInst
