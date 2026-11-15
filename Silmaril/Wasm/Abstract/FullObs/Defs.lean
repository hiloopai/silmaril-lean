module

public import Silmaril.Games.Abstract.FullFun.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Defs

/-!
# Full observations of interaction-tree bodies

`toFull f := (toAFun f, toInf f)`: a body's full observation, its finite behaviours (finished
paths, a trap with its payload and store erased, silent divergence) paired with its productive
runs (infinite streams of answered import calls, `BodyTrace.toInf`). Theorems in
`Silmaril.Wasm.Abstract.FullObs.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.FullObs

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace

universe u

/-- **The full observation of a body.** -/
def toFull {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    FullFun (liftSig E) S A B :=
  (toAFun f, toInf f)

end Silmaril.Wasm.Abstract.FullObs
