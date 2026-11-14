module

public import Silmaril.Games.Abstract.TrapCut.Defs
public import Silmaril.Wasm.Abstract.Instance.Defs
public import Silmaril.Wasm.Det.Game.Defs
public import Silmaril.Wasm.Det.Game.Instance.Defs

/-!
# Scalar Wasm instances with visible divergence: both trap/divergence notions

The scalar instance machine of `Silmaril.Wasm.Abstract.Instance` folds every
host-free run into the visible move that ends it. A diverging export call
therefore just never answers, exactly like a stuck one. `omachine I P s` adds
the host-free steps back as *silent* steps: from a running state, one
`InternalP P` step of the thread. A trap stays what it is in the Wasm game, a
visible Proponent answer `Answer.trap` (`trapMove`).

The two equivalences of instance machines:

* **sensitive**: `OMachine.TagEquiv`. Trap answers are moves and
  divergence is the `div` tag, so the two are distinguished, and the trace
  continues after a trap (the instance stays callable);
* **trap ≈ divergence**: `OMachine.CutEquiv (trapMove I)`. Every
  observation is cut at the first trapping answer, and that point is tagged
  `abort`, like a divergence there.

`Silmaril.Wasm.Abstract.InstanceOutcome.Thms` proves the following:
the silent steps do not change the traces (so state erasure is still the
existing instance strategy), and the `div` observations are exactly the
host-free divergences of an export call.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Game Silmaril.Wasm.Det.Game
open Silmaril.Wasm.Numerics (Profile)

/-- The steps of an instance with host-free steps silent. -/
inductive OStep (I : ScalarInstance) (P : Profile) :
    I.HState → Option (Move I.E I.F) → I.HState → Prop
  /-- A move of the instance or its environment. -/
  | vis {x y : I.HState} {m : Move I.E I.F} : I.Trans P x m y → OStep I P x (some m) y
  /-- One host-free step of the running thread. -/
  | tau {f : I.F.Op} {s s' : Silmaril.Wasm.Execution.Core.Store Nat}
      {t t' : Silmaril.Wasm.SingleThreaded.Thread} :
      InternalP P (s, t) (s', t') → OStep I P (.running f s t) none (.running f s' t')

/-- The instance at store `s` as a machine with silent host-free steps. It never
terminates as a whole (`PEmpty` results), and it has no trap states: traps are
answers. -/
def omachine (I : ScalarInstance) (P : Profile) (s : Silmaril.Wasm.Execution.Core.Store Nat) :
    OMachine (sigGame I.E I.F) PEmpty :=
  ⟨⟨I.HState, .idle s, OStep I P⟩, fun _ _ => False, fun _ => False⟩

/-- The trapping answers of export calls. -/
def trapMove (I : ScalarInstance) : (sigGame I.E I.F).Move → Prop :=
  PTrap (E := I.E) (wasmTraps I.exports)

end Silmaril.Wasm.Abstract
