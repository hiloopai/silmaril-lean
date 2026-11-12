module

public import Silmaril.Wasm.Spec.Basic.Defs
public import Silmaril.Wasm.Spec.Wasm.Defs
public import Silmaril.Wasm.Logic.Strategy.Defs

@[expose] public section

/-!
# Verification conditions for the simple Wasm specifications

The simple logics reduce to the verified every-run Hoare logic of `Silmaril.Wasm.Logic` through its
game link (`Silmaril.Wasm.Logic.GameLink.strategy_sound`: `GameSat P I Inv Ii Ie → Inv s →
I.strategy P s ≤ agStrat Ii Ie`, every profile). The interface specifications below put the
property on the Proponent side (import questions, export answers) and nothing on the Opponent
side, so the assume-guarantee strategy constrains every play:

* `importGuard i Pre`: calls of import `i` must have arguments satisfying `Pre`; nothing else is
  constrained, every answer is allowed;
* `exportGuard j Q`: answers of export `j` must have behaviours satisfying `Q`; every question is
  allowed.

The **verification condition** for "every call of import `i` satisfies `Pre`" is
`GameSat P p.inst Inv (importGuard … i Pre) (exportGuard … none)`: one Hoare triple per export,
`FSpecValid P (gameHost I Ii) (I.addr j) (exportSpec I Inv Ie j)`, where an import stub may only
be called (`Open.FSpecAt.stub`) when its precondition holds. For "import `i` is never called"
the precondition of `i` is `False`, so the proof must show the call unreachable. Soundness:
`Silmaril.Wasm.Spec.Check.Thms`.
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-- Calls of import `i` must satisfy `Pre`; nothing else is constrained. -/
def importGuard (ts : List FnType) (i : Fin ts.length) (Pre : List Val → Prop) :
    ISpec (ifaceSig ts) where
  pre e := e.1 = i → Pre e.2.1
  post _ _ := True

/-- Answers of export `j` (if any) must satisfy `Q`; every question is allowed. -/
def exportGuard (ts : List FnType) (j : Option (Fin ts.length)) (Q : Behaviour Val → Prop) :
    ISpec (ifaceSig ts) where
  pre _ := True
  post f w := j = some f.1 → Q (Answer.toBehaviour (ft := ts.get f.1) w)

end Silmaril.Wasm.Spec
