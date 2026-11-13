module

public import Silmaril.Wasm.Game.LinkStart.Defs

/-!
# Static links with start functions, divergence observed: definitions

For a link with start functions (`Linking.StartSetup`), the intermediate world of the proof that
the linked module's instantiable strategy is the game-semantic link of the provider and the
consumer, divergence observed (`Silmaril.Wasm.Game.LinkStartDiv.Thms`):

* `StartSetup.sharedInstStrategy P`: the shared world (provider and consumer instantiated
  separately in one store, `Setup.sharedI`) whose instantiation runs the linked start sequence
  `S.linkedStarts` (`ScalarInstance.instSysSeq`), divergence observed.

New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Linking.StartSetup

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable (S : StartSetup)

/-- **The instantiable strategy of the shared world** running the linked start sequence. -/
noncomputable def sharedInstStrategy (P : Profile) :
    DStrategy (ifaceSig []) ((ifaceSig S.exportTypes).withInst (Behaviour Val)) :=
  DStrategy.ofInst (S.sharedI.instSysSeq P S.sc S.linkedStarts)

end Silmaril.Wasm.Game.Linking.StartSetup
