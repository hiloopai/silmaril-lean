module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.DivSub
public import Silmaril.Proofs.Wasm.Game.DivAdequacy.Comp

/-!
# Static linking is composition, divergence observed: proofs

`link_is_composition_div`: for every profile, the divergence-observing strategy of the linked
module is the `DStrategy.comp` of those of the provider and the consumer:

* (A) `DivShared.linked_dstrategy_eq_shared`: linked = shared (lock-step bisimulation along the
  linker relation, both directions);
* (B) `Split.shared_eq_comp`: shared = the composite system of provider and consumer
  (`Split.compSim`, `Split.sharedSim`, divergence-sensitive simulations with measures for
  synchronisations and doomed configurations);
* `DStrategy.ofLTS_comp`: the composite system's strategy is the composite of the strategies
  (the instance systems denote their strategies and take silent steps only when running).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Linking

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking

variable {S : Setup}

/-- **M3, divergence observed, every profile.** -/
theorem link_is_composition_div (hS : S.Scalar) (P : Profile) :
    S.linkedI.dstrategy P S.sl =
      (S.providerI.dstrategy P S.sp).comp (S.consumerI.dstrategy P S.scs) := by
  rw [DivShared.linked_dstrategy_eq_shared hS P, Split.shared_eq_comp hS P]
  exact DStrategy.ofLTS_comp (ScalarInstance.denotes_dlts P S.sp)
    (ScalarInstance.denotes_dlts P S.scs)
    (LTS.SilentRunning.divRunning (ScalarInstance.silentRunning_dlts P S.sp))
    (LTS.SilentRunning.divRunning (ScalarInstance.silentRunning_dlts P S.scs))

end Silmaril.Proofs.Wasm.Game.Linking
