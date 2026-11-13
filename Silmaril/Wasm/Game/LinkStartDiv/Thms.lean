module

public import Silmaril.Wasm.Game.LinkStartDiv.Defs
public import Silmaril.Wasm.Game.LinkStart.Thms
public import Silmaril.Games.Inst.Thms
import Silmaril.Proofs.Wasm.Game.LinkStartDiv.Main

/-!
# Static links with start functions, divergence observed

For an **arbitrary** silmaril profile `P` (no determinism is used) and a link with start
functions (`Linking.StartSetup`: the linker fragment of `Linking.Setup` with scalar interfaces,
`S.Scalar`, and start functions of type `[] → []` that are functions of their modules):

* `StartSetup.link_is_composition_inst_div`: **the divergence-observing instantiable strategy of
  the linked module equals the game-semantic link of the components' divergence-observing
  instantiable strategies**, `S.linkedInstStrategy P = S.linkInst P`. The linked module runs its
  start sequence `S.linkedStarts` (the provider's start function, then the consumer's) during
  instantiation; the link (`Silmaril.Games.DStrategy.link`) instantiates the provider, running its
  start function, before the consumer, whose start function may call the provider. Plays,
  **divergences and infinite plays** agree, during instantiation and in the export calls after
  it. This strengthens `link_is_composition_inst` (finite plays only; its `forget`,
  `link_is_composition_inst_div_forget`) and extends `Setup.link_is_composition_div` (no start
  functions) to start functions.
* `StartSetup.linkedInst_eq_sharedInst`, `StartSetup.sharedInst_eq_linkInst`: the two steps,
  through the shared world running the start sequence (`sharedInstStrategy`).
* `StartSetup.linkInst_instDiverges_iff`: hence the link diverges during instantiation exactly
  when the linked start sequence has an infinite host-free run (`SeqStep`), including a consumer
  start function diverging through infinitely many calls to the provider.

Proofs: `Silmaril.Proofs.Wasm.Game.LinkStartDiv.*` (new): divergence-sensitive simulations
(`LTS.DivSimulation`) in both directions between the shared world and the composite of the
provider's instantiable system and the consumer's link system, made receptive
(`LinkStartDiv.complete`: `DStrategy.ofLTS_comp` needs systems denoting their strategies, and the
instantiable systems refuse Opponent moves that `Strategy.ofLTS` adds by receptiveness). The
provider's start run is related by `Split.SRel`, the consumer's start run (which may call the
provider) and export calls by `Split.CRel`/`Split.PRel` with a phase recording which of the two
the consumer runs; the hidden synchronisations of the link decrease a measure, and doomed shared
configurations (a provider trap inside a consumer call) shrink their code, as in
`Silmaril.Proofs.Wasm.Game.Linking.Split.{DivSup,DivSub}`.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Linking.StartSetup

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable (S : StartSetup) (P : Profile)

/-- **M3 with start functions, divergence observed, every profile.** The divergence-observing
instantiable strategy of the linked module (instantiation running the provider's start function,
then the consumer's) is the link of the provider's divergence-observing instantiable strategy
below the consumer's instantiable system. -/
theorem link_is_composition_inst_div (hS : S.Scalar) : S.linkedInstStrategy P = S.linkInst P :=
  Silmaril.Proofs.Wasm.Game.LinkStartDiv.linkedInst_eq_linkInst hS P

/-- The same, as a composite in `Silmaril.Games.DStrategy` (`DStrategy.link` is composition). -/
theorem link_is_composition_inst_div_comp (hS : S.Scalar) :
    S.linkedInstStrategy P =
      (S.providerI.instStrategy P S.sp S.provStart).comp
        (DStrategy.ofLTS (S.consumerI.instSys P S.scs S.consStart).consumerLTS) :=
  S.link_is_composition_inst_div P hS

/-- The finite plays of `link_is_composition_inst_div` (`link_is_composition_inst`). -/
theorem link_is_composition_inst_div_forget (hS : S.Scalar) :
    (S.linkedInstStrategy P).forget = (S.linkInst P).forget :=
  congrArg DStrategy.forget (S.link_is_composition_inst_div P hS)

/-- **Linked = shared**, start sequences included, divergence observed. -/
theorem linkedInst_eq_sharedInst (hS : S.Scalar) :
    S.linkedInstStrategy P = S.sharedInstStrategy P :=
  Silmaril.Proofs.Wasm.Game.LinkStartDiv.linked_eq_sharedInst hS P

/-- **Shared = link**, start functions included, divergence observed. -/
theorem sharedInst_eq_linkInst (hS : S.Scalar) : S.sharedInstStrategy P = S.linkInst P :=
  Silmaril.Proofs.Wasm.Game.LinkStartDiv.sharedInst_eq_linkInst hS P

/-- **The link diverges during instantiation exactly when the linked start sequence may run
forever** (host-free steps of the provider's start function, then of the consumer's). -/
theorem linkInst_instDiverges_iff (hS : S.Scalar) :
    (S.linkInst P).InstDiverges ↔
      InfiniteTrace (SeqStep P) (S.sl, .active {} [], S.linkedStarts) := by
  rw [← S.link_is_composition_inst_div P hS]
  exact DStrategy.ofInst_instDiverges_iff

end Silmaril.Wasm.Game.Linking.StartSetup
