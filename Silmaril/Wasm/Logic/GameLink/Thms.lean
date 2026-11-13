module

public import Silmaril.Proofs.Wasm.Logic.GameLink.Productive

/-!
# The logic and the Wasm game: soundness and verified linking

For a scalar Core 3.0 instance `I : Silmaril.Wasm.Game.ScalarInstance` (the fragment
of `Silmaril.Wasm.Game`, see `Silmaril.Wasm.Logic.GameLink.Defs`), an import
specification `Ii : ISpec I.E`, an export specification `Ie : ISpec I.F` and a
store invariant `Inv`, for **every profile** `P`:

* `strategy_sound` (`Silmaril.Proofs.Wasm.Logic.GameLink.Strategy`):
  `GameSat P I Inv Ii Ie → Inv s → I.strategy P s ≤ agStrat Ii Ie`: the module
  strategy of `Silmaril.Wasm.Game` (store hidden and persisting across export
  calls) refines the assume/guarantee strategy; with `s = I.store` this is
  `I.σ P ≤ agStrat Ii Ie`;
* `dstrategy_sound`: `TGameSat P I Inv Ii Ie → Inv s → I.dstrategy P s ≤
  dagStrat Ii Ie`: the divergence-observing strategy diverges only after a play
  in which Opponent broke the specifications (`dstrategy_div`);
  `dstrategy_productive` (`Silmaril.Proofs.Wasm.Logic.GameLink.Productive`): it is
  productive; `GameSat.of_total`: `TGameSat → GameSat`;
* `answer_post` (`Silmaril.Proofs.Wasm.Logic.GameLink.Link`): closed-world reading,
  a host-free Core run of an allowed export call that ends in a result answers
  as `Ie.post` requires;
* **verified static linking** `linked_sound`: for a static link
  `S : Silmaril.Wasm.Game.Linking.Setup` in the scalar fragment (`S.Scalar`), if the
  provider meets `Im` from `S.sp` and the consumer (with host stubs) meets `Ie`
  under `Im` from `S.scs`, then `S.linkedI.σ P ≤ agStrat Ii Ie`, by
  `Strategy.comp_refines` and M3 (`Setup.link_is_composition_profile`);
  `linked_answer_post`: every terminating host-free run of an allowed export
  call of the linked module meets `Ie`; `linked_sound_total` from total
  correctness;
* divergence-aware composition of the parts: `dcomp_sound` (generic:
  `σ ≤ dagStrat Ii Im → τ ≤ dagStrat Im Ie → Productive Im Ie τ → σ.comp τ ≤
  dagStrat Ii Ie`) and `dlink_parts_sound`
  (`(S.providerI.dstrategy P S.sp).comp (S.consumerI.dstrategy P S.scs) ≤
  dagStrat Ii Ie` from total correctness of both parts). This is about the
  divergence-observing composite of the parts, not about the linked module:
  `Silmaril.Wasm.Game` has no divergence-observing M3.

The worked example is `Silmaril.Wasm.Logic.GameLink.Examples`.

A Silmaril addition.
-/
