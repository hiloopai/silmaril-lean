module

public import Silmaril.Proofs.Wasm.Game.LinkStartDiv.Sub
public import Silmaril.Wasm.Game.LinkStartDiv.Defs

/-!
# Static links with start functions, divergence observed: assembly

For a link with start functions `S` in the scalar fragment and **every profile** `P`
(`linkedInst_eq_linkInst`):

  `S.linkedInstStrategy P = S.linkInst P`

as divergence-observing strategies. The chain:

* linked = shared (`linked_eq_shared`, lock-step along the linker relation, start sequences
  included);
* the shared world has the strategy of its receptive completion (`ofLTS_complete`);
* the completed shared world and the composite of the completed provider and consumer simulate
  each other divergence-sensitively (`subSim`, `supSim`);
* the composite system's strategy is the composite of the strategies
  (`DStrategy.ofLTS_comp`; the completions denote their strategies, `denotes_complete`, and take
  silent steps only when running, `silentRunning_complete`), and the completions have the
  strategies of the provider and consumer systems (`ofLTS_complete`), whose composite is
  `StartSetup.linkInst` by definition (`DStrategy.link`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.LinkStartDiv

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game
  Silmaril.Proofs.Wasm.Game.GamesAux Silmaril.Proofs.Wasm.Game.Linking.Split Silmaril.Wasm

variable {S : StartSetup}

/-- The start functions of the linked sequence are typed in the shared store. -/
theorem linkedStarts_typed : ∀ a ∈ S.linkedStarts, StartTyped S.sc a := by
  intro a ha
  rcases List.mem_append.1 ha with hp | hc
  · exact LinkStart.StartSetup.startTyped_sc_of_sp S (S.provStartTyped a (Option.mem_toList.1 hp))
  · exact LinkStart.StartSetup.startTyped_sc_of_scs S (S.consStartTyped a (Option.mem_toList.1 hc))

/-- **Linked = shared**, start sequences included, divergence observed. -/
theorem linked_eq_sharedInst (hS : S.Scalar) (P : Profile) :
    S.linkedInstStrategy P = S.sharedInstStrategy P :=
  linked_eq_shared hS P linkedStarts_typed

/-- The completed provider and consumer have the strategies of the provider and consumer. -/
theorem comp_completed (P : Profile) :
    DStrategy.ofLTS (CompC S P) = S.linkInst P := by
  have hp := posMap_toLTS (S.providerI.instSys P S.sp S.provStart)
  have hc := posMap_consumer (S.consumerI.instSys P S.scs S.consStart)
  have e : DStrategy.ofLTS (CompC S P) =
      (DStrategy.ofLTS (LPc S P)).comp (DStrategy.ofLTS (LCc S P)) :=
    DStrategy.ofLTS_comp (denotes_complete hp) (denotes_complete hc)
      (LTS.SilentRunning.divRunning (silentRunning_complete hp (running_toLTS _)))
      (LTS.SilentRunning.divRunning (silentRunning_complete hc (running_consumer _)))
  have e₁ : DStrategy.ofLTS (LPc S P) = DStrategy.ofLTS (LP S P) := ofLTS_complete hp
  have e₂ : DStrategy.ofLTS (LCc S P) = DStrategy.ofLTS (LC S P) := ofLTS_complete hc
  have e₃ : (DStrategy.ofLTS (LPc S P)).comp (DStrategy.ofLTS (LCc S P)) =
      (DStrategy.ofLTS (LP S P)).comp (DStrategy.ofLTS (LCc S P)) :=
    congrArg (fun δ => DStrategy.comp δ (DStrategy.ofLTS (LCc S P))) e₁
  have e₄ : (DStrategy.ofLTS (LP S P)).comp (DStrategy.ofLTS (LCc S P)) = S.linkInst P :=
    congrArg (DStrategy.comp (DStrategy.ofLTS (LP S P))) e₂
  exact e.trans (e₃.trans e₄)

/-- **Shared = link**, start functions included, divergence observed. -/
theorem sharedInst_eq_linkInst (hS : S.Scalar) (P : Profile) :
    S.sharedInstStrategy P = S.linkInst P := by
  obtain ⟨St, hOp, hOc⟩ := static_spec S.toSetup hS
  have hsh : S.sharedInstStrategy P = DStrategy.ofLTS (LSHc S P) :=
    (ofLTS_complete (posMap_toLTS (ShSys S.toSetup P S.linkedStarts))).symm
  have hle : DStrategy.ofLTS (LSHc S P) = DStrategy.ofLTS (CompC S P) :=
    le_antisymm (subSim (P := P) (St := St) hOp hOc hS).ofLTS_le
      (supSim (P := P) (St := St) hOp hOc).ofLTS_le
  rw [hsh, hle, comp_completed]

/-- **M3 with start functions, divergence observed, every profile.** -/
theorem linkedInst_eq_linkInst (hS : S.Scalar) (P : Profile) :
    S.linkedInstStrategy P = S.linkInst P :=
  (linked_eq_sharedInst hS P).trans (sharedInst_eq_linkInst hS P)

end Silmaril.Proofs.Wasm.Game.LinkStartDiv
