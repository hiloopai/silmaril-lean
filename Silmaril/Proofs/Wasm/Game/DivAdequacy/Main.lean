module

public import Silmaril.Proofs.Wasm.Game.DivAdequacy.Diverge
public import Silmaril.Proofs.Wasm.Game.Adequacy.Later

/-!
# Adequacy with divergence-observing strategies: proofs

For every profile `P`: the closed-world behaviours of an export call are
exactly the observations `dcompositeObs` of the divergence-observing closed
program `I.closedD P s K`, divergence included (`adequacy_div`). Terminating
behaviours come from M2 (`adequacy_profile`) and `forget_closedD`;
divergence from `mem_div_closedD_iff`.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

namespace ScalarInstance

variable {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile}

/-- **M2 with divergence-observing strategies, every profile.** -/
theorem adequacy_div {s : Store Nat} (hw : I.WellFormed s) (K : Silmaril.Wasm.Game.Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      dcompositeObs (I.closedD P s K) f := by
  have hforget : (I.closedD P s K).toStrategy = I.closedWith P s K := forget_closedD P s K
  have hdiv : ∀ b : Behaviour Val, (b = .diverges ∧ [.inr (.ask f)] ∈ (I.closedD P s K).div) ↔
      (b = .diverges ∧ Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1)) :=
    fun _ => and_congr_right fun _ => mem_div_closedD_iff f
  rw [adequacy_profile hw K hK f]
  ext b
  show (b ∈ compositeObs (I.closedWith P s K) f ∨
      (b = .diverges ∧ Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1))) ↔
    ((∃ w, Responds (I.closedD P s K).toStrategy f w ∧
      b = Answer.toBehaviour (ft := I.exports.get f.1) w) ∨
      (b = .diverges ∧ [.inr (.ask f)] ∈ (I.closedD P s K).div))
  rw [hforget, hdiv b]
  constructor
  · rintro ((hans | ⟨hb, hno⟩) | hd)
    · exact .inl hans
    · exact .inr ⟨hb, diverges_of_no_answer hw hK hno⟩
    · exact .inr hd
  · rintro (hans | hd)
    · exact .inl (.inl hans)
    · exact .inr hd

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
