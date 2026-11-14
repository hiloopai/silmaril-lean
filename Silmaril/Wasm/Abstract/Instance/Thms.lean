module

public import Silmaril.Wasm.Abstract.Instance.Defs
public import Silmaril.Games.Abstract.SigBridge.Thms
public import Silmaril.Wasm.Det.Game.Instance.Thms

/-!
# Scalar Wasm instances as abstract machines: theorems

* `strategyIso_strategy`: state erasure of the instance machine is the instance
  strategy `I.strategy P s`, read as a trace model. The square
  "instance → machine → trace model" commutes with "instance → strategy".
* `machine_tau_free`: the machine has no silent steps.
* `detMod_iff_detUpTo`: for any strategy of `E ↠ F`, determinism modulo traps
  (`DetMod`) is `DetUpTo` of the proponent trap moves on the trace model.
* `denote_detUpTo`: a deterministic module (`DetModule`) with typed exports has
  a deterministic trace model modulo traps, under every profile.
-/

public section

namespace Silmaril.Wasm.Abstract

universe u

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Game Silmaril.Wasm.Det.Game
open Silmaril.Wasm.Numerics (Profile)

/-- State erasure of the instance machine is the instance strategy. -/
theorem strategyIso_strategy (I : ScalarInstance) (P : Profile)
    (s : Silmaril.Wasm.Execution.Core.Store Nat) :
    SigBridge.strategyIso (I.strategy P s) = (machine I P s).denote :=
  SigBridge.strategyIso_ofLTS (I.lts P s)

/-- The instance machine has no silent steps. -/
theorem machine_tau_free (I : ScalarInstance) (P : Profile)
    (s : Silmaril.Wasm.Execution.Core.Store Nat) {x y : (machine I P s).State} :
    ¬ (machine I P s).step x none y := by
  rintro ⟨m, h, -⟩
  cases h

/-- Proponent moves of `E ↠ F` are the non-Opponent moves. -/
theorem move_isP_iff_not_isO {E F : Sig.{u}} {m : Move E F} : m.IsP ↔ ¬ m.IsO := by
  rcases m with (_ | _) | (_ | _) <;> simp [Move.IsO, Move.IsP]

/-- Determinism modulo traps is `DetUpTo` the Proponent trap moves. -/
theorem detMod_iff_detUpTo {E F : Sig.{u}} (tF : Traps F) (σ : Strategy E F) :
    DetMod tF σ ↔ (SigBridge.strategyIso σ).DetUpTo (PTrap (E := E) tF) := by
  constructor
  · intro h s p q hp hq hpo hqo hs
    exact h s p q hp hq (move_isP_iff_not_isO.2 hpo) (move_isP_iff_not_isO.2 hqo) hs
  · intro h s p q hp hq hpo hqo hs
    exact h hp hq (move_isP_iff_not_isO.1 hpo) (move_isP_iff_not_isO.1 hqo) hs

/-- A deterministic module has a trace model that is deterministic modulo
traps, under every profile. -/
theorem denote_detUpTo {I : ScalarInstance} {P : Profile}
    {s₀ : Silmaril.Wasm.Execution.Core.Store Nat}
    (hD : Silmaril.Wasm.Det.Core.DetModule P (entry I) s₀) (ht : ExportsTyped I s₀) :
    (machine I P s₀).denote.DetUpTo (PTrap (E := I.E) (wasmTraps I.exports)) := by
  rw [← strategyIso_strategy]
  exact (detMod_iff_detUpTo _ _).1 (detMod_strategy hD ht)

end Silmaril.Wasm.Abstract
