module

public import Silmaril.Games.Abstract.SigLink.Defs
public import Silmaril.Games.Abstract.Link.Thms
public import Silmaril.Games.Abstract.SigBridge.Thms
import Silmaril.Proofs.Games.Abstract.SigLink.Basic

/-!
# Composition as linking: theorems

* `strategyIso_comp`: generic linking in the situation `sigLink E F G` is the
  existing composition `Strategy.comp`, read through `strategyIso`.
* `denote_link_ofLTS`: for transition systems with receptive traces, the
  linked machine erases to the composite of their strategies.

Together with `Silmaril.Wasm.Game` (`link_is_composition_profile`: Wasm
linking of scalar instances is `Strategy.comp`), this places Wasm linking
inside the generic linking of `Silmaril.Games.Abstract.Link`.
-/

public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

variable {E F G : Sig.{u}}

/-- Generic linking of `E ↠ F` with `F ↠ G` is `Strategy.comp`. -/
theorem SigBridge.strategyIso_comp (σ : Strategy E F) (τ : Strategy F G) :
    SigBridge.strategyIso (σ.comp τ) =
      TraceModel.link (sigLink E F G) (SigBridge.strategyIso σ) (SigBridge.strategyIso τ) :=
  Silmaril.Proofs.Games.Abstract.SigLink.strategyIso_comp σ τ

/-- For transition systems with receptive traces, erasing the linked machine
gives the composite of their strategies. -/
theorem Machine.denote_link_ofLTS {L₁ : LTS E F} {L₂ : LTS F G}
    (h₁ : (sigGame E F).Closed (Machine.ofLTS L₁).traces)
    (h₂ : (sigGame F G).Closed (Machine.ofLTS L₂).traces) :
    (Machine.link (sigLink E F G) (Machine.ofLTS L₁) (Machine.ofLTS L₂)).denote =
      SigBridge.strategyIso ((Strategy.ofLTS L₁).comp (Strategy.ofLTS L₂)) := by
  rw [Machine.denote_link h₁ h₂, SigBridge.strategyIso_comp, SigBridge.strategyIso_ofLTS,
    SigBridge.strategyIso_ofLTS]

end Silmaril.Games.Abstract
