module

public import Silmaril.Games.DivLTSComp.Defs
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Proofs.Games.DivLTSComp.Main

/-!
# Composition of transition systems with divergence: proofs of the header laws

Proofs for `Silmaril.Games.DivLTSComp.Thms`: the divergent and the infinite plays of
a composite system are those of the composite strategy, assembled from the
inclusions of `Silmaril.Proofs.Games.DivLTSComp.Main`.
-/

public section

namespace Silmaril.Proofs.Games.DivLTSComp.Laws

open Silmaril.Games Silmaril.Games.DStrategy Silmaril.Proofs.Games.DivLTSComp

universe u

variable {E F G : Sig.{u}} {L₁ : LTS E F} {L₂ : LTS F G} {σ : Strategy E F} {τ : Strategy F G}

/-- The divergent plays of a composite system are those of the composite strategy. -/
theorem ofLTS_comp_div (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) (d₁ : L₁.DivRunning)
    (d₂ : L₂.DivRunning) :
    (ofLTS (L₁.comp L₂)).div = compDiv (ofLTS L₁) (ofLTS L₂) := by
  ext p
  constructor
  · exact div_comp_of_div h₁ h₂ d₁ d₂
  · intro hp
    have hrun : ∃ g, Path .idle p (.run g) := compDiv_run hp
    rcases hp with ⟨s, t, hz, hst⟩ | ⟨i, hi⟩
    · obtain ⟨y, hy, hd⟩ := div_of_local h₁ h₂ hz hst
      exact ⟨⟨y, hy, hd⟩, hrun⟩
    · obtain ⟨y, hy, hd⟩ := div_of_chatter h₁ h₂ i hi
      exact ⟨⟨y, hy, hd⟩, hrun⟩

/-- The infinite plays of a composite system are those of the composite strategy. -/
theorem ofLTS_comp_inf (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) :
    (ofLTS (L₁.comp L₂)).inf = ((ofLTS L₁).comp (ofLTS L₂)).inf := by
  ext I
  constructor
  · exact inf_comp_of_inf h₁ h₂
  · intro hI
    have hsub : I ⊆ ((ofLTS L₁).comp (ofLTS L₂)).toStrategy.plays :=
      ((ofLTS L₁).comp (ofLTS L₂)).inf_sub hI
    obtain ⟨i, hu, rfl⟩ := hI
    exact ⟨inf_of_inter h₁ h₂ i hu, fun q hq => Strategy.legal _ (hsub hq)⟩

end Silmaril.Proofs.Games.DivLTSComp.Laws
