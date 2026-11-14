module

public import Silmaril.Games.Abstract.SigLink.Defs
public import Silmaril.Games.Abstract.Link.Thms
public import Silmaril.Games.Abstract.SigBridge.Thms

/-!
# Composition as linking: proofs

Zipped plays are exactly the views of joint plays, so generic linking in the
situation `sigLink E F G` is `Strategy.comp`.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SigLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SigLink
  Silmaril.Games.Abstract.TraceModel

universe u

variable {E F G : Sig.{u}}

theorem exists_joint {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∃ u : List (Ev E ⊕ Ev F ⊕ Ev G),
      u.filterMap p₁ = s ∧ u.filterMap p₂ = t ∧ u.filterMap pe = p := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | left a _ ih =>
    obtain ⟨u, h₁, h₂, h₃⟩ := ih
    exact ⟨.inl a :: u, by simp [p₁, h₁], by simp [List.filterMap_cons, p₂, h₂], by simp [pe, h₃]⟩
  | right c _ ih =>
    obtain ⟨u, h₁, h₂, h₃⟩ := ih
    exact ⟨.inr (.inr c) :: u, by simp [List.filterMap_cons, p₁, h₁], by simp [p₂, h₂], by simp [pe, h₃]⟩
  | sync b _ ih =>
    obtain ⟨u, h₁, h₂, h₃⟩ := ih
    exact ⟨.inr (.inl b) :: u, by simp [p₁, h₁], by simp [p₂, h₂],
      by simp [List.filterMap_cons, pe, h₃]⟩

theorem strategyIso_comp (σ : Strategy E F) (τ : Strategy F G) :
    SigBridge.strategyIso (σ.comp τ) =
      TraceModel.link (sigLink E F G) (SigBridge.strategyIso σ) (SigBridge.strategyIso τ) := by
  apply le_antisymm
  · rintro p ⟨s, hs, t, ht, hz⟩
    obtain ⟨u, rfl, rfl, rfl⟩ := exists_joint hz
    exact filterMap_mem_hide (f := (sigLink E F G).ext)
      (mem_inf_pull.2 ⟨⟨σ.legal hs, τ.legal ht⟩, hs, ht⟩)
  · refine generate_le_iff.2 ?_
    rintro _ ⟨u, hu, rfl⟩ -
    obtain ⟨-, h₁, h₂⟩ := mem_inf_pull.1 hu
    exact ⟨_, h₁, _, h₂, zip_views u⟩

end Silmaril.Proofs.Games.Abstract.SigLink
