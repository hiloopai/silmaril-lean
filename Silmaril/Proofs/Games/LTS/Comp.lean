module

public import Silmaril.Games.LTS.Defs
public import Silmaril.Games.Composition.Defs
import Silmaril.Proofs.Games.LTS.Basic

/-!
# Transition systems of strategies and their composition: proofs

Proofs for `Silmaril.Games.LTS.Thms`: the transition system of a strategy denotes
it, and the parallel composition of transition systems denotes the composite
strategy.
-/

public section

namespace Silmaril.Proofs.Games.LTS

open Silmaril.Games

universe u

variable {E F G : Sig.{u}}

theorem toLTS_run {σ : Strategy E F} {x y : σ.toLTS.State} {s : List (Move E F)}
    (h : σ.toLTS.Run x s y) : y = x ++ s ∧ (s ≠ [] → x ++ s ∈ σ) := by
  induction h with
  | nil => simp
  | tau hs _ _ => cases hs
  | vis hs hr ih =>
    rename_i x₀ y₀ z₀ o₀ s₀
    cases hs with
    | mk o hmem =>
      obtain ⟨h₁, h₂⟩ := ih
      refine ⟨by simp [h₁], fun _ => ?_⟩
      by_cases hs : s₀ = []
      · subst hs; simpa using hmem
      · simpa using h₂ hs

theorem run_toLTS {σ : Strategy E F} {x : List (Move E F)} {s : List (Move E F)}
    (h : x ++ s ∈ σ) : σ.toLTS.Run x s (x ++ s) := by
  induction s generalizing x with
  | nil => simpa using LTS.Run.nil (L := σ.toLTS) x
  | cons o s ih =>
    have h₁ : x ++ [o] ∈ σ := σ.of_prefix h (by simp)
    have := ih (x := x ++ [o]) (by simpa using h)
    simpa using LTS.Run.vis (Strategy.TStep.mk x o h₁) this

theorem denotes_toLTS (σ : Strategy E F) : σ.toLTS.Denotes σ := by
  intro p
  constructor
  · rintro ⟨y, h⟩
    obtain ⟨-, h⟩ := toLTS_run h
    by_cases hp : p = []
    · subst hp; exact σ.nil_mem
    · simpa using h hp
  · intro hp
    exact ⟨_, run_toLTS (x := []) (by simpa using hp)⟩

theorem comp_taus₁ {L₁ : LTS E F} {L₂ : LTS F G} {x x' : L₁.State} (y : L₂.State)
    (h : L₁.Run x [] x') : (L₁.comp L₂).Run (x, y) [] (x', y) := by
  generalize hl : ([] : List (Move E F)) = l at h
  induction h with
  | nil => exact .nil _
  | tau hs _ ih => exact .tau (LTS.CompStep.tau₁ hs) (ih hl)
  | vis => cases hl

theorem comp_taus₂ {L₁ : LTS E F} {L₂ : LTS F G} (x : L₁.State) {y y' : L₂.State}
    (h : L₂.Run y [] y') : (L₁.comp L₂).Run (x, y) [] (x, y') := by
  generalize hl : ([] : List (Move F G)) = l at h
  induction h with
  | nil => exact .nil _
  | tau hs _ ih => exact .tau (LTS.CompStep.tau₂ hs) (ih hl)
  | vis => cases hl

theorem comp_run {L₁ : LTS E F} {L₂ : LTS F G} {z z' : (L₁.comp L₂).State}
    {p : List (Move E G)} (h : (L₁.comp L₂).Run z p z') :
    ∃ s t, L₁.Run z.1 s z'.1 ∧ L₂.Run z.2 t z'.2 ∧ Zip s t p := by
  induction h with
  | nil => exact ⟨[], [], .nil _, .nil _, .nil⟩
  | tau hs _ ih =>
    obtain ⟨s, t, h₁, h₂, hz⟩ := ih
    cases hs with
    | tau₁ hs => exact ⟨s, t, .tau hs h₁, h₂, hz⟩
    | tau₂ hs => exact ⟨s, t, h₁, .tau hs h₂, hz⟩
    | sync f hs ht => exact ⟨_, _, .vis hs h₁, .vis ht h₂, .sync f hz⟩
  | vis hs _ ih =>
    obtain ⟨s, t, h₁, h₂, hz⟩ := ih
    cases hs with
    | left e hs => exact ⟨_, t, .vis hs h₁, h₂, .left e hz⟩
    | right g hs => exact ⟨s, _, h₁, .vis hs h₂, .right g hz⟩

theorem run_comp {L₁ : LTS E F} {L₂ : LTS F G} {s : List (Move E F)} {t : List (Move F G)}
    {p : List (Move E G)} (hz : Zip s t p) :
    ∀ {x x' y y'}, L₁.Run x s x' → L₂.Run y t y' → (L₁.comp L₂).Run (x, y) p (x', y') := by
  induction hz with
  | nil =>
    intro x x' y y' h₁ h₂
    exact run_append (comp_taus₁ y h₁) (comp_taus₂ x' h₂)
  | left e _ ih =>
    intro x x' y y' h₁ h₂
    obtain ⟨x₁, x₂, ht, hs, hr⟩ := run_cons_inv h₁
    exact run_append (comp_taus₁ y ht) (.vis (LTS.CompStep.left e hs) (ih hr h₂))
  | right g _ ih =>
    intro x x' y y' h₁ h₂
    obtain ⟨y₁, y₂, ht, hs, hr⟩ := run_cons_inv h₂
    exact run_append (comp_taus₂ x ht) (.vis (LTS.CompStep.right g hs) (ih h₁ hr))
  | sync f _ ih =>
    intro x x' y y' h₁ h₂
    obtain ⟨x₁, x₂, ht₁, hs₁, hr₁⟩ := run_cons_inv h₁
    obtain ⟨y₁, y₂, ht₂, hs₂, hr₂⟩ := run_cons_inv h₂
    exact run_append (comp_taus₁ y ht₁) (run_append (comp_taus₂ x₁ ht₂)
      (.tau (LTS.CompStep.sync f hs₁ hs₂) (ih hr₁ hr₂)))

theorem denotes_comp {L₁ : LTS E F} {L₂ : LTS F G} {σ : Strategy E F} {τ : Strategy F G}
    (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) : (L₁.comp L₂).Denotes (σ.comp τ) := by
  intro p
  rw [Strategy.mem_comp]
  constructor
  · rintro ⟨z, h⟩
    obtain ⟨s, t, hs, ht, hz⟩ := comp_run h
    exact ⟨s, (h₁ s).1 ⟨_, hs⟩, t, (h₂ t).1 ⟨_, ht⟩, hz⟩
  · rintro ⟨s, hs, t, ht, hz⟩
    obtain ⟨x', hx⟩ := (h₁ s).2 hs
    obtain ⟨y', hy⟩ := (h₂ t).2 ht
    exact ⟨_, run_comp hz hx hy⟩

end Silmaril.Proofs.Games.LTS
