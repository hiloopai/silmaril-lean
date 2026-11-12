module

public import Silmaril.Games.DivLTS.Defs
public import Silmaril.Games.LTS.Thms
public import Mathlib.Data.List.Basic

/-!
# Functional bisimulations of transition systems with relabelling

`FBisim L₁ L₂`: a map `φ` on states and an injective map `ρ` on moves such that
every step of `L₁` is matched by a step of `L₂` between the images, with the
relabelled label, and every step of `L₂` from an image is such a match. Then
runs correspond (`FBisim.run_fwd`, `FBisim.run_bwd`) and so does silent
divergence (`FBisim.diverges_iff`). A bisimulation whose relabelling fixes
lower moves lifts below any transition system (`FBisim.compLeft`).

Used to read the export phase of an instantiable Wasm system as the
divergence-observing instance system. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Start

open Silmaril.Games

universe u

variable {E₁ F₁ E₂ F₂ : Sig.{u}}

/-- A functional bisimulation from `L₁` to `L₂`, relabelling moves by `ρ`. -/
structure FBisim (L₁ : LTS E₁ F₁) (L₂ : LTS E₂ F₂) where
  /-- The map on states. -/
  φ : L₁.State → L₂.State
  /-- The relabelling of moves. -/
  ρ : Move E₁ F₁ → Move E₂ F₂
  inj : Function.Injective ρ
  /-- Steps are matched. -/
  fwd : ∀ {x : L₁.State} {l : Option (Move E₁ F₁)} {y : L₁.State},
    L₁.step x l y → L₂.step (φ x) (l.map ρ) (φ y)
  /-- Steps from images are matches. -/
  bwd : ∀ {x : L₁.State} {l : Option (Move E₂ F₂)} {z : L₂.State},
    L₂.step (φ x) l z → ∃ l₁ y, l = l₁.map ρ ∧ z = φ y ∧ L₁.step x l₁ y

namespace FBisim

variable {L₁ : LTS E₁ F₁} {L₂ : LTS E₂ F₂} (B : FBisim L₁ L₂)

/-- Runs are matched. -/
theorem run_fwd {x y : L₁.State} {w : List (Move E₁ F₁)} (h : L₁.Run x w y) :
    L₂.Run (B.φ x) (w.map B.ρ) (B.φ y) := by
  induction h with
  | nil x => exact .nil _
  | tau hs _ ih => exact .tau (B.fwd hs) ih
  | vis hs _ ih => exact .vis (B.fwd hs) ih

/-- Runs from images are matches. -/
theorem run_bwd {x : L₁.State} {w' : List (Move E₂ F₂)} {z : L₂.State}
    (h : L₂.Run (B.φ x) w' z) : ∃ w y, w' = w.map B.ρ ∧ z = B.φ y ∧ L₁.Run x w y := by
  generalize hx : B.φ x = x' at h
  induction h generalizing x with
  | nil => exact ⟨[], x, rfl, hx.symm, .nil _⟩
  | tau hs _ ih =>
    obtain ⟨l₁, y, hl, rfl, hy⟩ := B.bwd (hx ▸ hs)
    obtain rfl : l₁ = none := Option.map_eq_none_iff.1 hl.symm
    obtain ⟨w, z, rfl, rfl, hr⟩ := ih rfl
    exact ⟨w, z, rfl, rfl, .tau hy hr⟩
  | vis hs _ ih =>
    obtain ⟨l₁, y, hl, rfl, hy⟩ := B.bwd (hx ▸ hs)
    obtain ⟨m, rfl, rfl⟩ : ∃ m, l₁ = some m ∧ B.ρ m = _ := by
      cases l₁ with
      | none => cases hl
      | some m => exact ⟨m, rfl, (Option.some.inj hl).symm⟩
    obtain ⟨w, z, rfl, rfl, hr⟩ := ih rfl
    exact ⟨m :: w, z, rfl, rfl, .vis hy hr⟩

/-- Runs from images, with relabelled moves. -/
theorem run_iff {x : L₁.State} {w : List (Move E₁ F₁)} {z : L₂.State} :
    L₂.Run (B.φ x) (w.map B.ρ) z ↔ ∃ y, z = B.φ y ∧ L₁.Run x w y := by
  constructor
  · intro h
    obtain ⟨w', y, hw, rfl, hr⟩ := B.run_bwd h
    obtain rfl : w = w' := List.map_injective_iff.2 B.inj hw
    exact ⟨y, rfl, hr⟩
  · rintro ⟨y, rfl, hr⟩
    exact B.run_fwd hr

/-- Silent divergence is matched both ways. -/
theorem diverges_iff {x : L₁.State} : L₂.Diverges (B.φ x) ↔ L₁.Diverges x := by
  constructor
  · intro h
    refine Silmaril.InfiniteTrace.of_map B.φ (fun _ => True) ?_ trivial h
    intro a b _ hab
    obtain ⟨l₁, y, hl, rfl, hy⟩ := B.bwd hab
    obtain rfl : l₁ = none := Option.map_eq_none_iff.1 hl.symm
    exact ⟨y, hy, trivial, rfl⟩
  · exact Silmaril.InfiniteTrace.map B.φ fun _ _ h => B.fwd h

end FBisim

/-! ## Lifting below a lower system -/

variable {X E F₁ F₂ : Sig.{u}}

/-- The relabelling of moves of `X ↠ F₁` by a map on upper events. -/
def upperMap (ρU : Ev F₁ → Ev F₂) : Move X F₁ → Move X F₂ := Sum.map id ρU

theorem upperMap_injective {ρU : Ev F₁ → Ev F₂} (h : Function.Injective ρU) :
    Function.Injective (upperMap (X := X) ρU) :=
  Sum.map_injective.2 ⟨Function.injective_id, h⟩

/-- A bisimulation relabelling only upper moves lifts below a lower system `K`. -/
def FBisim.compLeft {L₁ : LTS E F₁} {L₂ : LTS E F₂} (K : LTS X E) (B : FBisim L₁ L₂)
    (ρU : Ev F₁ → Ev F₂) (hU : Function.Injective ρU) (hρ : B.ρ = upperMap ρU) :
    FBisim (K.comp L₁) (K.comp L₂) where
  φ x := (x.1, B.φ x.2)
  ρ := upperMap ρU
  inj := upperMap_injective hU
  fwd := by
    intro x l y h
    cases h with
    | tau₁ hk => exact .tau₁ hk
    | tau₂ hs => exact .tau₂ (B.fwd hs)
    | left e hk => exact .left e hk
    | right g hs =>
      have hs' := B.fwd hs
      rw [hρ] at hs'
      exact .right (ρU g) hs'
    | sync f hk hs =>
      have hs' := B.fwd hs
      rw [hρ] at hs'
      exact .sync f hk hs'
  bwd := by
    rintro ⟨x₁, x₂⟩ l z h
    cases h with
    | tau₁ hk => exact ⟨none, (_, x₂), rfl, rfl, .tau₁ hk⟩
    | tau₂ hs =>
      obtain ⟨l₁, y, hl, rfl, hy⟩ := B.bwd hs
      obtain rfl : l₁ = none := Option.map_eq_none_iff.1 hl.symm
      exact ⟨none, (x₁, y), rfl, rfl, .tau₂ hy⟩
    | left e hk => exact ⟨some (.inl e), (_, x₂), rfl, rfl, .left e hk⟩
    | right g hs =>
      obtain ⟨l₁, y, hl, rfl, hy⟩ := B.bwd hs
      rw [hρ] at hl
      rcases l₁ with _ | (e | g₁)
      · cases hl
      · cases hl
      · cases hl
        exact ⟨some (.inr g₁), (x₁, y), rfl, rfl, .right g₁ hy⟩
    | sync f hk hs =>
      obtain ⟨l₁, y, hl, rfl, hy⟩ := B.bwd hs
      rw [hρ] at hl
      rcases l₁ with _ | (e | g₁)
      · cases hl
      · cases hl
        exact ⟨none, (_, y), rfl, rfl, .sync _ hk hy⟩
      · cases hl

end Silmaril.Proofs.Wasm.Game.Start
