module

public import Silmaril.Wasm.Component.FXRes.ContPool.Defs
public import Silmaril.Wasm.Component.FXRes.ContEngine.Thms

/-!
# Continuations in the table or in a store: live locations and the step method

* `inv_mono`: a step that only kills locations and keeps identities keeps `GInv`;
* `inv_step`: the general step method: each live location after the step either has an origin
  before the step, whose identity it has, or is the one fresh location of the step, with
  identity `next`; origins are not shared;
* live locations under `List.set` and append of thread slots.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContPool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (ContFX)
open Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.FXRes Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Resource
open Silmaril.Wasm.Component.Runtime (Table)

variable {H : Type}

theorem inv_mono {p p' : Pool H} {g : Ghost} (hI : GInv p g) (hf : FreeOK p'.s.tab)
    (hl : ∀ l, Live p' l → Live p l) : GInv p' g :=
  ⟨hf, fun l h => hI.lt l (hl l h), fun l₁ l₂ h₁ h₂ => hI.inj l₁ l₂ (hl _ h₁) (hl _ h₂)⟩

section Method

variable {p p' : Pool H} {g g' : Ghost}

/-- The hypotheses of the step method. -/
structure StepHyp (p p' : Pool H) (g g' : Ghost) (o : Loc → Option Loc) : Prop where
  hsome : ∀ l l₀, Live p' l → o l = some l₀ → Live p l₀ ∧ g'.id l = g.id l₀
  hnone : ∀ l, Live p' l → o l = none → g'.id l = g.next ∧ g.next < g'.next
  honce : ∀ l₁ l₂, Live p' l₁ → Live p' l₂ → o l₁ = none → o l₂ = none → l₁ = l₂
  hinj : ∀ l₁ l₂ l₀, Live p' l₁ → Live p' l₂ → o l₁ = some l₀ → o l₂ = some l₀ → l₁ = l₂
  hnext : g.next ≤ g'.next

theorem step_lt (hI : GInv p g) {o : Loc → Option Loc} (hy : StepHyp p p' g g' o) {l : Loc}
    (hl : Live p' l) : g'.id l < g'.next := by
  cases ho : o l with
  | none =>
    obtain ⟨hid, hlt⟩ := hy.hnone l hl ho
    exact hid ▸ hlt
  | some l₀ =>
    obtain ⟨hl₀, hid⟩ := hy.hsome l l₀ hl ho
    exact hid ▸ Nat.lt_of_lt_of_le (hI.lt l₀ hl₀) hy.hnext

theorem step_ne_mixed (hI : GInv p g) {o : Loc → Option Loc} (hy : StepHyp p p' g g' o)
    {l₁ l₂ : Loc} (h₁ : Live p' l₁) (h₂ : Live p' l₂) (ho₁ : o l₁ = none) {b : Loc}
    (ho₂ : o l₂ = some b) : g'.id l₁ ≠ g'.id l₂ := by
  obtain ⟨hb, hidb⟩ := hy.hsome l₂ b h₂ ho₂
  have hlt : g.id b < g.next := hI.lt b hb
  have hida : g'.id l₁ = g.next := (hy.hnone l₁ h₁ ho₁).1
  omega

theorem step_inj_some (hI : GInv p g) {o : Loc → Option Loc} (hy : StepHyp p p' g g' o)
    {l₁ l₂ a b : Loc} (h₁ : Live p' l₁) (h₂ : Live p' l₂) (ho₁ : o l₁ = some a)
    (ho₂ : o l₂ = some b) (he : g'.id l₁ = g'.id l₂) : l₁ = l₂ := by
  obtain ⟨ha, hida⟩ := hy.hsome l₁ a h₁ ho₁
  obtain ⟨hb, hidb⟩ := hy.hsome l₂ b h₂ ho₂
  have hab : a = b := hI.inj a b ha hb (by rw [← hida, ← hidb]; exact he)
  exact hy.hinj l₁ l₂ a h₁ h₂ ho₁ (hab ▸ ho₂)

/-- **The step method.** -/
theorem inv_step (hI : GInv p g) (hf : FreeOK p'.s.tab) {o : Loc → Option Loc}
    (hy : StepHyp p p' g g' o) : GInv p' g' := by
  refine ⟨hf, fun l hl => step_lt hI hy hl, fun l₁ l₂ h₁ h₂ he => ?_⟩
  cases ho₁ : o l₁ with
  | none =>
    cases ho₂ : o l₂ with
    | none => exact hy.honce l₁ l₂ h₁ h₂ ho₁ ho₂
    | some b => exact absurd he (step_ne_mixed hI hy h₁ h₂ ho₁ ho₂)
  | some a =>
    cases ho₂ : o l₂ with
    | none => exact absurd he.symm (step_ne_mixed hI hy h₂ h₁ ho₂ ho₁)
    | some b => exact step_inj_some hI hy h₁ h₂ ho₁ ho₂ he

end Method

/-! ## Two instances of the method -/

/-- Location `L` is new, with the fresh identity: every other live location was live. -/
theorem inv_fresh {p p' : Pool H} {g : Ghost} (hI : GInv p g) (hf : FreeOK p'.s.tab) (L : Loc)
    (hback : ∀ l, Live p' l → l ≠ L → Live p l) : GInv p' (g.fresh L) := by
  refine inv_step hI hf (o := fun l => if l = L then none else some l)
    { hsome := ?_, hnone := ?_, honce := ?_, hinj := ?_, hnext := Nat.le_succ _ }
  · intro l l₀ hl ho
    have hlL : l ≠ L := fun h => by simp [h] at ho
    have hl₀ : l₀ = l := by simpa [hlL] using ho.symm
    rw [hl₀]
    exact ⟨hback l hl hlL, Function.update_of_ne hlL _ _⟩
  · intro l _ ho
    have hlL : l = L := by by_contra h; simp [h] at ho
    exact hlL ▸ ⟨Function.update_self _ _ _, Nat.lt_succ_self _⟩
  · intro l₁ l₂ _ _ h₁ h₂
    by_cases e₁ : l₁ = L <;> by_cases e₂ : l₂ = L <;> simp_all
  · intro l₁ l₂ l₀ _ _ h₁ h₂
    by_cases e₁ : l₁ = L <;> by_cases e₂ : l₂ = L <;> simp_all

/-- The continuation at `src` moved to `dst`: `src` is dead, and every other live location was
live. -/
theorem inv_move {p p' : Pool H} {g : Ghost} (hI : GInv p g) (hf : FreeOK p'.s.tab)
    {src dst : Loc} (hsrc : Live p src) (hdead : ¬ Live p' src)
    (hback : ∀ l, Live p' l → l ≠ dst → Live p l) : GInv p' (g.move src dst) := by
  refine inv_step hI hf (o := fun l => if l = dst then some src else some l)
    { hsome := ?_, hnone := ?_, honce := ?_, hinj := ?_, hnext := Nat.le_refl _ }
  · intro l l₀ hl ho
    by_cases hld : l = dst
    · have hl₀ : l₀ = src := by simpa [hld] using ho.symm
      rw [hl₀, hld]
      exact ⟨hsrc, Function.update_self _ _ _⟩
    · have hl₀ : l₀ = l := by simpa [hld] using ho.symm
      rw [hl₀]
      exact ⟨hback l hl hld, Function.update_of_ne hld _ _⟩
  · intro l _ ho
    by_cases hld : l = dst <;> simp [hld] at ho
  · intro l₁ _ _ _ h₁
    by_cases hld : l₁ = dst <;> simp [hld] at h₁
  · intro l₁ l₂ l₀ h₁ h₂ ho₁ ho₂
    by_cases e₁ : l₁ = dst <;> by_cases e₂ : l₂ = dst <;> simp_all

/-! ## Live locations -/

theorem live_tab_iff {p : Pool H} {n : ℕ} : Live p (.tab n) ↔ ∃ C, p.s.tab.get? n = some C :=
  Iff.rfl

theorem live_store_of {p : Pool H} {i j : ℕ} {t : ThreadV (CH H)} (hi : p.ts[i]? = some (some t))
    {C : ContFX} (hC : (threadConts t)[j]? = some (some C)) : Live p (.store i j) :=
  ⟨t, hi, C, hC⟩

theorem lt_of_slot {ts : List (Option (ThreadV (CH H)))} {i : ℕ} {t : ThreadV (CH H)}
    (hi : ts[i]? = some (some t)) : i < ts.length := by
  by_contra h
  rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hi
  cases hi

/-- A live store location after replacing slot `i`. -/
theorem live_store_set {s s' : EStore H} {ts : List (Option (ThreadV (CH H)))} {i i' j : ℕ}
    {t t' : ThreadV (CH H)} (hi : ts[i]? = some (some t))
    (h : Live ⟨s', ts.set i (some t')⟩ (.store i' j)) :
    (i' = i ∧ ∃ C, (threadConts t')[j]? = some (some C)) ∨
      (i' ≠ i ∧ Live ⟨s, ts⟩ (.store i' j)) := by
  obtain ⟨u, hu, C, hC⟩ := h
  by_cases hii : i' = i
  · subst hii
    have hu' : (ts.set i' (some t'))[i']? = some (some t') :=
      List.getElem?_set_self (lt_of_slot hi)
    rw [hu'] at hu
    cases hu
    exact .inl ⟨rfl, C, hC⟩
  · have hu' : (ts.set i (some t'))[i']? = ts[i']? := List.getElem?_set_ne (Ne.symm hii)
    rw [hu'] at hu
    exact .inr ⟨hii, u, hu, C, hC⟩

/-- A live store location of another slot is still live after replacing slot `i`. -/
theorem live_store_set_ne {s s' : EStore H} {ts : List (Option (ThreadV (CH H)))} {i i' j : ℕ}
    {x : Option (ThreadV (CH H))} (hii : i' ≠ i) (h : Live ⟨s, ts⟩ (.store i' j)) :
    Live ⟨s', ts.set i x⟩ (.store i' j) := by
  obtain ⟨u, hu, C, hC⟩ := h
  refine ⟨u, ?_, C, hC⟩
  rw [List.getElem?_set_ne (Ne.symm hii)]
  exact hu

/-- A live entry of the replaced slot. -/
theorem live_store_set_self {s' : EStore H} {ts : List (Option (ThreadV (CH H)))} {i j : ℕ}
    {t t' : ThreadV (CH H)} (hi : ts[i]? = some (some t)) {C : ContFX}
    (hC : (threadConts t')[j]? = some (some C)) : Live ⟨s', ts.set i (some t')⟩ (.store i j) :=
  ⟨t', List.getElem?_set_self (lt_of_slot hi), C, hC⟩

/-- Replacing slot `i` by a thread with no more live entries (and possibly another table) kills
locations only. -/
theorem live_set_mono {s s' : EStore H} {ts : List (Option (ThreadV (CH H)))} {i : ℕ}
    {t t' : ThreadV (CH H)} (hi : ts[i]? = some (some t))
    (hK : ∀ (j : ℕ) (C : ContFX), (threadConts t')[j]? = some (some C) →
      ∃ C' : ContFX, (threadConts t)[j]? = some (some C'))
    (htab : ∀ (n : ℕ) (C : ContFX), s'.tab.get? n = some C → ∃ C' : ContFX, s.tab.get? n = some C') :
    ∀ l, Live ⟨s', ts.set i (some t')⟩ l → Live ⟨s, ts⟩ l := by
  intro l hl
  cases l with
  | store i' j =>
    rcases live_store_set (s := s) hi hl with ⟨rfl, C, hC⟩ | ⟨-, h⟩
    · obtain ⟨C', hC'⟩ := hK j C hC
      exact ⟨t, hi, C', hC'⟩
    · exact h
  | tab n =>
    obtain ⟨C, hC⟩ := hl
    exact htab n C hC

end Silmaril.Wasm.Component.FXRes.ContPool
