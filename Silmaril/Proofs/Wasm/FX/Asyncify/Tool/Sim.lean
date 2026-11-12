module

public import Silmaril.Wasm.FX.Asyncify.Tool.Sys.Defs

/-!
# Simulations of deterministic closed systems

`beh_eq_of_sim`: a simulation `R` in which every source step is matched by target steps, either
at least one or none with a decreasing measure (stuttering), and in which source stops are
matched by the same target stop, gives equal behaviours, divergence included. Divergence is
carried by `IsSim.progress`: the stuttering steps (no target step, a smaller measure) cannot go on
forever, so a diverging source makes the target take steps.

New proofs (moved from `Silmaril/Raw/Wasm/FX/Asyncify/Tool/Sim.lean` and restyled).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

variable {X Y σ : Type}

theorem runN_add (step : X → SRes X σ) (m n : Nat) (x : X) :
    runN step (m + n) x =
      match runN step m x with
      | .next y => runN step n y
      | .stop o => .stop o := by
  induction m generalizing x with
  | zero => simp [runN]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [runN]
    cases step x with
    | next x' => exact ih x'
    | stop o => rfl

theorem runN_add_next {step : X → SRes X σ} {m n : Nat} {x y : X} (h : runN step m x = .next y) :
    runN step (m + n) x = runN step n y := by
  rw [runN_add, h]

theorem runN_stop_mono {step : X → SRes X σ} {n n' : Nat} {x : X} {o : Obs σ}
    (h : runN step n x = .stop o) (hn : n ≤ n') : runN step n' x = .stop o := by
  induction n generalizing x n' with
  | zero => simp [runN] at h
  | succ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    simp only [runN] at h ⊢
    cases hs : step x with
    | next x' => rw [hs] at h; exact ih h (by omega)
    | stop o' => rw [hs] at h; exact h

theorem runN_next_mono {step : X → SRes X σ} {n m : Nat} {x y : X}
    (h : runN step n x = .next y) (hm : m ≤ n) : ∃ z, runN step m x = .next z := by
  cases hr : runN step m x with
  | next z => exact ⟨z, rfl⟩
  | stop o => rw [runN_stop_mono hr hm] at h; cases h

section Sim

variable (s : X → SRes X σ) (t : Y → SRes Y σ) (R : X → Y → Prop) (μ : X → Nat)

/-- The hypotheses of a stuttering simulation. -/
structure IsSim : Prop where
  stop : ∀ x y o, R x y → s x = .stop o → ∃ n, runN t n y = .stop o
  next : ∀ x y x', R x y → s x = .next x' →
    ∃ n y', runN t n y = .next y' ∧ R x' y' ∧ (0 < n ∨ μ x' < μ x)

variable {s t R μ}

theorem IsSim.stops (hS : IsSim s t R μ) {n : Nat} :
    ∀ {x y o}, R x y → runN s n x = .stop o → ∃ m, runN t m y = .stop o := by
  induction n with
  | zero => intro x y o _ h; simp [runN] at h
  | succ n ih =>
    intro x y o hR h
    simp only [runN] at h
    cases hs : s x with
    | stop o' =>
      rw [hs] at h; cases h
      exact hS.stop x y _ hR hs
    | next x' =>
      rw [hs] at h
      obtain ⟨k, y', hk, hR', -⟩ := hS.next x y x' hR hs
      obtain ⟨m, hm⟩ := ih hR' h
      exact ⟨k + m, by rw [runN_add_next hk]; exact hm⟩

/-- A source run from `x` that never stops. -/
def Diverges (s : X → SRes X σ) (x : X) : Prop := ∀ n, ∃ x', runN s n x = .next x'

theorem Diverges.step {x x' : X} (hdiv : Diverges s x) (hs : s x = .next x') : Diverges s x' := by
  intro n
  obtain ⟨z, hz⟩ := hdiv (n + 1)
  have hz' : runN s n x' = .next z := by simpa only [runN, hs] using hz
  exact ⟨z, hz'⟩

theorem Diverges.first {x : X} (hdiv : Diverges s x) : ∃ x', s x = .next x' := by
  obtain ⟨x1, hx1⟩ := hdiv 1
  cases hs : s x with
  | next x' => exact ⟨x', rfl⟩
  | stop o =>
    have h1 : runN s 1 x = .stop o := by simp only [runN, hs]
    cases h1.symm.trans hx1

/-- **Progress**: from a related pair and a diverging source, the target takes a positive number
of steps to a related pair whose source still diverges (by induction on the measure, through
the stuttering steps). -/
theorem IsSim.progress (hS : IsSim s t R μ) (k : Nat) :
    ∀ x y, μ x = k → R x y → Diverges s x →
      ∃ j x' y', 0 < j ∧ runN t j y = .next y' ∧ R x' y' ∧ Diverges s x' := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x y hk hR hdiv
    obtain ⟨x', hs⟩ : ∃ x', s x = .next x' := hdiv.first
    have hdiv' : Diverges s x' := hdiv.step hs
    obtain ⟨j, y', hj, hR', hdec⟩ := hS.next x y x' hR hs
    by_cases hj0 : 0 < j
    · exact ⟨j, x', y', hj0, hj, hR', hdiv'⟩
    · have hj0' : j = 0 := by omega
      have hy : y = y' := by simpa only [hj0', runN, SRes.next.injEq] using hj
      have hlt : μ x' < k := by omega
      exact ih (μ x') hlt x' y rfl (hy ▸ hR') hdiv'

theorem IsSim.diverges (hS : IsSim s t R μ) (N : Nat) :
    ∀ x y, R x y → Diverges s x → ∃ y', runN t N y = .next y' := by
  induction N with
  | zero => intro x y _ _; exact ⟨y, rfl⟩
  | succ N ih =>
    intro x y hR hdiv
    obtain ⟨j, x', y', hj, hrun, hR', hdiv'⟩ := hS.progress (μ x) x y rfl hR hdiv
    obtain ⟨y'', hy''⟩ := ih x' y' hR' hdiv'
    have hlong : runN t (j + N) y = .next y'' := (runN_add_next hrun).trans hy''
    exact runN_next_mono hlong (by omega)

/-- Two stops of one run have the same outcome. -/
theorem stop_eq {step : X → SRes X σ} {n m : Nat} {x : X} {o o' : Obs σ}
    (h1 : runN step n x = .stop o) (h2 : runN step m x = .stop o') : o = o' := by
  have e1 : runN step (max n m) x = .stop o := runN_stop_mono h1 (Nat.le_max_left n m)
  have e2 : runN step (max n m) x = .stop o' := runN_stop_mono h2 (Nat.le_max_right n m)
  exact SRes.stop.inj (e1.symm.trans e2)

/-- A run stops or diverges. -/
theorem stop_or_diverges (step : X → SRes X σ) (x : X) :
    (∃ m o, runN step m x = .stop o) ∨ Diverges step x := by
  by_cases hstop : ∃ m o, runN step m x = .stop o
  · exact .inl hstop
  · refine .inr fun n => ?_
    cases h : runN step n x with
    | next x' => exact ⟨x', rfl⟩
    | stop o => exact absurd ⟨n, o, h⟩ hstop

theorem IsSim.beh_sub (hS : IsSim s t R μ) {x : X} {y : Y} (hR : R x y) : beh s x ⊆ beh t y := by
  rintro b (⟨n, hn⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl (hS.stops hR hn)
  · exact Or.inr ⟨rfl, fun N => hS.diverges N x y hR hdiv⟩

theorem IsSim.beh_sup (hS : IsSim s t R μ) {x : X} {y : Y} (hR : R x y) : beh t y ⊆ beh s x := by
  rintro b (⟨n, hn⟩ | ⟨rfl, hdiv⟩)
  · show b ∈ beh s x
    rcases stop_or_diverges s x with ⟨m, o, hm⟩ | hdivs
    · obtain ⟨m', hm'⟩ := hS.stops hR hm
      have ho : o = b := stop_eq hm' hn
      exact Or.inl ⟨m, ho ▸ hm⟩
    · obtain ⟨y', hy'⟩ := hS.diverges n x y hR hdivs
      cases hn.symm.trans hy'
  · show Obs.diverges ∈ beh s x
    rcases stop_or_diverges s x with ⟨m, o, hm⟩ | hdivs
    · obtain ⟨m', hm'⟩ := hS.stops hR hm
      obtain ⟨y', hy'⟩ := hdiv m'
      cases hm'.symm.trans hy'
    · exact Or.inr ⟨rfl, hdivs⟩

theorem beh_eq_of_sim (hS : IsSim s t R μ) {x : X} {y : Y} (hR : R x y) : beh s x = beh t y :=
  Set.Subset.antisymm (hS.beh_sub hR) (hS.beh_sup hR)

end Sim

/-- Behaviours do not change along deterministic steps. -/
theorem beh_shift {step : X → SRes X σ} {k : Nat} {y y' : X} (h : runN step k y = .next y') :
    beh step y = beh step y' := by
  ext b
  simp only [beh, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨n, hn⟩ | ⟨rfl, hdiv⟩)
    · refine Or.inl ⟨n, ?_⟩
      have := runN_stop_mono hn (Nat.le_add_left n k)
      rwa [runN_add_next h] at this
    · exact Or.inr ⟨rfl, fun n => by
        obtain ⟨z, hz⟩ := hdiv (k + n)
        rw [runN_add_next h] at hz
        exact ⟨z, hz⟩⟩
  · rintro (⟨n, hn⟩ | ⟨rfl, hdiv⟩)
    · exact Or.inl ⟨k + n, by rw [runN_add_next h]; exact hn⟩
    · exact Or.inr ⟨rfl, fun n => by
        obtain ⟨z, hz⟩ := hdiv n
        have : runN step (k + n) y = .next z := by rw [runN_add_next h]; exact hz
        exact runN_next_mono this (Nat.le_add_left n k)⟩

end Silmaril.Wasm.FX.Asyncify.Tool
