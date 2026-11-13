module

public import Silmaril.Wasm.FX.Asyncify.Tool.Bounded.Defs

/-!
# A system that stops at bad states: runs and behaviours

`step₂` agrees with `step₁` away from `Bad` states and stops with `o x` at a bad state `x`.
Along a run of `step₁` that meets no bad state, the two runs agree (`runN_eq_of_safe`); at the
first bad state the run of `step₂` stops (`runN_first_bad`). So the behaviours of `step₂` are
those of `step₁` when no bad state is reachable, and `{o y}` otherwise, for the first bad
state `y`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Bounded

open Silmaril.Wasm.FX.Asyncify.Tool

variable {X σ : Type} {step₁ step₂ : X → SRes X σ} {Bad : X → Prop} {o : X → Obs σ}

theorem runN_succ_next {step : X → SRes X σ} {x x' : X} (h : step x = .next x') (n : Nat) :
    runN step (n + 1) x = runN step n x' := by
  simp only [runN, h]

theorem safe_next {x x' : X} (hs : Safe step₁ Bad x) (h : step₁ x = .next x') :
    Safe step₁ Bad x' := fun n y hy => hs (n + 1) y (by rw [runN_succ_next h]; exact hy)

theorem safe_here {x : X} (hs : Safe step₁ Bad x) : ¬ Bad x := hs 0 x rfl

/-- Away from bad states the two runs agree. -/
theorem runN_eq_of_safe (hg : ∀ x, ¬ Bad x → step₂ x = step₁ x) :
    ∀ (n : Nat) {x : X}, Safe step₁ Bad x → runN step₂ n x = runN step₁ n x := by
  intro n
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    intro x hs
    have h2 := hg x (safe_here hs)
    cases h1 : step₁ x with
    | next x' =>
      rw [runN_succ_next h1, runN_succ_next (h2.trans h1)]
      exact ih (safe_next hs h1)
    | stop b => simp only [runN, h2, h1]

theorem runN_stop_le {step : X → SRes X σ} {x : X} {b : Obs σ} :
    ∀ {n m : Nat}, runN step n x = .stop b → n ≤ m → runN step m x = .stop b := by
  intro n
  induction n generalizing x with
  | zero => intro m h; cases h
  | succ n ih =>
    intro m h hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    cases hs : step x with
    | next x' =>
      rw [runN_succ_next hs] at h ⊢
      exact ih h (by omega)
    | stop b' =>
      simp only [runN, hs] at h ⊢
      exact h

/-- A run that stops has that stop as its only behaviour. -/
theorem beh_of_runN_stop {step : X → SRes X σ} {x : X} {k : Nat} {b : Obs σ}
    (h : runN step k x = .stop b) : beh step x = {b} := by
  ext b'
  simp only [beh, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨n, hn⟩ | ⟨-, hd⟩)
    · have e1 := runN_stop_le hn (Nat.le_max_left n k)
      have e2 := runN_stop_le h (Nat.le_max_right n k)
      rw [e1] at e2
      cases e2
      rfl
    · obtain ⟨y, hy⟩ := hd k
      rw [h] at hy
      cases hy
  · rintro rfl
    exact Or.inl ⟨k, h⟩

/-- The run of `step₂` up to the first bad state, where it stops. -/
theorem runN_first_bad (hg : ∀ x, ¬ Bad x → step₂ x = step₁ x)
    (hb : ∀ x, Bad x → step₂ x = .stop (o x)) :
    ∀ (n : Nat) {x y : X}, runN step₁ n x = .next y → Bad y →
      (∀ m < n, ∀ z, runN step₁ m x = .next z → ¬ Bad z) →
      runN step₂ (n + 1) x = .stop (o y) := by
  intro n
  induction n with
  | zero =>
    intro x y hy hbad _
    cases hy
    simp only [runN, hb x hbad]
  | succ n ih =>
    intro x y hy hbad hmin
    have hx : ¬ Bad x := hmin 0 (by omega) x rfl
    cases h1 : step₁ x with
    | next x' =>
      rw [runN_succ_next h1] at hy
      rw [runN_succ_next ((hg x hx).trans h1)]
      refine ih hy hbad fun m hm z hz => hmin (m + 1) (by omega) z ?_
      rw [runN_succ_next h1]
      exact hz
    | stop b =>
      simp only [runN, h1] at hy
      cases hy

/-- No bad state reachable: the same behaviours. -/
theorem beh_eq_of_safe (hg : ∀ x, ¬ Bad x → step₂ x = step₁ x) {x : X}
    (hs : Safe step₁ Bad x) : beh step₂ x = beh step₁ x := by
  have := runN_eq_of_safe hg
  ext b
  simp only [beh, Set.mem_union, Set.mem_ofPred_eq, this _ hs]

/-- A bad state reachable: the only behaviour is the stop at the first one. -/
theorem beh_eq_of_bad (hg : ∀ x, ¬ Bad x → step₂ x = step₁ x)
    (hb : ∀ x, Bad x → step₂ x = .stop (o x)) {x : X} (hns : ¬ Safe step₁ Bad x) :
    ∃ n y, runN step₁ n x = .next y ∧ Bad y ∧ beh step₂ x = {o y} := by
  classical
  have hex : ∃ n, ∃ y, runN step₁ n x = .next y ∧ Bad y := by
    simp only [Safe, not_forall, not_not] at hns
    obtain ⟨n, y, hy, hbad⟩ := hns
    exact ⟨n, y, hy, hbad⟩
  obtain ⟨y, hy, hbad⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, y, hy, hbad, beh_of_runN_stop (k := Nat.find hex + 1) ?_⟩
  refine runN_first_bad hg hb _ hy hbad fun m hm z hz hz' => ?_
  exact Nat.find_min hex hm ⟨z, hz, hz'⟩

/-- Every behaviour of `step₂` is one of `step₁` or a stop at a bad state. -/
theorem beh_sub (hg : ∀ x, ¬ Bad x → step₂ x = step₁ x)
    (hb : ∀ x, Bad x → step₂ x = .stop (o x)) (x : X) :
    beh step₂ x ⊆ beh step₁ x ∪ {b | ∃ y, Bad y ∧ b = o y} := by
  classical
  by_cases hs : Safe step₁ Bad x
  · rw [beh_eq_of_safe hg hs]
    exact Set.subset_union_left
  · obtain ⟨_, y, -, hbad, he⟩ := beh_eq_of_bad hg hb hs
    rw [he]
    intro b hb'
    exact Or.inr ⟨y, hbad, hb'⟩

/-! ## The bounded target system -/

theorem stepB_of_not_oob {cap : Nat} {E : Env} {c : Cfg} (h : ¬ OOB cap c) :
    stepB cap E c = step E c := by
  simp only [stepB, h, ↓reduceIte]

theorem tgtStepB_good {cap : Nat} {E : Env} {H : Host σ} (t : TSt σ) (h : ¬ OOB cap t.cfg) :
    tgtStepB cap E H t = tgtStep E H t := by
  unfold tgtStepB tgtStep
  rw [stepB_of_not_oob h]
  cases step E t.cfg <;> rfl

theorem tgtStepB_bad {cap : Nat} {E : Env} {H : Host σ} (t : TSt σ) (h : OOB cap t.cfg) :
    tgtStepB cap E H t = .stop (.trap t.host) := by
  simp only [tgtStepB, stepB, h, ↓reduceIte]

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Bounded
