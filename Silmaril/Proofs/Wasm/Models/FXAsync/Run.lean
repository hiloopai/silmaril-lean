module

public import Silmaril.Wasm.Models.FXAsync.Defs

/-!
# Runs of deterministic machines, and behaviours under a stuttering simulation

Generic facts about `runN` for a step function `step : C → Res C V`:

* `runN_add`: running `a + b` steps is running `a` steps, then `b` more if nothing stopped;
* `runN_stop_add`: a stopped run stays stopped;
* **`beh_eq_of_sim`**: if every step of `s` from `x` is matched by a positive number of steps of
  `t` from `g x` (`SimStep s t g`), then `s` from `x` and `t` from `g x` have the same
  behaviours. Both are functions, so the simulation needs no backward half: a target that stops
  with `o` cannot face a diverging source, and a stopped source fixes the target's outcome;
* `beh_of_stop`: a run that stops has exactly one behaviour.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsync

open Silmaril.Wasm.Models.FXAsync

variable {C D V : Type}

/-- Continue a result. -/
def _root_.Silmaril.Wasm.Models.FXAsync.Res.andThen : Res C V → (C → Res C V) → Res C V
  | .next c, k => k c
  | .stop o, _ => .stop o

theorem runN_add (step : C → Res C V) (a b : Nat) (c : C) :
    runN step (a + b) c = (runN step a c).andThen (runN step b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, runN, Res.andThen]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [runN]
    cases step c with
    | next c' => exact ih c'
    | stop o => rfl

theorem runN_stop_add {step : C → Res C V} {n : Nat} {c : C} {o : Outcome V}
    (h : runN step n c = .stop o) (k : Nat) : runN step (n + k) c = .stop o := by
  rw [runN_add, h]; rfl

theorem runN_stop_le {step : C → Res C V} {n m : Nat} {c : C} {o : Outcome V}
    (h : runN step n c = .stop o) (hle : n ≤ m) : runN step m c = .stop o := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact runN_stop_add h k

/-- Every step of `s` is matched by a positive number of steps of `t`. -/
def SimStep (s : C → Res C V) (t : D → Res D V) (g : C → D) : Prop :=
  ∀ x, ∃ n, 0 < n ∧ runN t n (g x) = (s x).map g

theorem sim_runN {s : C → Res C V} {t : D → Res D V} {g : C → D} (hsim : SimStep s t g)
    (n : Nat) (x : C) : ∃ m, n ≤ m ∧ runN t m (g x) = (runN s n x).map g := by
  induction n generalizing x with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ n ih =>
    obtain ⟨k, hk, hrun⟩ := hsim x
    cases hs : s x with
    | next x' =>
      obtain ⟨m, hm, hrun'⟩ := ih x'
      have hstep : runN s (n + 1) x = runN s n x' := by simp only [runN, hs]
      refine ⟨k + m, by omega, ?_⟩
      rw [runN_add, hrun, hs, hstep]
      exact hrun'
    | stop o =>
      have hstep : runN s (n + 1) x = .stop o := by simp only [runN, hs]
      have htk : runN t k (g x) = .stop o := by rw [hrun, hs]; rfl
      exact ⟨k + (n + 1), by omega, by rw [hstep]; exact runN_stop_add htk _⟩

theorem runN_next_or_stop (step : C → Res C V) (n : Nat) (c : C) :
    (∃ c', runN step n c = .next c') ∨ ∃ o, runN step n c = .stop o := by
  cases runN step n c with
  | next c' => exact .inl ⟨c', rfl⟩
  | stop o => exact .inr ⟨o, rfl⟩

/-- A stopped source run is a stopped target run. -/
theorem sim_stop {s : C → Res C V} {t : D → Res D V} {g : C → D} (hsim : SimStep s t g)
    {n : Nat} {x : C} {o : Outcome V} (h : runN s n x = .stop o) :
    ∃ m, runN t m (g x) = .stop o := by
  obtain ⟨m, -, hm⟩ := sim_runN hsim n x
  exact ⟨m, by rw [hm, h]; rfl⟩

/-- A target that stops at `m` makes every source run of `m` steps stop, with that outcome. -/
theorem sim_stop_back {s : C → Res C V} {t : D → Res D V} {g : C → D} (hsim : SimStep s t g)
    {m : Nat} {x : C} {o : Outcome V} (h : runN t m (g x) = .stop o) :
    runN s m x = .stop o := by
  obtain ⟨m', hle, hm'⟩ := sim_runN hsim m x
  have ht : runN t m' (g x) = .stop o := runN_stop_le h hle
  cases hs : runN s m x with
  | next c' =>
    have hbad : runN t m' (g x) = .next (g c') := by rw [hm', hs]; rfl
    rw [ht] at hbad; cases hbad
  | stop o' =>
    have hgood : runN t m' (g x) = .stop o' := by rw [hm', hs]; rfl
    rw [ht] at hgood; cases hgood; rfl

/-- **Equal behaviours under a stuttering simulation of deterministic machines.** -/
theorem beh_eq_of_sim {s : C → Res C V} {t : D → Res D V} {g : C → D} (hsim : SimStep s t g)
    (x : C) : beh s x = beh t (g x) := by
  ext b
  constructor
  · rintro (⟨n, o, h, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨m, hm⟩ := sim_stop hsim h
      exact .inl ⟨m, o, hm, rfl⟩
    · refine .inr ⟨rfl, fun n => ?_⟩
      rcases runN_next_or_stop t n (g x) with hnext | ⟨o, ho⟩
      · exact hnext
      · obtain ⟨c', hc'⟩ := hdiv n
        rw [sim_stop_back hsim ho] at hc'; cases hc'
  · rintro (⟨m, o, h, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact .inl ⟨m, o, sim_stop_back hsim h, rfl⟩
    · refine .inr ⟨rfl, fun n => ?_⟩
      rcases runN_next_or_stop s n x with hnext | ⟨o, ho⟩
      · exact hnext
      · obtain ⟨m, hm⟩ := sim_stop hsim ho
        obtain ⟨c', hc'⟩ := hdiv m
        rw [hm] at hc'; cases hc'


/-- A run that stops has exactly one behaviour. -/
theorem beh_of_stop {step : C → Res C V} {n : Nat} {c : C} {o : Outcome V}
    (h : runN step n c = .stop o) : beh step c = {o.toObs} := by
  ext b
  constructor
  · rintro (⟨m, o', hm, rfl⟩ | ⟨rfl, hdiv⟩)
    · have h1 : runN step (n + m) c = .stop o := runN_stop_add h m
      have h2 : runN step (n + m) c = .stop o' := by
        rw [Nat.add_comm]; exact runN_stop_add hm n
      rw [h1] at h2; cases h2; rfl
    · obtain ⟨c', hc'⟩ := hdiv n
      rw [h] at hc'; cases hc'
  · rintro rfl
    exact .inl ⟨n, o, h, rfl⟩

end Silmaril.Proofs.Wasm.Models.FXAsync
