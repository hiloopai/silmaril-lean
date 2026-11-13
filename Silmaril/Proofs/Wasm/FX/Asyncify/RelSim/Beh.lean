module

public import Silmaril.Wasm.FX.Asyncify.RelSim.Defs

/-!
# Behaviours under a relational stuttering simulation

* `runN_add`, `runN_stop_add`, `runN_stop_le`: runs compose, and a stopped run stays stopped;
* `rsim_runN`: `n` steps of `s` are matched by `m ≥ n` steps of `t`;
* **`beh_eq_of_rsim`**: related configurations have the same behaviours. Both machines are
  functions, so no backward simulation is needed;
* `rsim_of_lock`: a lock-step relation is a simulation with one step;
* `beh_of_stop`: a run that stops has exactly one behaviour.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.RelSim

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.RelSim

variable {C D V : Type}

theorem runN_succ_next {step : C → Res C V} {c c' : C} (h : step c = .next c') (n : Nat) :
    runN step (n + 1) c = runN step n c' := by
  simp only [runN, h]

theorem runN_succ_stop {step : C → Res C V} {c : C} {o : Outcome V} (h : step c = .stop o)
    (n : Nat) : runN step (n + 1) c = .stop o := by
  simp only [runN, h]

theorem runN_add_next {step : C → Res C V} {a : Nat} {c c' : C} (h : runN step a c = .next c')
    (b : Nat) : runN step (a + b) c = runN step b c' := by
  induction a generalizing c with
  | zero =>
    have hc : c = c' := by simpa only [runN, Res.next.injEq] using h
    rw [Nat.zero_add, hc]
  | succ a ih =>
    rw [Nat.succ_add]
    cases hs : step c with
    | next d =>
      have hd : runN step a d = .next c' := by rw [← runN_succ_next hs]; exact h
      rw [runN_succ_next hs]; exact ih hd
    | stop o =>
      have hbad : runN step (a + 1) c = .stop o := runN_succ_stop hs a
      rw [hbad] at h; cases h

theorem runN_stop_add {step : C → Res C V} {n : Nat} {c : C} {o : Outcome V}
    (h : runN step n c = .stop o) (k : Nat) : runN step (n + k) c = .stop o := by
  induction n generalizing c with
  | zero => simp only [runN] at h; cases h
  | succ n ih =>
    rw [Nat.succ_add]
    cases hs : step c with
    | next d =>
      have hd : runN step n d = .stop o := by rw [← runN_succ_next hs]; exact h
      rw [runN_succ_next hs]; exact ih hd
    | stop o' =>
      have h' : runN step (n + 1) c = .stop o' := runN_succ_stop hs n
      rw [h'] at h
      rw [runN_succ_stop hs]; exact h

theorem runN_stop_le {step : C → Res C V} {n m : Nat} {c : C} {o : Outcome V}
    (h : runN step n c = .stop o) (hle : n ≤ m) : runN step m c = .stop o := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact runN_stop_add h k

theorem resRel_next_left {R : C → D → Prop} {x : C} {b : Res D V} (h : RRes R (.next x) b) :
    ∃ y, b = .next y ∧ R x y := by
  cases h with
  | next h => exact ⟨_, rfl, h⟩

theorem resRel_stop_left {R : C → D → Prop} {o : Outcome V} {b : Res D V}
    (h : RRes R (.stop o) b) : b = .stop o := by
  cases h with
  | stop _ => rfl

theorem resRel_stop_right {R : C → D → Prop} {o : Outcome V} {a : Res C V}
    (h : RRes R a (.stop o)) : a = .stop o := by
  cases h with
  | stop _ => rfl

/-- `n` steps of `s` are matched by at least `n` steps of `t`. -/
theorem rsim_runN {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V} (hsim : RSim R s t)
    (n : Nat) : ∀ x y, R x y → ∃ m, n ≤ m ∧ RRes R (runN s n x) (runN t m y) := by
  induction n with
  | zero => exact fun x y h => ⟨0, Nat.le_refl 0, .next h⟩
  | succ n ih =>
    intro x y hxy
    obtain ⟨k, hk, hrel⟩ := hsim x y hxy
    cases hs : s x with
    | next x' =>
      have hrel' : RRes R (.next x') (runN t k y) := hs ▸ hrel
      obtain ⟨y', hy', hxy'⟩ := resRel_next_left hrel'
      obtain ⟨m, hm, hrun⟩ := ih x' y' hxy'
      have hsn : runN s (n + 1) x = runN s n x' := runN_succ_next hs n
      have htn : runN t (k + m) y = runN t m y' := runN_add_next hy' m
      exact ⟨k + m, by omega, by rw [hsn, htn]; exact hrun⟩
    | stop o =>
      have hrel' : RRes R (.stop o) (runN t k y) := hs ▸ hrel
      have htk : runN t k y = .stop o := resRel_stop_left hrel'
      have hsn : runN s (n + 1) x = .stop o := runN_succ_stop hs n
      have htn : runN t (k + (n + 1)) y = .stop o := runN_stop_add htk _
      exact ⟨k + (n + 1), by omega, by rw [hsn, htn]; exact .stop o⟩

theorem runN_next_or_stop (step : C → Res C V) (n : Nat) (c : C) :
    (∃ c', runN step n c = .next c') ∨ ∃ o, runN step n c = .stop o := by
  cases runN step n c with
  | next c' => exact .inl ⟨c', rfl⟩
  | stop o => exact .inr ⟨o, rfl⟩

/-- A stopped run of `s` is a stopped run of `t`. -/
theorem rsim_stop {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V} (hsim : RSim R s t)
    {x : C} {y : D} (hxy : R x y) {n : Nat} {o : Outcome V} (h : runN s n x = .stop o) :
    ∃ m, runN t m y = .stop o := by
  obtain ⟨m, -, hm⟩ := rsim_runN hsim n x y hxy
  exact ⟨m, resRel_stop_left (h ▸ hm)⟩

/-- A run of `t` that stops at `m` makes the run of `s` stop at `m`, alike. -/
theorem rsim_stop_back {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V}
    (hsim : RSim R s t) {x : C} {y : D} (hxy : R x y) {m : Nat} {o : Outcome V}
    (h : runN t m y = .stop o) : runN s m x = .stop o := by
  obtain ⟨m', hle, hm'⟩ := rsim_runN hsim m x y hxy
  have ht : runN t m' y = .stop o := runN_stop_le h hle
  exact resRel_stop_right (ht ▸ hm')

/-- A diverging run of `s` makes `t` diverge. -/
theorem rsim_div {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V} (hsim : RSim R s t)
    {x : C} {y : D} (hxy : R x y) (hdiv : ∀ n, ∃ c', runN s n x = .next c') (n : Nat) :
    ∃ d', runN t n y = .next d' := by
  rcases runN_next_or_stop t n y with hnext | ⟨o, ho⟩
  · exact hnext
  · obtain ⟨c', hc'⟩ := hdiv n
    have hs : runN s n x = .stop o := rsim_stop_back hsim hxy ho
    rw [hs] at hc'; cases hc'

/-- A diverging run of `t` makes `s` diverge. -/
theorem rsim_div_back {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V}
    (hsim : RSim R s t) {x : C} {y : D} (hxy : R x y) (hdiv : ∀ n, ∃ d', runN t n y = .next d')
    (n : Nat) : ∃ c', runN s n x = .next c' := by
  rcases runN_next_or_stop s n x with hnext | ⟨o, ho⟩
  · exact hnext
  · obtain ⟨m, hm⟩ := rsim_stop hsim hxy ho
    obtain ⟨d', hd'⟩ := hdiv m
    rw [hm] at hd'; cases hd'

/-- **Equal behaviours under a relational stuttering simulation.** -/
theorem beh_eq_of_rsim {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V}
    (hsim : RSim R s t) {x : C} {y : D} (hxy : R x y) : beh s x = beh t y := by
  ext b
  constructor
  · rintro (⟨n, o, h, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨m, hm⟩ := rsim_stop hsim hxy h
      exact .inl ⟨m, o, hm, rfl⟩
    · exact .inr ⟨rfl, rsim_div hsim hxy hdiv⟩
  · rintro (⟨m, o, h, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact .inl ⟨m, o, rsim_stop_back hsim hxy h, rfl⟩
    · exact .inr ⟨rfl, rsim_div_back hsim hxy hdiv⟩

/-- A lock-step relation is a simulation with one step. -/
theorem rsim_of_lock {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V}
    (h : LockStep R s t) : RSim R s t := by
  intro x y hxy
  refine ⟨1, Nat.one_pos, ?_⟩
  have h1 : runN t 1 y = t y := by
    simp only [runN]
    cases t y <;> rfl
  rw [h1]
  exact h x y hxy

/-- A run that stops has exactly one behaviour. -/
theorem beh_of_stop {step : C → Res C V} {n : Nat} {c : C} {o : Outcome V}
    (h : runN step n c = .stop o) : beh step c = {o.toObs} := by
  ext b
  constructor
  · rintro (⟨m, o', hm, rfl⟩ | ⟨rfl, hdiv⟩)
    · have h1 : runN step (n + m) c = .stop o := runN_stop_add h m
      have h2 : runN step (n + m) c = .stop o' := by
        rw [Nat.add_comm]; exact runN_stop_add hm n
      have ho : o = o' := by rw [h1] at h2; cases h2; rfl
      rw [ho]; rfl
    · obtain ⟨c', hc'⟩ := hdiv n
      rw [h] at hc'; cases hc'
  · rintro rfl
    exact .inl ⟨n, o, h, rfl⟩

end Silmaril.Proofs.Wasm.FX.Asyncify.RelSim
