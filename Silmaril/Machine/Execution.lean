module

/-! # Finite execution and simulation of partial deterministic machines

The caller supplies a fetched step, including its fault behavior. `none` denotes
failure; a successful finite run says nothing about other inputs or divergence.
This layer does not depend on an ISA, register representation, or memory model.
-/

@[expose] public section

namespace Silmaril.Machine.Execution

universe u v
variable {State : Type u} {Target : Type v}

/-- Execute exactly `n` transitions, stopping at the first failed transition. -/
def run (step : State → Option State) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (step s).bind (run step n)

@[simp] theorem run_zero (step : State → Option State) (s : State) :
    run step 0 s = some s := rfl

@[simp] theorem run_succ (step : State → Option State) (n : Nat) (s : State) :
    run step (n + 1) s = (step s).bind (run step n) := rfl

/-- Fuel addition is sequential composition, including failures. -/
theorem run_add (step : State → Option State) (n m : Nat) (s : State) :
    run step (n + m) s = (run step n s).bind (run step m) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    simp only [Nat.succ_add, run_succ]
    cases h : step s with
    | none => rfl
    | some t => exact ih t

/-- Every prestate of a successful execution prefix meets a local obligation.
The final state after `n` transitions is deliberately outside this certificate. -/
def SafePrefixes (step : State → Option State) (check : State → Prop)
    (n : Nat) (s : State) : Prop :=
  ∀ k, k < n → ∀ mid, run step k s = some mid → check mid

theorem SafePrefixes.zero (step : State → Option State) (check : State → Prop) (s : State) :
    SafePrefixes step check 0 s := by
  intro k hk
  exact False.elim (Nat.not_lt_zero k hk)

theorem SafePrefixes.cons {step : State → Option State} {check : State → Prop}
    {n : Nat} {s t : State} (head : check s) (transition : step s = some t)
    (tail : SafePrefixes step check n t) : SafePrefixes step check (n + 1) s := by
  intro k hk mid executed
  cases k with
  | zero => cases Option.some.inj executed; exact head
  | succ k =>
    rw [run_succ, transition] at executed
    exact tail k (Nat.lt_of_succ_lt_succ hk) mid executed

theorem SafePrefixes.append {step : State → Option State} {check : State → Prop}
    {n m : Nat} {s t : State} (first : SafePrefixes step check n s)
    (executed : run step n s = some t) (second : SafePrefixes step check m t) :
    SafePrefixes step check (n + m) s := by
  intro k hk mid partialRun
  by_cases hkn : k < n
  · exact first k hkn mid partialRun
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    have heq : k = n + (k - n) := (Nat.add_sub_of_le hnk).symm
    rw [heq, run_add, executed] at partialRun
    exact second (k - n) (by omega) mid partialRun

/-- A certificate can discharge any weaker local obligation. -/
theorem SafePrefixes.imp {step : State → Option State} {check other : State → Prop}
    {n : Nat} {s : State} (safe : SafePrefixes step check n s)
    (implies : ∀ state, check state → other state) : SafePrefixes step other n s := by
  intro k hk mid executed
  exact implies mid (safe k hk mid executed)

/-- Reducing an execution budget only removes safety obligations. -/
theorem SafePrefixes.prefix {step : State → Option State} {check : State → Prop}
    {n m : Nat} {s : State} (safe : SafePrefixes step check n s) (bound : m ≤ n) :
    SafePrefixes step check m s := by
  intro k hk mid executed
  exact safe k (Nat.lt_of_lt_of_le hk bound) mid executed

/-- Per-step invariants hold after every successful finite execution. -/
theorem run_preserves (step : State → Option State) (invariant : State → Prop)
    (preserves : ∀ s t, invariant s → step s = some t → invariant t)
    (n : Nat) {s t : State} (initial : invariant s) (exec : run step n s = some t) :
    invariant t := by
  induction n generalizing s with
  | zero => cases Option.some.inj exec; exact initial
  | succ n ih =>
    simp only [run_succ] at exec
    cases h : step s with
    | none => simp [h] at exec
    | some mid =>
      simp only [h, Option.bind_some] at exec
      exact ih (preserves s mid initial h) exec

/-- A successful source transition is simulated by one successful target transition. -/
theorem run_simulates (step : State → Option State) (targetStep : Target → Option Target)
    (relation : State → Target → Prop)
    (simulate : ∀ s t s', relation s t → step s = some s' →
      ∃ t', targetStep t = some t' ∧ relation s' t')
    (n : Nat) {s s' : State} {t : Target}
    (related : relation s t) (exec : run step n s = some s') :
    ∃ t', run targetStep n t = some t' ∧ relation s' t' := by
  induction n generalizing s t with
  | zero => cases Option.some.inj exec; exact ⟨t, rfl, related⟩
  | succ n ih =>
    simp only [run_succ] at exec
    cases hs : step s with
    | none => simp [hs] at exec
    | some mid =>
      simp only [hs, Option.bind_some] at exec
      obtain ⟨tmid, ht, hr⟩ := simulate s t mid related hs
      obtain ⟨final, tail, result⟩ := ih hr exec
      exact ⟨final, by simp only [run_succ, ht, Option.bind_some, tail], result⟩

/-- Reachability retains a finite successful execution witness. -/
def Reaches (step : State → Option State) (s t : State) : Prop :=
  ∃ n, run step n s = some t

@[refl] theorem Reaches.refl (step : State → Option State) (s : State) : Reaches step s s :=
  ⟨0, rfl⟩

theorem Reaches.trans {step : State → Option State} {s t u : State}
    (first : Reaches step s t) (second : Reaches step t u) : Reaches step s u := by
  obtain ⟨n, hn⟩ := first
  obtain ⟨m, hm⟩ := second
  exact ⟨n + m, by rw [run_add, hn]; exact hm⟩

/-- Compilers may emit any finite target block for each source transition. -/
theorem reaches_simulates (step : State → Option State) (targetStep : Target → Option Target)
    (relation : State → Target → Prop)
    (simulate : ∀ s t s', relation s t → step s = some s' →
      ∃ t', Reaches targetStep t t' ∧ relation s' t')
    {s s' : State} {t : Target}
    (related : relation s t) (exec : Reaches step s s') :
    ∃ t', Reaches targetStep t t' ∧ relation s' t' := by
  obtain ⟨n, exec⟩ := exec
  induction n generalizing s t with
  | zero => cases Option.some.inj exec; exact ⟨t, .refl _ _, related⟩
  | succ n ih =>
    simp only [run_succ] at exec
    cases hs : step s with
    | none => simp [hs] at exec
    | some mid =>
      simp only [hs, Option.bind_some] at exec
      obtain ⟨tmid, ht, hr⟩ := simulate s t mid related hs
      obtain ⟨final, tail, result⟩ := ih hr exec
      exact ⟨final, ht.trans tail, result⟩

end Silmaril.Machine.Execution
