module

public import Silmaril.Cerberus.Core.Interleave.Defs

/-! # Failures inside `unseq` arenas

A task of an `unseq` arena (`Interleave`) that reaches an ending (undefined behaviour) does not
finish: the arena answers its request `end_ o` by raising `o`, `choose [(raise o, [])]`, and an
enclosing arena passes that raise on unchanged. `Fails wc s o`: local steps from `s` reach a
state, not a value, whose request is the ending `o` or that raise. `fail_task`: the last task of
an arena fails, so the arena fails (with every earlier pending task untouched); `fail_unseq`: the
tasks after it in source order run, then it fails, so `unseq` fails. At the top level a failure is
a run of the Core LTS to the halted outcome `o` (`fail_reaches`).

This is a proof device: nothing executable uses it.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.ArenaFail

open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave

variable (file : Program) (labels : Labels)

/-- A failing run: local steps to a non-value state whose request ends with `o`, directly or
raised by an arena. -/
def Fails (wc : Bool) (s : State) (o : Outcome) : Prop :=
  ∃ t : State, LocalReaches file labels wc s t ∧ (∀ v, t.control ≠ .value v) ∧
    (requestAux file labels t.memory t.control t.stack wc = .end_ o ∨
      requestAux file labels t.memory t.control t.stack wc = .choose [(.raise o, [])])

theorem Fails.pre {wc : Bool} {s s' : State} {o : Outcome} (h : LocalReaches file labels wc s s')
    (f : Fails file labels wc s' o) : Fails file labels wc s o := by
  obtain ⟨t, run, hv, hr⟩ := f
  exact ⟨t, h.trans run, hv, hr⟩

/-- The arena raises the ending of its last task. -/
theorem requestAux_drive_end {ts : List (Nat × (Control × List Frame))} {i : Nat}
    (hp : Pending ts i) (m : Mem.Concrete.State) (done : List (Nat × (Val × List Access)))
    (c : Control) (fr k : List Frame) (wc : Bool) (hunf : Unfinished ⟨c, fr, m⟩) {o : Outcome}
    (hr : requestAux file labels m c fr (taskFlag wc k ts) = .end_ o) :
    requestAux file labels m (.interleave done (ts ++ [(i, c, fr)])) k wc =
      .choose [(.raise o, [])] := by
  unfold taskFlag at hr
  obtain ⟨y, ys, hy⟩ : ∃ y ys, ts ++ [(i, c, fr)] = y :: ys := List.exists_cons_of_ne_nil (by simp)
  rw [hy, requestAux.eq_def]
  simp only [awaitsScheduling, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false]
  rw [← hy, find_last]
  all_goals
    rw [hp.cond c fr]
    simp only [Bool.false_eq_true, ite_false, hp.filter, hp.replace]
    rw [any_isBound k _ (by intro f; cases f <;> rfl)]
    cases c
    case value v => simp [hunf v rfl, hr]
    all_goals simp [hr]

/-- The arena passes on a raise of its last task. -/
theorem requestAux_drive_raise {ts : List (Nat × (Control × List Frame))} {i : Nat}
    (hp : Pending ts i) (m : Mem.Concrete.State) (done : List (Nat × (Val × List Access)))
    (c : Control) (fr k : List Frame) (wc : Bool) (hunf : Unfinished ⟨c, fr, m⟩) {o : Outcome}
    (hr : requestAux file labels m c fr (taskFlag wc k ts) = .choose [(.raise o, [])]) :
    requestAux file labels m (.interleave done (ts ++ [(i, c, fr)])) k wc =
      .choose [(.raise o, [])] := by
  unfold taskFlag at hr
  obtain ⟨y, ys, hy⟩ : ∃ y ys, ts ++ [(i, c, fr)] = y :: ys := List.exists_cons_of_ne_nil (by simp)
  rw [hy, requestAux.eq_def]
  simp only [awaitsScheduling, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false]
  rw [← hy, find_last]
  all_goals
    rw [hp.cond c fr]
    simp only [Bool.false_eq_true, ite_false, hp.filter, hp.replace]
    rw [any_isBound k _ (by intro f; cases f <;> rfl)]
    cases c
    case value v => simp [hunf v rfl, hr]
    all_goals simp [hr]

/-- A run of the last task that ends away from a value is a run of the arena. -/
theorem drive_run {ts : List (Nat × (Control × List Frame))} {i : Nat} (hp : Pending ts i)
    {done : List (Nat × (Val × List Access))} {k : List Frame} {wc : Bool} {s t : State}
    (h : LocalReaches file labels (taskFlag wc k ts) s t) (ht : ∀ v, t.control ≠ .value v) :
    LocalReaches file labels wc ⟨.interleave done (ts ++ [(i, s.control, s.stack)]), k, s.memory⟩
      ⟨.interleave done (ts ++ [(i, t.control, t.stack)]), k, t.memory⟩ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step rest ih =>
    rename_i s s'
    rcases unfinished_or_finished s with hunf | ⟨v0, xs0, hc, hk0⟩
    · exact (drive_step file labels hp hunf step).trans ih
    · obtain ⟨cs, ks, ms⟩ := s
      simp only at hc hk0
      subst hc
      exact absurd (finished_reaches file labels hk0 (.head step rest)).1 (ht v0)

/-- A state that is not a value is unfinished. -/
theorem unfinished_of_not_value {s : State} (h : ∀ v, s.control ≠ .value v) : Unfinished s :=
  fun v hv => absurd hv (h v)

/-- **The last task of an arena fails, so the arena fails.** -/
theorem fail_task {ts : List (Nat × (Control × List Frame))} {i : Nat} (hp : Pending ts i)
    {done : List (Nat × (Val × List Access))} {k : List Frame} {wc : Bool} {c : Control}
    {fr : List Frame} {m : Mem.Concrete.State} {o : Outcome}
    (h : Fails file labels (taskFlag wc k ts) ⟨c, fr, m⟩ o) :
    Fails file labels wc ⟨.interleave done (ts ++ [(i, c, fr)]), k, m⟩ o := by
  obtain ⟨t, run, hv, hr⟩ := h
  have hint : ∀ v, Control.interleave done (ts ++ [(i, t.control, t.stack)]) ≠ .value v :=
    fun _ h => by cases h
  refine ⟨⟨.interleave done (ts ++ [(i, t.control, t.stack)]), k, t.memory⟩,
    drive_run file labels hp (done := done) run hv, hint, Or.inr ?_⟩
  obtain ⟨ct, kt, mt⟩ := t
  rcases hr with hr | hr
  · exact requestAux_drive_end file labels hp mt done ct kt k wc
      (unfinished_of_not_value hv) hr
  · exact requestAux_drive_raise file labels hp mt done ct kt k wc
      (unfinished_of_not_value hv) hr

theorem unseqTasks_pair (e₁ e₂ : EE) (env : Env) :
    unseqTasks [e₁, e₂] env = [(0, .effectExpr e₁ env, [])] ++ [(1, .effectExpr e₂ env, [])] := rfl

/-- **`unseq [e₁, e₂]` fails** when `e₂` (run first) fails, or `e₂` runs and then `e₁` fails. -/
theorem fail_pair {wc : Bool} {k : List Frame} {annots : List Annot} {e₁ e₂ : EE} {env : Env}
    {m : Mem.Concrete.State} {o : Outcome}
    (h : Fails file labels (taskFlag wc k [(0, .effectExpr e₁ env, [])])
        ⟨.effectExpr e₂ env, [], m⟩ o ∨
      ∃ v xs m', TaskRuns file labels (taskFlag wc k [(0, .effectExpr e₁ env, [])])
          ⟨.effectExpr e₂ env, [], m⟩ v xs m' ∧
        Fails file labels (taskFlag wc k []) ⟨.effectExpr e₁ env, [], m'⟩ o) :
    Fails file labels wc ⟨.effectExpr (.mk annots (.unseq [e₁, e₂])) env, k, m⟩ o := by
  have start : LocalReaches file labels wc ⟨.effectExpr (.mk annots (.unseq [e₁, e₂])) env, k, m⟩
      ⟨.interleave [] ([(0, .effectExpr e₁ env, [])] ++ [(1, .effectExpr e₂ env, [])]), k, m⟩ :=
    .single (.next (requestAux_unseq file labels m annots [e₁, e₂] env k wc)
      (plain_interleave _ _))
  have hp1 : Pending [(0, .effectExpr e₁ env, [])] 1 :=
    ⟨by simp, by intro t ht; simp at ht; subst ht; exact activeCall_effectExpr e₁ env⟩
  have hp0 : Pending [] 0 := ⟨by simp, by simp⟩
  refine Fails.pre file labels start ?_
  rcases h with f | ⟨v, xs, m', run, f⟩
  · exact fail_task file labels hp1 f
  · refine Fails.pre file labels (drive_task file labels hp1 (done := []) run) ?_
    exact fail_task file labels hp0 (ts := []) f

theorem requestAux_raise (m : Mem.Concrete.State) (o : Outcome) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.raise o) k wc = .end_ o := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-- At the top level (flag `false`), a failure is a run of the Core LTS to the halted outcome. -/
theorem fail_reaches {s : State} {o : Outcome} (h : Fails file labels false s o) :
    ∃ t, CoreReaches file labels s t ∧ t.control = .halt o := by
  obtain ⟨⟨c, k, m⟩, run, -, hr⟩ := h
  have pre := reaches_of_local file labels run
  simp only at hr
  by_cases hc : ∃ o', c = .halt o'
  · obtain ⟨o', rfl⟩ := hc
    rw [requestAux_halt] at hr
    rcases hr with hr | hr <;> cases hr
    exact ⟨_, pre, rfl⟩
  have live : ∀ o', c ≠ .halt o' := fun o' h => hc ⟨o', h⟩
  rcases hr with hr | hr
  · refine ⟨⟨.halt o, [], m⟩, pre.tail ⟨.terminal o, Step.respond live ?_⟩, rfl⟩
    rw [show (⟨c, k, m⟩ : State).memory = m from rfl,
      request_of_requestAux file labels hr (fun _ _ _ _ h => nomatch h)]
    exact .end_
  · have s₁ : CoreReaches file labels ⟨c, k, m⟩ ⟨.raise o, [], m⟩ := by
      refine .single ⟨.tau, Step.respond live ?_⟩
      rw [show (⟨c, k, m⟩ : State).memory = m from rfl,
        request_of_requestAux file labels hr (fun _ _ _ _ h => nomatch h)]
      exact .choose (by simp)
    refine ⟨⟨.halt o, [], m⟩, (pre.trans s₁).tail ⟨.terminal o, Step.respond
      (fun _ h => nomatch h) ?_⟩, rfl⟩
    rw [show (⟨Control.raise o, [], m⟩ : State).memory = m from rfl,
      request_of_requestAux file labels (requestAux_raise file labels m o [] false)
        (fun _ _ _ _ h => nomatch h)]
    exact .end_

end Silmaril.Cerberus.Core.ArenaFail
