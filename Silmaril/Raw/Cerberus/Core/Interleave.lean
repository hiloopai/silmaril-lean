module

public import Silmaril.Cerberus.Core.Dynamics.Defs

/-! # Unsequenced expressions in the Core dynamics: last task first, reads never race

`Dynamics.requestAux` runs an unsequenced expression `unseq [e₀, …, eₙ]` as an arena
`interleave done tasks`. Each task is a control with its own frames; `requestAux` reduces a task
alone (its frames, not the arena's continuation) and lifts the result back into the arena. Among the
tasks that can move, the arena reduces the first in reverse source order, so when no task holds a
procedure call it always drives the **last** pending task. A task whose control is a value over frames
that are only annotations is finished: it moves to `done` with its accesses. When no task is left,
the arena compares the accesses of distinct tasks (`races`) and either ends in UB035 or returns the
tuple of the task values, sorted by index, under one `annotations` frame.

This file proves that schedule generically:

* `LocalStep`: one deterministic step that `requestAux` gives for a control over given frames (a
  continuation that neither raises nor jumps, a one-way choice, a memory action, an update), with the
  flag `requestAux` threads for unsequenced contexts holding a call. `TaskRuns`: a task's run to a
  value over annotation frames. Both are statements about `requestAux` alone, so they hold for a task
  inside any arena and continuation.
* `interleave_runs`: if each task runs (last first, memory threaded from the last task to the first)
  the arena reaches `interleave (results ++ done) []`; `interleave_end` finishes it when no two tasks
  race, and `noRace_of_reads` proves that read-only accesses never race (`races` needs a write).
* `unseq_runs`: an `unseq` whose tasks run and only read reaches the tuple of their values in index
  order, under the concatenation of their accesses.
* `reaches_of_local`: at the top level (flag `false`) local steps are transitions of the Core LTS
  (`Dynamics.Step`), so these runs are runs of the specification's source relation.
* First users: `pure_task` (an `Epure` task runs to the value of its operand, whatever its location
  annotations), `unseq_pure` (an `unseq` of pure tasks reaches the tuple of their values, no
  accesses) and `unseq_literals` / `unseq_literals_reaches` (the `unseq` of literals that Cerberus
  makes of `3-3`).
* `pure_bridge`: a run of the Core LTS from a pure state (pure control above pure frames) is a run
  of local steps, since every pure state has exactly one request, a pure continuation or an
  ending. So `pure_task_of_reaches` and `unseq_pure_reaches` take the evaluations that
  `Fold.eval_reaches` and `PureEval.Eval.sound` prove (for every continuation and memory) as they
  are, for arenas without calls (flag `false`).

Nothing executable uses these definitions: they are proof devices over the canonical dynamics.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.Interleave

open Silmaril.Cerberus.Core.Dynamics

variable (file : Program) (labels : Labels)

/-- A frame that cuts off the enclosing unsequenced context. -/
def isBound : Frame → Bool
  | .bound => true
  | _ => false

/-- The call flag `requestAux` passes to a task of `interleave done tasks` under the arena
continuation `k`: the enclosing flag below no bound, or a call in another pending task. -/
def taskFlag (wc : Bool) (k : List Frame) (pending : List (Nat × (Control × List Frame))) : Bool :=
  (wc && !k.any isBound) || pending.any fun t => controlHasCCall t.2.1 t.2.2

/-- A continuation the arena lifts as it is: it neither raises nor transfers to a label. -/
def Plain (c : Control) : Prop := (∀ o, c ≠ .raise o) ∧ ∀ s vs env, c ≠ .jumping s vs env

/-- One deterministic step of a control over its frames, read off `requestAux` with call flag
`wc`: the memory of the state is the memory of the step. -/
inductive LocalStep (wc : Bool) : State → State → Prop where
  | next {c c' : Control} {k k' : List Frame} {m : Mem.Concrete.State} :
      requestAux file labels m c k wc = .next c' k' → Plain c' → LocalStep wc ⟨c, k, m⟩ ⟨c', k', m⟩
  | choose {c c' : Control} {k k' : List Frame} {m : Mem.Concrete.State} :
      requestAux file labels m c k wc = .choose [(c', k')] → Plain c' →
      LocalStep wc ⟨c, k, m⟩ ⟨c', k', m⟩
  | memory {c c' : Control} {k k' : List Frame} {m m' : Mem.Concrete.State} {name : String} :
      requestAux file labels m c k wc = .memory name m' c' k' → LocalStep wc ⟨c, k, m⟩ ⟨c', k', m'⟩
  | update {c c' : Control} {k k' : List Frame} {m m' : Mem.Concrete.State} :
      requestAux file labels m c k wc = .update m' c' k' → LocalStep wc ⟨c, k, m⟩ ⟨c', k', m'⟩

/-- Runs of local steps. -/
abbrev LocalReaches (wc : Bool) := Relation.ReflTransGen (LocalStep file labels wc)

/-- A task's run: from `s` to the value `v` over frames that are only the annotations `xs`,
ending in memory `m'`. -/
def TaskRuns (wc : Bool) (s : State) (v : Val) (xs : List Access) (m' : Mem.Concrete.State) :
    Prop :=
  ∃ k', LocalReaches file labels wc s ⟨.value v, k', m'⟩ ∧ annotationsOnly k' = some xs

/-! ## Reductions of `requestAux` -/

theorem any_isBound (k : List Frame) (g : Frame → Bool) (h : ∀ f, g f = isBound f) :
    k.any g = k.any isBound := by
  rw [show g = isBound from funext h]

theorem requestAux_halt (m : Mem.Concrete.State) (o : Outcome) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.halt o) k wc = .end_ o := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_commitMemory (m m' : Mem.Concrete.State) (name : String) (c : Control)
    (k : List Frame) (wc : Bool) :
    requestAux file labels m (.commitMemory name m' c) k wc = .memory name m' c k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_commitUpdate (m m' : Mem.Concrete.State) (c : Control) (k : List Frame)
    (wc : Bool) : requestAux file labels m (.commitUpdate m' c) k wc = .update m' c k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-- A value over no frames ends the run. -/
theorem requestAux_value_nil (m : Mem.Concrete.State) (v : Val) (wc : Bool) :
    requestAux file labels m (.value v) [] wc = .end_ (.defined v) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-- A value over one annotation frame ends the run. -/
theorem requestAux_value_annotations (m : Mem.Concrete.State) (v : Val) (xs : List Access)
    (wc : Bool) : requestAux file labels m (.value v) [.annotations xs] wc = .end_ (.defined v) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, requestAux_value_nil]

/-- Two annotation frames merge. -/
theorem requestAux_value_merge (m : Mem.Concrete.State) (v : Val) (xs ys : List Access)
    (k : List Frame) (wc : Bool) :
    requestAux file labels m (.value v) (.annotations xs :: .annotations ys :: k) wc =
      .next (.value v) (.annotations (xs ++ ys) :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-! ## Finished tasks -/

/-- A task is finished when it is a value over annotation frames only. -/
def Unfinished (s : State) : Prop := ∀ v, s.control = .value v → annotationsOnly s.stack = none

theorem unfinished_or_finished (s : State) :
    Unfinished s ∨ ∃ v xs, s.control = .value v ∧ annotationsOnly s.stack = some xs := by
  by_cases h : ∃ v xs, s.control = .value v ∧ annotationsOnly s.stack = some xs
  · exact .inr h
  · refine .inl fun v hv => ?_
    cases hs : annotationsOnly s.stack with
    | none => rfl
    | some xs => exact absurd ⟨v, xs, hv, hs⟩ h

/-- No local step leaves a control whose request is an ending. -/
theorem LocalStep.not_end {wc : Bool} {c : Control} {k : List Frame} {m : Mem.Concrete.State}
    {t : State} {o : Outcome} (h : LocalStep file labels wc ⟨c, k, m⟩ t)
    (hr : requestAux file labels m c k wc = .end_ o) : False := by
  cases h with
  | next h' _ => rw [hr] at h'; cases h'
  | choose h' _ => rw [hr] at h'; cases h'
  | memory h' => rw [hr] at h'; cases h'
  | update h' => rw [hr] at h'; cases h'

/-- A local step from a deterministic continuation goes there. -/
theorem LocalStep.of_next {wc : Bool} {c c' : Control} {k k' : List Frame}
    {m : Mem.Concrete.State} {t : State} (h : LocalStep file labels wc ⟨c, k, m⟩ t)
    (hr : requestAux file labels m c k wc = .next c' k') : t = ⟨c', k', m⟩ := by
  cases h with
  | next h' _ => rw [hr] at h'; cases h'; rfl
  | choose h' _ => rw [hr] at h'; cases h'
  | memory h' => rw [hr] at h'; cases h'
  | update h' => rw [hr] at h'; cases h'

/-- The only step from a finished task merges annotation frames: the value, the accesses and the
memory stay. -/
theorem finished_step {wc : Bool} {v : Val} {k : List Frame} {m : Mem.Concrete.State}
    {xs : List Access} {t : State} (hk : annotationsOnly k = some xs)
    (h : LocalStep file labels wc ⟨.value v, k, m⟩ t) :
    t.control = .value v ∧ annotationsOnly t.stack = some xs ∧ t.memory = m := by
  rcases k with _ | ⟨f1, rest⟩
  · exact (h.not_end file labels (requestAux_value_nil file labels m v wc)).elim
  cases f1 with
  | annotations ys =>
    rcases rest with _ | ⟨f2, rest⟩
    · exact (h.not_end file labels (requestAux_value_annotations file labels m v ys wc)).elim
    cases f2 with
    | annotations zs =>
      rw [h.of_next file labels (requestAux_value_merge file labels m v ys zs rest wc)]
      refine ⟨rfl, ?_, rfl⟩
      simp only [annotationsOnly, Option.map_map] at hk ⊢
      simpa [Function.comp_def] using hk
    | _ => simp [annotationsOnly] at hk
  | _ => simp [annotationsOnly] at hk

theorem finished_reaches {wc : Bool} {v : Val} {k : List Frame} {m : Mem.Concrete.State}
    {xs : List Access} {t : State} (hk : annotationsOnly k = some xs)
    (h : LocalReaches file labels wc ⟨.value v, k, m⟩ t) :
    t.control = .value v ∧ annotationsOnly t.stack = some xs ∧ t.memory = m := by
  induction h with
  | refl => exact ⟨rfl, hk, rfl⟩
  | tail _ step ih =>
    obtain ⟨hc, hs, hm⟩ := ih
    rename_i b _ _
    obtain ⟨cb, kb, mb⟩ := b
    simp only at hc hs hm
    subst hc hm
    exact finished_step file labels hs step

/-! ## One arena step -/

/-- The first of the reversed attached list is the last element. -/
theorem find_last {α β : Type} (ts : List α) (x : α) (g : {y // y ∈ ts ++ [x]} → β)
    (p : β → Bool) (hx : p (g ⟨x, by simp⟩) = true) :
    List.find? p ((ts ++ [x]).attach.reverse.map g) = some (g ⟨x, by simp⟩) := by
  have : ∃ rest, (ts ++ [x]).attach.reverse = ⟨x, by simp⟩ :: rest := by
    refine ⟨(ts.attach.map fun y => ⟨y.1, by simp [y.2]⟩).reverse, ?_⟩
    rw [List.attach_append]; simp [List.reverse_append]
  obtain ⟨rest, h⟩ := this
  rw [h, List.map_cons, List.find?_cons, hx]

/-- The hypotheses on the pending tasks: fresh index, no active call. -/
structure Pending (ts : List (Nat × (Control × List Frame))) (i : Nat) : Prop where
  fresh : i ∉ ts.map (·.1)
  idle : ∀ t ∈ ts, activeCall t.2.1 t.2.2 = false

theorem Pending.filter {ts : List (Nat × (Control × List Frame))} {i : Nat} (h : Pending ts i)
    (c : Control) (fr : List Frame) : (ts ++ [(i, c, fr)]).filter (fun t => t.1 != i) = ts := by
  rw [List.filter_append]
  simp only [List.filter_cons, List.filter_nil, bne_self_eq_false, Bool.false_eq_true, ite_false,
    List.append_nil]
  rw [List.filter_eq_self]
  intro t ht
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact h.fresh (List.mem_map_of_mem ht)

theorem Pending.replace {ts : List (Nat × (Control × List Frame))} {i : Nat} (h : Pending ts i)
    (c c' : Control) (fr fr' : List Frame) :
    (ts ++ [(i, c, fr)]).map (fun t => if (t.1 == i) = true then (i, c', fr') else t) =
      ts ++ [(i, c', fr')] := by
  rw [List.map_append]
  simp only [List.map_cons, List.map_nil, beq_self_eq_true, ite_true]
  congr 1
  rw [List.map_congr_left (g := id), List.map_id]
  intro t ht
  have : (t.1 == i) = false := by
    rw [beq_eq_false_iff_ne]
    rintro rfl
    exact h.fresh (List.mem_map_of_mem ht)
  simp [this]

theorem Pending.cond {ts : List (Nat × (Control × List Frame))} {i : Nat} (h : Pending ts i)
    (c : Control) (fr : List Frame) :
    (((ts ++ [(i, c, fr)]).any fun t => activeCall t.2.1 t.2.2) && !activeCall c fr) = false := by
  cases hc : activeCall c fr
  · have : ((ts ++ [(i, c, fr)]).any fun t => activeCall t.2.1 t.2.2) = false := by
      rw [List.any_eq_false]
      intro t ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · simp [h.idle t ht]
      · simp [hc]
    simp [this]
  · simp

/-- The arena moves its finished last task to `done`. -/
theorem requestAux_finish {ts : List (Nat × (Control × List Frame))} {i : Nat} (hp : Pending ts i)
    (m : Mem.Concrete.State) (done : List (Nat × (Val × List Access))) (v : Val) (fr : List Frame)
    (xs : List Access) (k : List Frame) (wc : Bool) (hfr : annotationsOnly fr = some xs) :
    requestAux file labels m (.interleave done (ts ++ [(i, .value v, fr)])) k wc =
      .choose [(.interleave ((i, v, xs) :: done) ts, k)] := by
  obtain ⟨y, ys, hy⟩ : ∃ y ys, ts ++ [(i, Control.value v, fr)] = y :: ys :=
    List.exists_cons_of_ne_nil (by simp)
  rw [hy, requestAux.eq_def]
  simp only [awaitsScheduling, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false]
  rw [← hy, find_last]
  · rw [hp.cond (.value v) fr]; simp [hfr, hp.filter]
  · rw [hp.cond (.value v) fr]; simp [hfr]

/-- The arena drives its last task by that task's own continuation. -/
theorem requestAux_drive_next {ts : List (Nat × (Control × List Frame))} {i : Nat}
    (hp : Pending ts i) (m : Mem.Concrete.State) (done : List (Nat × (Val × List Access)))
    (c c' : Control) (fr fr' k : List Frame) (wc : Bool) (hunf : Unfinished ⟨c, fr, m⟩)
    (hr : requestAux file labels m c fr (taskFlag wc k ts) = .next c' fr') (hc' : Plain c') :
    requestAux file labels m (.interleave done (ts ++ [(i, c, fr)])) k wc =
      .choose [(.interleave done (ts ++ [(i, c', fr')]), k)] := by
  obtain ⟨hraise, hjump⟩ := hc'
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

theorem requestAux_drive_choose {ts : List (Nat × (Control × List Frame))} {i : Nat}
    (hp : Pending ts i) (m : Mem.Concrete.State) (done : List (Nat × (Val × List Access)))
    (c c' : Control) (fr fr' k : List Frame) (wc : Bool) (hunf : Unfinished ⟨c, fr, m⟩)
    (hr : requestAux file labels m c fr (taskFlag wc k ts) = .choose [(c', fr')]) (hc' : Plain c') :
    requestAux file labels m (.interleave done (ts ++ [(i, c, fr)])) k wc =
      .choose [(.interleave done (ts ++ [(i, c', fr')]), k)] := by
  obtain ⟨hraise, hjump⟩ := hc'
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

theorem requestAux_drive_memory {ts : List (Nat × (Control × List Frame))} {i : Nat}
    (hp : Pending ts i) (m m' : Mem.Concrete.State) (done : List (Nat × (Val × List Access)))
    (name : String) (c c' : Control) (fr fr' k : List Frame) (wc : Bool)
    (hunf : Unfinished ⟨c, fr, m⟩)
    (hr : requestAux file labels m c fr (taskFlag wc k ts) = .memory name m' c' fr') :
    requestAux file labels m (.interleave done (ts ++ [(i, c, fr)])) k wc =
      .choose [(.commitMemory name m' (.interleave done (ts ++ [(i, c', fr')])), k)] := by
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

theorem requestAux_drive_update {ts : List (Nat × (Control × List Frame))} {i : Nat}
    (hp : Pending ts i) (m m' : Mem.Concrete.State) (done : List (Nat × (Val × List Access)))
    (c c' : Control) (fr fr' k : List Frame) (wc : Bool) (hunf : Unfinished ⟨c, fr, m⟩)
    (hr : requestAux file labels m c fr (taskFlag wc k ts) = .update m' c' fr') :
    requestAux file labels m (.interleave done (ts ++ [(i, c, fr)])) k wc =
      .choose [(.commitUpdate m' (.interleave done (ts ++ [(i, c', fr')])), k)] := by
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

theorem plain_interleave (done : List (Nat × (Val × List Access)))
    (tasks : List (Nat × (Control × List Frame))) : Plain (.interleave done tasks) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem plain_commitMemory (name : String) (m : Mem.Concrete.State) (c : Control) :
    Plain (.commitMemory name m c) := ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem plain_commitUpdate (m : Mem.Concrete.State) (c : Control) :
    Plain (.commitUpdate m c) := ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-! ## The arena runs its tasks last first -/

/-- One local step of the last task is one or two local steps of the arena. -/
theorem drive_step {ts : List (Nat × (Control × List Frame))} {i : Nat} (hp : Pending ts i)
    {done : List (Nat × (Val × List Access))} {k : List Frame} {wc : Bool} {s t : State}
    (hunf : Unfinished s) (h : LocalStep file labels (taskFlag wc k ts) s t) :
    LocalReaches file labels wc ⟨.interleave done (ts ++ [(i, s.control, s.stack)]), k, s.memory⟩
      ⟨.interleave done (ts ++ [(i, t.control, t.stack)]), k, t.memory⟩ := by
  cases h with
  | next hr hc' =>
    exact .single (.choose (requestAux_drive_next file labels hp _ done _ _ _ _ k wc hunf hr hc')
      (plain_interleave _ _))
  | choose hr hc' =>
    exact .single (.choose (requestAux_drive_choose file labels hp _ done _ _ _ _ k wc hunf hr hc')
      (plain_interleave _ _))
  | memory hr =>
    exact .head (.choose (requestAux_drive_memory file labels hp _ _ done _ _ _ _ _ k wc hunf hr)
      (plain_commitMemory _ _ _))
      (.single (.memory (requestAux_commitMemory file labels _ _ _ _ k wc)))
  | update hr =>
    exact .head (.choose (requestAux_drive_update file labels hp _ _ done _ _ _ _ k wc hunf hr)
      (plain_commitUpdate _ _))
      (.single (.update (requestAux_commitUpdate file labels _ _ _ k wc)))

/-- The arena runs its last task to the end and moves it to `done`. -/
theorem drive_task {ts : List (Nat × (Control × List Frame))} {i : Nat} (hp : Pending ts i)
    {done : List (Nat × (Val × List Access))} {k : List Frame} {wc : Bool} {c : Control}
    {fr : List Frame} {m m' : Mem.Concrete.State} {v : Val} {xs : List Access}
    (h : TaskRuns file labels (taskFlag wc k ts) ⟨c, fr, m⟩ v xs m') :
    LocalReaches file labels wc ⟨.interleave done (ts ++ [(i, c, fr)]), k, m⟩
      ⟨.interleave ((i, v, xs) :: done) ts, k, m'⟩ := by
  obtain ⟨k', hrun, hk'⟩ := h
  -- Induct on the run from its first state, keeping the end fixed.
  suffices ∀ s, LocalReaches file labels (taskFlag wc k ts) s ⟨.value v, k', m'⟩ →
      LocalReaches file labels wc ⟨.interleave done (ts ++ [(i, s.control, s.stack)]), k, s.memory⟩
        ⟨.interleave ((i, v, xs) :: done) ts, k, m'⟩ from this _ hrun
  intro s hs
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exact .single (.choose (requestAux_finish file labels hp m' done v k' xs k wc hk')
      (plain_interleave _ _))
  | head step rest ih =>
    rename_i s s'
    rcases unfinished_or_finished s with hunf | ⟨v0, xs0, hc, hk0⟩
    · exact (drive_step file labels hp hunf step).trans ih
    · obtain ⟨cs, ks, ms⟩ := s
      simp only at hc hk0
      subst hc
      obtain ⟨hv, hxs, hm⟩ := finished_reaches file labels hk0 (.head step rest)
      simp only [Control.value.injEq] at hv hxs hm
      rw [hk', Option.some.injEq] at hxs
      subst hv hxs hm
      exact .single (.choose (requestAux_finish file labels hp _ done _ ks _ k wc hk0)
        (plain_interleave _ _))

/-- The tasks of an arena run last first: each under the flag of the tasks still pending before
it, the memory threaded from the last task to the first. `results` lists their values and accesses
in task order. -/
inductive TasksRun (wc : Bool) (k : List Frame) :
    List (Nat × (Control × List Frame)) → Mem.Concrete.State →
      List (Nat × (Val × List Access)) → Mem.Concrete.State → Prop where
  | nil {m : Mem.Concrete.State} : TasksRun wc k [] m [] m
  | snoc {ts : List (Nat × (Control × List Frame))} {i : Nat} {c : Control} {fr : List Frame}
      {m m' m'' : Mem.Concrete.State} {v : Val} {xs : List Access}
      {results : List (Nat × (Val × List Access))} :
      TaskRuns file labels (taskFlag wc k ts) ⟨c, fr, m⟩ v xs m' →
      TasksRun wc k ts m' results m'' →
      TasksRun wc k (ts ++ [(i, c, fr)]) m (results ++ [(i, v, xs)]) m''

theorem TasksRun.indices {wc : Bool} {k : List Frame} {tasks : List (Nat × (Control × List Frame))}
    {m m' : Mem.Concrete.State} {results : List (Nat × (Val × List Access))}
    (h : TasksRun file labels wc k tasks m results m') :
    results.map (·.1) = tasks.map (·.1) := by
  induction h with
  | nil => rfl
  | snoc _ _ ih => simp [ih]

/-- **The arena runs every task, last first**, when the task indices are distinct and no task
starts inside a procedure call. -/
theorem interleave_runs {wc : Bool} {k : List Frame} {tasks : List (Nat × (Control × List Frame))}
    {m m' : Mem.Concrete.State} {results : List (Nat × (Val × List Access))}
    (h : TasksRun file labels wc k tasks m results m') (fresh : (tasks.map (·.1)).Nodup)
    (idle : ∀ t ∈ tasks, activeCall t.2.1 t.2.2 = false) (done : List (Nat × (Val × List Access))) :
    LocalReaches file labels wc ⟨.interleave done tasks, k, m⟩
      ⟨.interleave (results ++ done) [], k, m'⟩ := by
  induction h generalizing done with
  | nil => exact .refl
  | @snoc ts i c fr m m' m'' v xs results run _ ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append, List.nodup_cons,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, List.mem_singleton,
      true_and] at fresh
    have hp : Pending ts i :=
      ⟨fun hi => fresh.2 i hi i rfl rfl, fun t ht => idle t (List.mem_append_left _ ht)⟩
    refine (drive_task file labels hp run).trans ?_
    simpa using ih fresh.1 (fun t ht => idle t (List.mem_append_left _ ht)) ((i, v, xs) :: done)

/-! ## The end of the arena: races -/

/-- No two accesses of distinct tasks race. -/
def NoRace (done : List (Nat × (Val × List Access))) : Prop :=
  ∀ x ∈ done, ∀ y ∈ done, x.1 ≠ y.1 → ∀ a ∈ x.2.2, ∀ b ∈ y.2.2, races a b = false

/-- **Reads never race**: `races` needs a write on one side. -/
theorem races_reads {a b : Access} (ha : a.write = false) (hb : b.write = false) :
    races a b = false := by
  simp [races, ha, hb]

theorem noRace_of_reads {done : List (Nat × (Val × List Access))}
    (reads : ∀ x ∈ done, ∀ a ∈ x.2.2, a.write = false) : NoRace done :=
  fun x hx y hy _ a ha b hb => races_reads (reads x hx a ha) (reads y hy b hb)

/-- Without a race, the finished arena returns the tuple of the task values in index order under
one frame of all the accesses. -/
theorem requestAux_end (m : Mem.Concrete.State) (done : List (Nat × (Val × List Access)))
    (k : List Frame) (wc : Bool) (norace : NoRace done)
    (sorted : done.Pairwise fun a b => a.1 ≤ b.1) :
    requestAux file labels m (.interleave done []) k wc =
      .next (.value (.tuple (done.map (·.2.1)))) (.annotations (done.flatMap (·.2.2)) :: k) := by
  have hrace : (done.any fun x => done.any fun y => x.1 != y.1 &&
      x.2.2.any fun a => y.2.2.any (races a)) = false := by
    simp only [List.any_eq_false, Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, not_and,
      not_exists]
    intro x hx y hy hne a ha b hb hab
    rw [norace x hx y hy hne a ha b hb] at hab
    cases hab
  have hsort : (done.mergeSort fun a b => decide (a.1 ≤ b.1)) = done :=
    List.mergeSort_of_pairwise (by simpa using sorted)
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false, hrace,
    hsort]

/-! ## Unsequenced expressions -/

/-- The arena of `unseq es` in environment `env`, as `requestAux` starts it. -/
def unseqTasks (es : List EE) (env : Env) : List (Nat × (Control × List Frame)) :=
  es.zipIdx.map fun p => (p.2, .effectExpr p.1 env, [])

theorem map_unseqTasks (es : List EE) (env : Env)
    (g : EE × Nat → Nat × (Control × List Frame))
    (h : ∀ p, g p = (p.2, .effectExpr p.1 env, [])) : es.zipIdx.map g = unseqTasks es env := by
  rw [show g = _ from funext h]; rfl

theorem requestAux_unseq (m : Mem.Concrete.State) (annots : List Annot) (es : List EE) (env : Env)
    (k : List Frame) (wc : Bool) :
    requestAux file labels m (.effectExpr (.mk annots (.unseq es)) env) k wc =
      .next (.interleave [] (unseqTasks es env)) k := by
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, Bool.not_false, ite_true, beq_self_eq_true]
  rw [map_unseqTasks es env _ (by intro p; rfl)]
  rfl

theorem unseqTasks_indices (es : List EE) (env : Env) :
    (unseqTasks es env).map (·.1) = List.range es.length := by
  rw [unseqTasks, List.map_map, List.range_eq_range']
  exact List.zipIdx_map_snd 0 es

theorem activeCall_effectExpr (e : EE) (env : Env) : activeCall (.effectExpr e env) [] = false := by
  rw [activeCall.eq_def]; simp

/-- **An unsequenced expression whose tasks run and only read** reaches the tuple of the task values
in index order, under one frame of their accesses. -/
theorem unseq_runs {wc : Bool} {k : List Frame} {annots : List Annot} {es : List EE} {env : Env}
    {m m' : Mem.Concrete.State} {results : List (Nat × (Val × List Access))}
    (h : TasksRun file labels wc k (unseqTasks es env) m results m')
    (reads : ∀ x ∈ results, ∀ a ∈ x.2.2, a.write = false) :
    LocalReaches file labels wc ⟨.effectExpr (.mk annots (.unseq es)) env, k, m⟩
      ⟨.value (.tuple (results.map (·.2.1))), .annotations (results.flatMap (·.2.2)) :: k, m'⟩ := by
  have hidx : results.map (·.1) = List.range es.length := by
    rw [h.indices, unseqTasks_indices]
  refine .head (.next (requestAux_unseq file labels m annots es env k wc) (plain_interleave _ _)) ?_
  refine (interleave_runs file labels h ?_ ?_ []).tail ?_
  · rw [unseqTasks_indices]; exact List.nodup_range
  · intro t ht
    simp only [unseqTasks, List.mem_map] at ht
    obtain ⟨p, _, rfl⟩ := ht
    exact activeCall_effectExpr p.1 env
  · rw [List.append_nil]
    refine .next (requestAux_end file labels m' results k wc (noRace_of_reads reads) ?_) ⟨?_, ?_⟩
    · have := List.pairwise_lt_range (n := es.length)
      rw [← hidx, List.pairwise_map] at this
      exact this.imp Nat.le_of_lt
    · intro o h; cases h
    · intro _ _ _ h; cases h

/-! ## Local steps are steps of the Core LTS -/

theorem request_of_requestAux {c : Control} {k : List Frame} {m : Mem.Concrete.State} {r : Request}
    (hr : requestAux file labels m c k = r) (hj : ∀ s vs env k', r ≠ .next (.jumping s vs env) k') :
    request file labels ⟨c, k, m⟩ = r := by
  -- The label-transfer arm of `request` is excluded by `hj`.
  unfold request
  simp only [hr]

theorem live_of_requestAux {c : Control} {k : List Frame} {m : Mem.Concrete.State} {r : Request}
    (hr : requestAux file labels m c k = r) (hend : ∀ o, r ≠ .end_ o) : ∀ o, c ≠ .halt o := by
  rintro o rfl
  rw [requestAux_halt] at hr
  exact hend o hr.symm

/-- At the top level (call flag `false`) a local step is a transition of the Core LTS. -/
theorem LocalStep.step {s t : State} (h : LocalStep file labels false s t) :
    ∃ l, (lts file labels).Tr s l t := by
  cases h with
  | next hr hc =>
    refine ⟨.tau, Step.respond (live_of_requestAux file labels hr (fun _ h => nomatch h)) ?_⟩
    rw [request_of_requestAux file labels hr (fun s vs env k' h => hc.2 s vs env (by cases h; rfl))]
    exact Respond.next
  | choose hr _ =>
    refine ⟨.tau, Step.respond (live_of_requestAux file labels hr (fun _ h => nomatch h)) ?_⟩
    rw [request_of_requestAux file labels hr (fun _ _ _ _ h => nomatch h)]
    exact Respond.choose (by simp)
  | @memory _ _ _ _ _ _ name hr =>
    refine ⟨.memory name, Step.respond (live_of_requestAux file labels hr (fun _ h => nomatch h)) ?_⟩
    rw [request_of_requestAux file labels hr (fun _ _ _ _ h => nomatch h)]
    exact Respond.memory
  | update hr =>
    refine ⟨.tau, Step.respond (live_of_requestAux file labels hr (fun _ h => nomatch h)) ?_⟩
    rw [request_of_requestAux file labels hr (fun _ _ _ _ h => nomatch h)]
    exact Respond.update

/-- **Top-level local runs are runs of the Core LTS** (the specification's `coreStep`). -/
theorem reaches_of_local {s t : State} (h : LocalReaches file labels false s t) :
    Relation.ReflTransGen (fun s t => ∃ l, (lts file labels).Tr s l t) s t :=
  h.lift id fun _ _ step => step.step

/-! ## Pure tasks -/

/-- A focused `pure` expression records its location, if it has one outside the library, then
evaluates its operand above a diagnostic frame. -/
theorem requestAux_pure (m : Mem.Concrete.State) (annots : List Annot) (p : PE) (env : Env)
    (wc : Bool) : ∃ l, requestAux file labels m (.effectExpr (.mk annots (.pure p)) env) [] wc =
      if ({m with currentLocation := l} : Mem.Concrete.State).currentLocation == m.currentLocation
      then .next (.pureExpr p env) [.diagnosticLocation m.currentLocation]
      else .next (.setLocation l (.pureExpr p env)) [.diagnosticLocation m.currentLocation] := by
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, Bool.false_eq_true, ite_false, Bool.not_true]
  split
  · split
    · exact ⟨m.currentLocation, by simp⟩
    · exact ⟨_, rfl⟩
  · exact ⟨m.currentLocation, by simp⟩

theorem requestAux_setLocation (m : Mem.Concrete.State) (l : Loc) (c : Control) (k : List Frame)
    (wc : Bool) : requestAux file labels m (.setLocation l c) k wc =
      .update {m with currentLocation := l} c k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_value_diagnostic (m : Mem.Concrete.State) (v : Val) (l : Loc)
    (k : List Frame) (wc : Bool) :
    requestAux file labels m (.value v) (.diagnosticLocation l :: k) wc = .next (.value v) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-- **An `Epure` task runs to the value of its expression**, reading and writing nothing; only the
current location of the memory may change. `eval` is the evaluation of the operand above the
task's diagnostic frame, from any current location. -/
theorem pure_task {wc : Bool} {annots : List Annot} {p : PE} {env : Env} {m : Mem.Concrete.State}
    {v : Val}
    (eval : ∀ l l' : Loc, LocalReaches file labels wc
      ⟨.pureExpr p env, [.diagnosticLocation l], {m with currentLocation := l'}⟩
      ⟨.value v, [.diagnosticLocation l], {m with currentLocation := l'}⟩) :
    ∃ l', TaskRuns file labels wc ⟨.effectExpr (.mk annots (.pure p)) env, [], m⟩ v []
      {m with currentLocation := l'} := by
  obtain ⟨l, hr⟩ := requestAux_pure file labels m annots p env wc
  have plain_pure : Plain (.pureExpr p env) := ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  have finish : ∀ l', LocalReaches file labels wc
      ⟨.pureExpr p env, [.diagnosticLocation m.currentLocation], {m with currentLocation := l'}⟩
      ⟨.value v, [], {m with currentLocation := l'}⟩ := fun l' =>
    (eval _ l').tail (.next (requestAux_value_diagnostic file labels _ v _ [] wc)
      ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩)
  by_cases hl : (({m with currentLocation := l} : Mem.Concrete.State).currentLocation ==
      m.currentLocation) = true
  · simp only [hl, ↓reduceIte] at hr
    exact ⟨m.currentLocation, [], .head (.next hr plain_pure) (finish m.currentLocation), rfl⟩
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hr
    refine ⟨l, [], .head (.next hr ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩)
      (.head (.update (requestAux_setLocation file labels m l _ _ wc)) (finish l)), rfl⟩

/-- A literal evaluates in one step over any frames. -/
theorem val_reaches {wc : Bool} (ann : List Annot) (w : Value Codec.wireModel) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels wc ⟨.pureExpr (.mk ann () (.val w)) env, k, m⟩
      ⟨.value (runtimeValue w), k, m⟩ := by
  refine .single (.next ?_ ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩)
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-- An `Epure` task of a literal (each operand of `3-3` in Cerberus's elaboration). -/
theorem literal_task {wc : Bool} (annots ann : List Annot) (w : Value Codec.wireModel) (env : Env)
    (m : Mem.Concrete.State) :
    ∃ l', TaskRuns file labels wc
      ⟨.effectExpr (.mk annots (.pure (.mk ann () (.val w)))) env, [], m⟩ (runtimeValue w) []
      {m with currentLocation := l'} :=
  pure_task file labels fun _ _ => val_reaches file labels ann w env _ _

/-! ## Unsequenced pure expressions -/

theorem unseqTasks_snoc (es : List EE) (e : EE) (env : Env) :
    unseqTasks (es ++ [e]) env = unseqTasks es env ++ [(es.length, .effectExpr e env, [])] := by
  simp [unseqTasks, List.zipIdx_append]

/-- The results of tasks with fixed values and no accesses. -/
def pureResults (val : EE → Val) (es : List EE) : List (Nat × (Val × List Access)) :=
  es.zipIdx.map fun p => (p.2, val p.1, [])

/-- Tasks with fixed values and no accesses run, when each runs under every flag `F` allows and
`F` allows the flag of every prefix. -/
theorem tasksRun_pure {wc : Bool} {k : List Frame} {env : Env} (F : Bool → Prop) (val : EE → Val)
    (es : List EE)
    (h : ∀ e ∈ es, ∀ (b : Bool), F b → ∀ (m : Mem.Concrete.State), ∃ m',
      TaskRuns file labels b ⟨.effectExpr e env, [], m⟩ (val e) [] m')
    (hF : ∀ es', es' <+: es → F (taskFlag wc k (unseqTasks es' env)))
    (m : Mem.Concrete.State) :
    ∃ m', TasksRun file labels wc k (unseqTasks es env) m (pureResults val es) m' := by
  induction es using List.reverseRecOn generalizing m with
  | nil => exact ⟨m, .nil⟩
  | append_singleton es e ih =>
    obtain ⟨m1, run⟩ := h e (by simp) (taskFlag wc k (unseqTasks es env))
      (hF es (List.prefix_append es [e])) m
    obtain ⟨m', rest⟩ := ih (fun e' he' => h e' (by simp [he']))
      (fun es' hes' => hF es' (hes'.trans (List.prefix_append es [e]))) m1
    refine ⟨m', ?_⟩
    rw [unseqTasks_snoc, show pureResults val (es ++ [e]) =
      pureResults val es ++ [(es.length, val e, [])] by simp [pureResults, List.zipIdx_append]]
    exact .snoc run rest

/-- **An unsequenced expression of pure tasks** reaches the tuple of their values in source order,
with no accesses: `unseq [e₀, …, eₙ]` evaluates every operand, last first, and never races. -/
theorem unseq_pure {wc : Bool} {k : List Frame} {annots : List Annot} {es : List EE} {env : Env}
    (val : EE → Val)
    (h : ∀ e ∈ es, ∀ (b : Bool) (m : Mem.Concrete.State), ∃ m',
      TaskRuns file labels b ⟨.effectExpr e env, [], m⟩ (val e) [] m')
    (m : Mem.Concrete.State) :
    ∃ m', LocalReaches file labels wc ⟨.effectExpr (.mk annots (.unseq es)) env, k, m⟩
      ⟨.value (.tuple (es.map val)), .annotations [] :: k, m'⟩ := by
  obtain ⟨m', run⟩ := tasksRun_pure file labels (wc := wc) (k := k) (fun _ => True) val es
    (fun e he b _ => h e he b) (fun _ _ => trivial) m
  refine ⟨m', ?_⟩
  have reads : ∀ x ∈ pureResults val es, ∀ a ∈ x.2.2, a.write = false := by
    intro x hx a ha
    simp only [pureResults, List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    cases ha
  have hv : (pureResults val es).map (·.2.1) = es.map val := by
    simp only [pureResults, List.map_map]
    rw [show ((·.2.1) ∘ fun p : EE × Nat => (p.2, val p.1, ([] : List Access))) = val ∘ Prod.fst
      from rfl, ← List.map_map, List.zipIdx_map_fst]
  have ha : (pureResults val es).flatMap (·.2.2) = [] := by simp [pureResults]
  simpa [hv, ha] using unseq_runs file labels (annots := annots) run reads

/-- An `Epure` literal. -/
def literal (annots ann : List Annot) (w : Value Codec.wireModel) : EE :=
  .mk annots (.pure (.mk ann () (.val w)))

/-- **`unseq` of literals** (the operands of `3-3` in Cerberus's elaboration of ctest 00002) reaches
the tuple of their runtime values, from any memory and continuation. -/
theorem unseq_literals {wc : Bool} {k : List Frame} (annots : List Annot)
    (lits : List (List Annot × List Annot × Value Codec.wireModel)) (env : Env)
    (m : Mem.Concrete.State) :
    ∃ m', LocalReaches file labels wc
      ⟨.effectExpr (.mk annots (.unseq (lits.map fun x => literal x.1 x.2.1 x.2.2))) env, k, m⟩
      ⟨.value (.tuple (lits.map fun x => runtimeValue x.2.2)), .annotations [] :: k, m'⟩ := by
  let val : EE → Val := fun e => match e with
    | .mk _ (.pure (.mk _ _ (.val w))) => runtimeValue w
    | _ => .unit
  obtain ⟨m', h⟩ := unseq_pure file labels (wc := wc) (k := k) (annots := annots)
    (es := lits.map fun x => literal x.1 x.2.1 x.2.2) (env := env) val (by
      intro e he b m
      simp only [List.mem_map] at he
      obtain ⟨x, _, rfl⟩ := he
      obtain ⟨l', run⟩ := literal_task file labels (wc := b) x.1 x.2.1 x.2.2 env m
      exact ⟨_, run⟩) m
  refine ⟨m', ?_⟩
  simpa [List.map_map, Function.comp_def, val, literal] using h

/-- At the top level, `unseq` of literals is a run of the Core LTS (the specification's
`coreStep`). -/
theorem unseq_literals_reaches {k : List Frame} (annots : List Annot)
    (lits : List (List Annot × List Annot × Value Codec.wireModel)) (env : Env)
    (m : Mem.Concrete.State) :
    ∃ m', Relation.ReflTransGen (fun s t => ∃ l, (lts file labels).Tr s l t)
      ⟨.effectExpr (.mk annots (.unseq (lits.map fun x => literal x.1 x.2.1 x.2.2))) env, k, m⟩
      ⟨.value (.tuple (lits.map fun x => runtimeValue x.2.2)), .annotations [] :: k, m'⟩ :=
  let ⟨m', h⟩ := unseq_literals file labels (wc := false) (k := k) annots lits env m
  ⟨m', reaches_of_local file labels h⟩

/-! ## Pure evaluations of the specification are task runs

`Fold.eval_reaches` and `PureEval.Eval.sound` prove that a pure expression reaches its value in the
Core LTS, for every continuation. A run of the LTS exists, but its steps are not recorded. Here a
pure state (a pure control above pure frames) has one request, a pure continuation or an ending,
so such a run is a run of local steps (flag `false`, no call in the arena), and an `Epure` task
whose operand evaluates runs. -/

def PurePrim : Prim → Bool
  | .ctor _ | .arrayShift _ | .memberShift _ _ | .structValue _ _ | .memberValue _ _ | .bin _
  | .conv _ | .catchInt _ _ | .wrapInt _ _ | .notBool | .functionInfo | .compatible | .call _
  | .isType _ => true
  | _ => false

def PureFrame : Frame → Bool
  | .arguments op _ _ _ => PurePrim op
  | .pureBind .. | .pureCase .. | .pureIf .. => true
  | _ => false

def PureControl : Control → Bool
  | .pureExpr .. | .value _ => true
  | .apply op _ => PurePrim op
  | _ => false

inductive PureAbove (base : List Frame) : List Frame → Prop where
  | base : PureAbove base base
  | cons {f : Frame} {k : List Frame} : PureFrame f = true → PureAbove base k → PureAbove base (f :: k)

def PureResult (base : List Frame) : Request → Prop
  | .next c' k' => PureControl c' = true ∧ PureAbove base k'
  | .end_ _ => True
  | _ => False

theorem pure_arguments {base k : List Frame} (hk : PureAbove base k) (op : Prim) (hop : PurePrim op = true)
    (ps : List PE) (env : Env) : PureResult base (arguments op ps env k) := by
  cases ps with
  | nil => exact ⟨by simp [PureControl, hop], hk⟩
  | cons p ps => exact ⟨rfl, .cons (by simp [PureFrame, hop]) hk⟩

theorem pure_expr {base k : List Frame} (hk : PureAbove base k) (m : Mem.Concrete.State) (p : PE) (env : Env) (wc : Bool) :
    PureResult base (requestAux file labels m (.pureExpr p env) k wc) := by
  obtain ⟨ann, u, pe⟩ := p
  rw [requestAux.eq_def]
  cases pe
  all_goals simp only [awaitsScheduling, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  all_goals first
    | exact pure_arguments hk _ rfl _ _
    | exact ⟨rfl, hk⟩
    | trivial
    | (exact ⟨rfl, .cons rfl hk⟩)
    | (split <;> first | exact ⟨rfl, hk⟩ | trivial)

theorem pure_value {base k : List Frame} (hk : PureAbove base k) (hne : k ≠ base) (m : Mem.Concrete.State) (v : Val) (wc : Bool) :
    PureResult base (requestAux file labels m (.value v) k wc) := by
  cases hk with
  | base => exact absurd rfl hne
  | @cons f k hf hk =>
    rw [requestAux.eq_def]
    cases f
    all_goals simp only [PureFrame, Bool.false_eq_true] at hf
    all_goals simp only [awaitsScheduling, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
    all_goals (split <;> first
      | exact ⟨rfl, hk⟩
      | trivial
      | exact ⟨rfl, .cons (by simp [PureFrame, hf]) hk⟩)

theorem pure_apply {base k : List Frame} (hk : PureAbove base k) (m : Mem.Concrete.State) (op : Prim)
    (hop : PurePrim op = true) (vs : List Val) (wc : Bool) :
    PureResult base (requestAux file labels m (.apply op vs) k wc) := by
  rw [requestAux.eq_def]
  cases op
  all_goals try (simp [PurePrim] at hop; done)
  all_goals simp only [awaitsScheduling, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  all_goals (repeat' split) <;> first | trivial | simp_all



theorem pure_result {c : Control} {base k : List Frame} (hc : PureControl c = true)
    (hk : PureAbove base k) (hne : ∀ v, c = .value v → k ≠ base) (m : Mem.Concrete.State)
    (wc : Bool) : PureResult base (requestAux file labels m c k wc) := by
  cases c
  all_goals try (simp [PureControl] at hc; done)
  case pureExpr p env => exact pure_expr file labels hk m p env wc
  case value v => exact pure_value file labels hk (hne v rfl) m v wc
  case apply op vs => exact pure_apply file labels hk m op (by simpa [PureControl] using hc) vs wc

/-- A transition of the Core LTS from a state whose request is a continuation goes there. -/
theorem lts_of_next {c c' : Control} {k k' : List Frame} {m : Mem.Concrete.State} {a : Label}
    {t : State} (hr : requestAux file labels m c k = .next c' k')
    (hc' : ∀ s vs env, c' ≠ .jumping s vs env) (h : (lts file labels).Tr ⟨c, k, m⟩ a t) :
    t = ⟨c', k', m⟩ := by
  obtain ⟨_, hresp⟩ := h
  rw [request_of_requestAux file labels hr (fun s vs env _ h => hc' s vs env (by cases h; rfl))]
    at hresp
  cases hresp; rfl

/-- A transition of the Core LTS from a state whose request is an ending halts. -/
theorem lts_of_end {c : Control} {k : List Frame} {m : Mem.Concrete.State} {o : Outcome}
    {a : Label} {t : State} (hr : requestAux file labels m c k = .end_ o)
    (h : (lts file labels).Tr ⟨c, k, m⟩ a t) : t = ⟨.halt o, [], m⟩ := by
  obtain ⟨_, hresp⟩ := h
  rw [request_of_requestAux file labels hr (fun _ _ _ _ h => nomatch h)] at hresp
  cases hresp; rfl

abbrev CoreReaches := Relation.ReflTransGen (fun s t => ∃ l, (lts file labels).Tr s l t)

theorem halt_reaches {o : Outcome} {k : List Frame} {m : Mem.Concrete.State} {t : State}
    (h : CoreReaches file labels ⟨.halt o, k, m⟩ t) : t = ⟨.halt o, k, m⟩ := by
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ =>
    obtain ⟨_, ⟨live, _⟩⟩ := step
    exact absurd rfl (live o)

/-- From a value above its diagnostic frame, the Core LTS only drops the frame and halts. -/
theorem diagnostic_reaches {v : Val} {l : Loc} {m : Mem.Concrete.State} {t : State}
    (h : CoreReaches file labels ⟨.value v, [.diagnosticLocation l], m⟩ t) :
    t = ⟨.value v, [.diagnosticLocation l], m⟩ ∨ t.stack = [] := by
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inl rfl
  | head step rest =>
    rw [lts_of_next file labels (requestAux_value_diagnostic file labels m v l [] false)
      (fun _ _ _ h => nomatch h) step.choose_spec] at rest
    cases rest using Relation.ReflTransGen.head_induction_on with
    | refl => exact .inr rfl
    | head step' rest' =>
      rw [lts_of_end file labels (requestAux_value_nil file labels m v false) step'.choose_spec]
        at rest'
      rw [halt_reaches file labels rest']
      exact .inr rfl

/-- **A run of the Core LTS from a pure state to a value above the diagnostic frame is a run of
local steps.** -/
theorem pure_bridge {c : Control} {k : List Frame} {l : Loc} {m m' : Mem.Concrete.State} {v : Val}
    (hc : PureControl c = true) (hk : PureAbove [.diagnosticLocation l] k)
    (h : CoreReaches file labels ⟨c, k, m⟩ ⟨.value v, [.diagnosticLocation l], m'⟩) :
    LocalReaches file labels false ⟨c, k, m⟩ ⟨.value v, [.diagnosticLocation l], m'⟩ := by
  suffices ∀ s, CoreReaches file labels s ⟨.value v, [.diagnosticLocation l], m'⟩ →
      PureControl s.control = true → PureAbove [.diagnosticLocation l] s.stack →
      LocalReaches file labels false s ⟨.value v, [.diagnosticLocation l], m'⟩ from
    this _ h hc hk
  intro s hs
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => intro _ _; exact .refl
  | head step rest ih =>
    rename_i s s'
    intro hc hk
    obtain ⟨cs, ks, ms⟩ := s
    simp only at hc hk
    by_cases hend : ∃ v0, cs = .value v0 ∧ ks = [.diagnosticLocation l]
    · obtain ⟨v0, rfl, rfl⟩ := hend
      rcases diagnostic_reaches file labels (.head step rest) with heq | hnil
      · rw [heq]
      · cases hnil
    · have hne : ∀ v0, cs = .value v0 → ks ≠ [.diagnosticLocation l] :=
        fun v0 hv hks => hend ⟨v0, hv, hks⟩
      have hres := pure_result file labels hc hk hne ms false
      revert hres
      cases hr : requestAux file labels ms cs ks false <;> simp only [PureResult,
        IsEmpty.forall_iff]
      case next c' k' =>
        rintro ⟨hc', hk'⟩
        have hj : ∀ s vs env, c' ≠ .jumping s vs env := by
          rintro s vs env rfl; simp [PureControl] at hc'
        have hs' := lts_of_next file labels hr hj step.choose_spec
        subst hs'
        exact .head (.next hr ⟨fun o h => by subst h; simp [PureControl] at hc', hj⟩)
          (ih hc' hk')
      case end_ o =>
        intro _
        have hs' := lts_of_end file labels hr step.choose_spec
        subst hs'
        have := halt_reaches file labels rest
        cases this

/-- **An `Epure` task whose operand reaches its value in the Core LTS** (as `Fold.eval_reaches`
and `PureEval.Eval.sound` prove, for every continuation and memory) runs under flag `false`. -/
theorem pure_task_of_reaches {annots : List Annot} {p : PE} {env : Env} {m : Mem.Concrete.State}
    {v : Val}
    (eval : ∀ k (m' : Mem.Concrete.State), CoreReaches file labels ⟨.pureExpr p env, k, m'⟩
      ⟨.value v, k, m'⟩) :
    ∃ l', TaskRuns file labels false ⟨.effectExpr (.mk annots (.pure p)) env, [], m⟩ v []
      {m with currentLocation := l'} :=
  pure_task file labels fun _ _ => pure_bridge file labels rfl .base (eval _ _)

theorem controlHasCCall_effectExpr (e : EE) (env : Env) :
    controlHasCCall (.effectExpr e env) [] = hasCCall e := by
  rw [controlHasCCall.eq_def]; simp

/-- Without a call in the enclosing context or in the tasks, every task of `unseq es` runs under
flag `false`. -/
theorem taskFlag_unseq {k : List Frame} {es es' : List EE} {env : Env}
    (calls : ∀ e ∈ es, hasCCall e = false) (hes' : es' <+: es) :
    taskFlag false k (unseqTasks es' env) = false := by
  simp only [taskFlag, Bool.false_and, Bool.false_or, List.any_eq_false, unseqTasks, List.mem_map]
  rintro t ⟨q, hq, rfl⟩
  simp only [controlHasCCall_effectExpr, Bool.not_eq_true]
  exact calls q.1 (hes'.subset (List.fst_mem_of_mem_zipIdx hq))

/-- **An unsequenced expression of `Epure` tasks whose operands reach their values** reaches, in
the Core LTS, the tuple of those values in source order. -/
theorem unseq_pure_reaches {k : List Frame} {annots : List Annot} {es : List EE} {env : Env}
    (val : EE → Val)
    (pure : ∀ e ∈ es, ∃ annots' p, e = .mk annots' (.pure p) ∧ ∀ k (m' : Mem.Concrete.State),
      CoreReaches file labels ⟨.pureExpr p env, k, m'⟩ ⟨.value (val e), k, m'⟩)
    (m : Mem.Concrete.State) :
    ∃ m', CoreReaches file labels ⟨.effectExpr (.mk annots (.unseq es)) env, k, m⟩
      ⟨.value (.tuple (es.map val)), .annotations [] :: k, m'⟩ := by
  have calls : ∀ e ∈ es, hasCCall e = false := by
    intro e he
    obtain ⟨annots', p, rfl, _⟩ := pure e he
    rw [hasCCall.eq_def]
  obtain ⟨m', run⟩ := tasksRun_pure file labels (wc := false) (k := k) (· = false) val es
    (fun e he b hb m => by
      subst hb
      obtain ⟨annots', p, rfl, eval⟩ := pure e he
      obtain ⟨l', run⟩ := pure_task_of_reaches file labels (annots := annots') (m := m) eval
      exact ⟨_, run⟩)
    (fun es' hes' => taskFlag_unseq calls hes') m
  refine ⟨m', reaches_of_local file labels ?_⟩
  have reads : ∀ x ∈ pureResults val es, ∀ a ∈ x.2.2, a.write = false := by
    intro x hx a ha
    simp only [pureResults, List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    cases ha
  have hv : (pureResults val es).map (·.2.1) = es.map val := by
    simp only [pureResults, List.map_map]
    rw [show ((·.2.1) ∘ fun p : EE × Nat => (p.2, val p.1, ([] : List Access))) = val ∘ Prod.fst
      from rfl, ← List.map_map, List.zipIdx_map_fst]
  have ha : (pureResults val es).flatMap (·.2.2) = [] := by simp [pureResults]
  simpa [hv, ha] using unseq_runs file labels (annots := annots) run reads

end Silmaril.Cerberus.Core.Interleave
