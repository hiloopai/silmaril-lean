module

public import Silmaril.Cerberus.Core.ArenaCall.Defs

/-! # Lifting successful procedure steps into a sole operand task

The step rule retains explicit boundary, unfinished-task and live-successor
conditions. Terminal source steps propagate out of an arena instead of becoming
halted tasks. Finished operands are collected separately.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.ArenaRun

open Dynamics Interleave ArenaLift

/-- The way an arena resumes a chosen operand. -/
noncomputable def wrapTask (labels : Labels) (done : List (Nat × (Val × List Access))) (i : Nat)
    (k : List Frame) (p : Control × List Frame) : Control × List Frame :=
  match p.1 with
  | .raise o => (.raise o, [])
  | .jumping s vs env => arenaJump labels s vs env k
  | _ => (.interleave done [(i, p.1, p.2)], k)

variable (file : Program) (labels : Labels)

theorem sole_choose (m : Mem.Concrete.State)
    (done : List (Nat × (Val × List Access))) (i : Nat)
    (c : Control) (fr k : List Frame) (cs : List (Control × List Frame))
    (hunf : Unfinished ⟨c, fr, m⟩)
    (hr : requestAux file labels m c fr false = .choose cs) :
    requestAux file labels m (.interleave done [(i, c, fr)]) k false =
      .choose (cs.map (wrapTask labels done i k)) := by
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, Bool.false_and, Bool.false_or, Bool.or_false,
    List.any_cons, List.any_nil, List.attach_cons, List.attach_nil,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil,
    List.filter_cons, List.filter_nil, beq_self_eq_true, bne_self_eq_false,
    Bool.and_not_self, Bool.false_eq_true, ite_false, ite_true,
    List.nil_append, List.find?_cons, List.find?_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  cases c
  case value v =>
    simp only [hunf v rfl, hr]
    rfl
  all_goals
    simp only [hr]
    rfl

theorem sole_scheduled (m : Mem.Concrete.State)
    (done : List (Nat × (Val × List Access))) (i : Nat)
    (c : Control) (fr k : List Frame) (cs : List (Control × List Frame))
    (hunf : Unfinished ⟨c, fr, m⟩)
    (hr : requestAux file labels m c fr false = .scheduled cs) :
    requestAux file labels m (.interleave done [(i, c, fr)]) k false =
      .scheduled (cs.map (wrapTask labels done i k)) := by
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, Bool.false_and, Bool.false_or, Bool.or_false,
    List.any_cons, List.any_nil, List.attach_cons, List.attach_nil,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil,
    List.filter_cons, List.filter_nil, beq_self_eq_true, bne_self_eq_false,
    Bool.and_not_self, Bool.false_eq_true, ite_false, ite_true,
    List.nil_append, List.find?_cons, List.find?_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  cases c
  case value v =>
    simp only [hunf v rfl, hr]
    rfl
  all_goals
    simp only [hr]
    rfl

/-- A plain chosen control stays inside its operand. -/
theorem wrapTask_plain (done : List (Nat × (Val × List Access))) (i : Nat)
    (k : List Frame) (p : Control × List Frame) (hp : Plain p.1) :
    wrapTask labels done i k p = (.interleave done [(i, p.1, p.2)], k) := by
  obtain ⟨c, fr⟩ := p
  cases c <;> simp_all [wrapTask, Plain]

/-- Embedding of a task state with the shared memory. -/
def embed (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame)
    (s : State) : State := ⟨.interleave done [(i, s.control, s.stack)], k, s.memory⟩

/-- The conditions under which a successful source step stays inside the task. -/
def StepOk (s t : State) : Prop :=
  hasBoundary s.stack = true ∧ Unfinished s ∧ Plain t.control ∧
    ∀ o, t.control ≠ .halt o

/-- One live procedure step is one or two arena steps. -/
theorem lift_step (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame)
    {s t : State} {a : Label} (h : Step file labels s a t) (ok : StepOk s t) :
    CoreReaches file labels (embed done i k s) (embed done i k t) := by
  obtain ⟨c, fr, m⟩ := s
  obtain ⟨hb, hunf, hp, live⟩ := ok
  cases h with
  | respond _ response =>
    rw [request_eq_aux file labels _ hb] at response
    generalize hr : requestAux file labels m c fr false = r at response
    have pending : Pending [] i := ⟨by simp, by simp⟩
    cases response with
    | memory =>
      simpa [embed] using reaches_of_local file labels
        (drive_step file labels pending (k := k) (wc := false) (done := done) hunf
          (.memory hr))
    | update =>
      simpa [embed] using reaches_of_local file labels
        (drive_step file labels pending (k := k) (wc := false) (done := done) hunf
          (.update hr))
    | next =>
      simpa [embed] using reaches_of_local file labels
        (drive_step file labels pending (k := k) (wc := false) (done := done) hunf
          (.next hr hp))
    | @choose c' k' choices member =>
      refine .single ⟨.tau, Step.respond (fun _ h => nomatch h) ?_⟩
      change Respond m (request file labels _) .tau _
      dsimp only [embed]
      rw [request_of_requestAux file labels
        (sole_choose file labels m done i c fr k _ hunf hr) (fun _ _ _ _ h => nomatch h)]
      apply Respond.choose
      rw [← wrapTask_plain labels done i k (c', k') hp]
      exact List.mem_map_of_mem member
    | @scheduled c' k' choices member =>
      refine .single ⟨.tau, Step.respond (fun _ h => nomatch h) ?_⟩
      change Respond m (request file labels _) .tau _
      dsimp only [embed]
      rw [request_of_requestAux file labels
        (sole_scheduled file labels m done i c fr k _ hunf hr) (fun _ _ _ _ h => nomatch h)]
      apply Respond.scheduled
      rw [← wrapTask_plain labels done i k (c', k') hp]
      exact List.mem_map_of_mem member
    | pull => exact (live _ rfl).elim
    | empty => exact (live _ rfl).elim
    | scheduledEmpty => exact (live _ rfl).elim
    | end_ => exact (live _ rfl).elim

/-- A successful trace with explicit step conditions lifts compositionally. -/
theorem lift_reaches (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame)
    {s t : State}
    (h : Relation.ReflTransGen
      (fun s t => (∃ a, Step file labels s a t) ∧ StepOk s t) s t) :
    CoreReaches file labels (embed done i k s) (embed done i k t) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih =>
    obtain ⟨⟨a, transition⟩, ok⟩ := step
    exact ih.trans (lift_step file labels done i k transition ok)

/-- Collect the result once the task has only access annotations left. -/
theorem collect (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame)
    (v : Val) (fr : List Frame) (m : Mem.Concrete.State) (xs : List Access)
    (hk : annotationsOnly fr = some xs) :
    CoreReaches file labels (embed done i k ⟨.value v, fr, m⟩)
      ⟨.interleave ((i, v, xs) :: done) [], k, m⟩ := by
  have pending : Pending [] i := ⟨by simp, by simp⟩
  apply reaches_of_local file labels
  exact .single (.choose (requestAux_finish file labels pending m done v fr xs k false hk)
    (plain_interleave _ _))

/-- A symbol-valued callee returns through its own boundary and is collected.
This supplies an inhabited successful trace for the lifting conditions. -/
theorem symbol_return (done : List (Nat × (Val × List Access))) (i : Nat)
    (k : List Frame) (sym : Sym) (env : Env) (v : Val) (ls : Labels)
    (m : Mem.Concrete.State) (lookup : env.lookup sym = some v) :
    CoreReaches file labels
      (embed done i k ⟨.pureExpr (.mk [] () (.sym sym)) env,
        [.procedureReturn ls], m⟩)
      ⟨.interleave ((i, v, []) :: done) [], k, m⟩ := by
  have first : Step file labels
      ⟨.pureExpr (.mk [] () (.sym sym)) env, [.procedureReturn ls], m⟩ .tau
      ⟨.value v, [.procedureReturn ls], m⟩ := by
    apply Step.respond
    · intro o h; cases h
    · have hr : request file labels
          ⟨.pureExpr (.mk [] () (.sym sym)) env, [.procedureReturn ls], m⟩ =
          .next (.value v) [.procedureReturn ls] := by
        simp [request, requestAux, awaitsScheduling, lookup]
      rw [hr]
      exact Respond.next
  have last : Step file labels ⟨.value v, [.procedureReturn ls], m⟩ .tau
      ⟨.value v, [], m⟩ := by
    apply Step.respond
    · intro o h; cases h
    · have hr : request file labels ⟨.value v, [.procedureReturn ls], m⟩ =
          .next (.value v) [] := by
        simp [request, requestAux, awaitsScheduling]
      rw [hr]
      exact Respond.next
  refine (lift_step file labels done i k first ?_).trans
    ((lift_step file labels done i k last ?_).trans
      (collect file labels done i k v [] m [] rfl))
  · simp [StepOk, hasBoundary, Unfinished, Plain]
  · simp [StepOk, hasBoundary, Unfinished, annotationsOnly, Plain]

/-- A guarded source run to a value finishes the sole operand task. -/
theorem lift_task (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame)
    {s : State} {v : Val} {fr : List Frame} {m : Mem.Concrete.State} {xs : List Access}
    (h : Relation.ReflTransGen
      (fun s t => (∃ a, Step file labels s a t) ∧ StepOk s t) s ⟨.value v, fr, m⟩)
    (hk : annotationsOnly fr = some xs) :
    CoreReaches file labels (embed done i k s)
      ⟨.interleave ((i, v, xs) :: done) [], k, m⟩ :=
  (lift_reaches file labels done i k h).trans (collect file labels done i k v fr m xs hk)

end Silmaril.Cerberus.Core.ArenaRun
