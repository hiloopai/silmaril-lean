module

public import Silmaril.Wasm.Component.Async.Defs

@[expose] public section

/-!
# Component Model async built-ins: theorems

PROVED (standard axioms), for the model of `Silmaril.Wasm.Component.Async`:

* **Waiting** (`wait_sound`, `wait_blocked`, `wait_live`): `waitable-set.wait` returns the
  pending event of a member of the set, removing it (a `Waits` step); it suspends only when no
  member has an event; and if some member below `next` has an event it does not suspend.
* **Streams are rendezvous channels** (`write_read`, `read_write`): a `stream.write` that finds
  no pending read becomes pending (`BLOCKED`); the next `stream.read` of `n ≥ |xs|` items
  delivers exactly `xs`, records them in the ghost `sent`, and posts the writer's
  `stream-write` event `COMPLETED |xs|`. Symmetrically a pending read of `n` items receives
  `xs.take n` through its `stream-read` event when a write arrives.
* **Dropped peers** (`write_dropped`): a write to a stream whose readable end is dropped
  reports `DROPPED` with count `0`.
* **Futures are written once** (`futureWrite_done`, `futureRead_done`): once a future's value
  is delivered, writing or reading it again traps.
* **`task.return` once** (`taskReturn_twice`), and task results are **write-once**
  (`step_result_stable`) and set only by `task.return` (`result_set_by`).
* **Sync lowering** (`syncRun_result`, `sync_from_start`, `sync_resumes`): in every
  interleaving with steps of other parties, the sync-lowered caller resumes exactly with the
  results the callee passed to `task.return`, and it can resume as soon as they are there.
* A worked run (`demo_events`): `stream.new`, a waitable set, a blocked write of two items
  joined to the set, a read by the peer, and `wait` returning the writer's
  `stream-write COMPLETED 2` event.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async

open Silmaril.Wasm.Component (Val)

/-! ## Waiting -/

theorem firstReady_spec {st : Store} {s : Nat} :
    ∀ {hs : List Nat} {h : Nat}, firstReady st s hs = some h →
      h ∈ hs ∧ st.joined h = some s ∧ (st.ev h).isSome
  | [], _, hh => by simp [firstReady] at hh
  | a :: hs, h, hh => by
    unfold firstReady at hh
    split_ifs at hh with ha
    · cases hh
      exact ⟨List.mem_cons_self, ha⟩
    · have ih := firstReady_spec hh
      exact ⟨List.mem_cons_of_mem _ ih.1, ih.2⟩

theorem firstReady_none {st : Store} {s : Nat} :
    ∀ {hs : List Nat}, firstReady st s hs = none →
      ∀ h ∈ hs, st.joined h = some s → st.ev h = none
  | [], _, h, hm, _ => absurd hm List.not_mem_nil
  | a :: hs, hn, h, hm, hj => by
    unfold firstReady at hn
    split_ifs at hn with ha
    · rcases List.mem_cons.1 hm with rfl | hm'
      · exact Option.not_isSome_iff_eq_none.1 fun hs' => ha ⟨hj, hs'⟩
      · exact firstReady_none hn h hm' hj

/-- **`wait` returns a member's event**, as a `Waits` step. -/
theorem wait_sound {st st' : Store} {s : Nat} {e : Event}
    (h : step st (.wait s) = some (st', .event e)) : ∃ w, Waits st s w e st' := by
  simp only [step] at h
  split_ifs at h with hs
  cases hf : firstReady st s (List.range st.next) with
    | none => rw [hf] at h; cases h
    | some w =>
      rw [hf] at h
      obtain ⟨-, hj, hev⟩ := firstReady_spec hf
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hev
      simp only [take, he', Option.map_some, Option.some.injEq, Prod.mk.injEq, Res.event.injEq] at h
      exact ⟨w, hs, hj, h.2 ▸ he', h.1.symm⟩

/-- **`wait` suspends only when no member has an event.** -/
theorem wait_blocked {st st' : Store} {s : Nat} (h : step st (.wait s) = some (st', .blocked)) :
    st' = st ∧ ∀ w < st.next, st.joined w = some s → st.ev w = none := by
  simp only [step] at h
  split_ifs at h with hs
  cases hf : firstReady st s (List.range st.next) with
    | none =>
      rw [hf] at h
      cases h
      exact ⟨rfl, fun w hw => firstReady_none hf w (List.mem_range.2 hw)⟩
    | some w =>
      rw [hf] at h
      obtain ⟨-, -, hev⟩ := firstReady_spec hf
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hev
      simp [take, he'] at h

/-- **`wait` does not suspend when a member below `next` has an event.** -/
theorem wait_live {st : Store} {s w : Nat} {e : Event} (hs : st.tbl s = some .wset)
    (hw : w < st.next) (hj : st.joined w = some s) (he : st.ev w = some e) :
    ∃ st' e', step st (.wait s) = some (st', .event e') := by
  cases hf : firstReady st s (List.range st.next) with
  | none =>
    have := firstReady_none hf w (List.mem_range.2 hw) hj
    rw [he] at this; cases this
  | some v =>
    obtain ⟨-, -, hev⟩ := firstReady_spec hf
    obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hev
    exact ⟨{ st with ev := upd st.ev v none }, e', by simp [step, hs, hf, take, he']⟩

/-! ## Streams -/

/-- **A write with no pending read blocks; the next read of enough items delivers exactly the
written items** and completes the writer through its `stream-write` event. -/
theorem write_read {st : Store} {r w s n : Nat} {xs : List Val}
    (hw : st.tbl w = some (.streamW s)) (hr : st.tbl r = some (.streamR s))
    (hp : (st.chans s).pend = .idle) (hd : (st.chans s).rDropped = false)
    (hn : xs.length ≤ n) :
    ∃ st₁ st₂, step st (.streamWrite w xs) = some (st₁, .nat blocked) ∧
      step st₁ (.streamRead r n) = some (st₂, .read (packCopy .completed xs.length) xs) ∧
      (st₂.chans s).sent = (st.chans s).sent ++ xs ∧
      st₂.ev w = some ⟨.streamWrite, w, packCopy .completed xs.length, []⟩ := by
  have hk : min n xs.length = xs.length := Nat.min_eq_right hn
  simp [step, streamWrite, streamRead, hw, hr, hp, hd, Store.setChan, Store.post, upd, hk]

/-- **A pending read receives `xs.take n` through its event when a write arrives**, and the
writer completes at once with the same count. -/
theorem read_write {st : Store} {r w s n : Nat} {xs : List Val}
    (hw : st.tbl w = some (.streamW s)) (hr : st.tbl r = some (.streamR s))
    (hp : (st.chans s).pend = .idle) (hd : (st.chans s).wDropped = false) :
    ∃ st₁ st₂, step st (.streamRead r n) = some (st₁, .nat blocked) ∧
      step st₁ (.streamWrite w xs) = some (st₂, .nat (packCopy .completed (min n xs.length))) ∧
      (st₂.chans s).sent = (st.chans s).sent ++ xs.take n ∧
      st₂.ev r = some ⟨.streamRead, r, packCopy .completed (min n xs.length), xs.take n⟩ := by
  simp [step, streamWrite, streamRead, hw, hr, hp, hd, Store.setChan, Store.post, upd]

/-- **A write towards a dropped reader reports `DROPPED`.** -/
theorem write_dropped {st : Store} {w s : Nat} {xs : List Val}
    (hw : st.tbl w = some (.streamW s)) (hp : (st.chans s).pend = .idle)
    (hd : (st.chans s).rDropped = true) :
    step st (.streamWrite w xs) = some (st, .nat (packCopy .dropped 0)) := by
  simp [step, streamWrite, hw, hp, hd]

/-! ## Futures -/

/-- **A delivered future cannot be written again.** -/
theorem futureWrite_done {st : Store} {w s : Nat} {v : Val} (hw : st.tbl w = some (.futureW s))
    (hd : (st.chans s).done = true) : step st (.futureWrite w v) = none := by
  simp [step, futureWrite, hw, hd]

/-- **A delivered future cannot be read again.** -/
theorem futureRead_done {st : Store} {r s : Nat} (hr : st.tbl r = some (.futureR s))
    (hd : (st.chans s).done = true) : step st (.futureRead r) = none := by
  simp [step, futureRead, hr, hd]

/-- A future written while its reader waits delivers the value to the reader's event. -/
theorem future_read_write {st : Store} {r w s : Nat} {v : Val}
    (hw : st.tbl w = some (.futureW s)) (hr : st.tbl r = some (.futureR s))
    (hp : (st.chans s).pend = .idle) (hd : (st.chans s).done = false) :
    ∃ st₁ st₂, step st (.futureRead r) = some (st₁, .nat blocked) ∧
      step st₁ (.futureWrite w v) = some (st₂, .nat CopyResult.completed.toNat) ∧
      (st₂.chans s).done = true ∧
      st₂.ev r = some ⟨.futureRead, r, CopyResult.completed.toNat, [v]⟩ := by
  simp [step, futureWrite, futureRead, hw, hr, hp, hd, Store.setChan, Store.post, upd]

/-! ## Tasks -/

/-- **`task.return` traps the second time.** -/
theorem taskReturn_twice {st : Store} {t : Nat} {vs : List Val}
    (h : (st.tasks t).result.isSome) : step st (.taskReturn t vs) = none := by
  simp [step, h]

/-- `task.return` records its values. -/
theorem taskReturn_result {st st' : Store} {t : Nat} {vs : List Val} {r : Res}
    (h : step st (.taskReturn t vs) = some (st', r)) : (st'.tasks t).result = some vs := by
  simp only [step] at h
  by_cases h0 : (st.tasks t).result.isSome
  · simp [h0] at h
  · by_cases hs : st.tbl t = some (.subtask t)
    · simp only [h0, hs, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [Store.post, upd]
    · simp only [h0, hs, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [upd]

/-- A step keeps `next` and the tasks. -/
def Frame (st st' : Store) : Prop := st'.next = st.next ∧ st'.tasks = st.tasks

/-- A `some` result of a helper built from `setChan`, `post` and `remove` keeps the frame. -/
macro "frame_tac" h:ident : tactic => `(tactic| (
  repeat' ((try dsimp only at $h:ident); split at $h:ident)
  all_goals first
    | (cases $h:ident; first | done | exact ⟨rfl, rfl⟩)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident
       obtain ⟨rfl, -⟩ := $h:ident
       exact ⟨rfl, rfl⟩)))

theorem streamWrite_frame {st st' : Store} {w : Nat} {xs : List Val} {r : Res}
    (h : streamWrite st w xs = some (st', r)) : Frame st st' := by
  unfold streamWrite at h; frame_tac h

theorem streamRead_frame {st st' : Store} {r n : Nat} {res : Res}
    (h : streamRead st r n = some (st', res)) : Frame st st' := by
  unfold streamRead at h; frame_tac h

theorem streamDropR_frame {st st' : Store} {r : Nat} {res : Res}
    (h : streamDropR st r = some (st', res)) : Frame st st' := by
  unfold streamDropR at h; frame_tac h

theorem streamDropW_frame {st st' : Store} {r : Nat} {res : Res}
    (h : streamDropW st r = some (st', res)) : Frame st st' := by
  unfold streamDropW at h; frame_tac h

theorem futureWrite_frame {st st' : Store} {w : Nat} {v : Val} {r : Res}
    (h : futureWrite st w v = some (st', r)) : Frame st st' := by
  unfold futureWrite at h; frame_tac h

theorem futureRead_frame {st st' : Store} {r : Nat} {res : Res}
    (h : futureRead st r = some (st', res)) : Frame st st' := by
  unfold futureRead at h; frame_tac h

theorem futureDropR_frame {st st' : Store} {r : Nat} {res : Res}
    (h : futureDropR st r = some (st', res)) : Frame st st' := by
  unfold futureDropR at h; frame_tac h

theorem futureDropW_frame {st st' : Store} {r : Nat} {res : Res}
    (h : futureDropW st r = some (st', res)) : Frame st st' := by
  unfold futureDropW at h; frame_tac h

theorem join_frame {st st' : Store} {x s : Nat} {res : Res}
    (h : step st (.join x s) = some (st', res)) : Frame st st' := by
  simp only [step] at h; frame_tac h

theorem take_frame {st st' : Store} {x : Nat} {e : Event} (h : take st x = some (st', e)) :
    Frame st st' := by
  unfold take at h
  cases he : st.ev x <;> simp only [he, Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨rfl, rfl⟩

theorem ready_frame {st st' : Store} {s : Nat} {res : Res} {dflt : Res}
    (h : (match firstReady st s (List.range st.next) with
      | some x => (take st x).map fun (st', e) => (st', Res.event e)
      | none => some (st, dflt)) = some (st', res)) : Frame st st' := by
  cases hf : firstReady st s (List.range st.next) with
  | none =>
    simp only [hf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  | some x =>
    simp only [hf, Option.map_eq_some_iff] at h
    obtain ⟨⟨st'', e⟩, ht, hp⟩ := h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    exact take_frame ht

theorem wait_frame {st st' : Store} {s : Nat} {res : Res}
    (h : step st (.wait s) = some (st', res)) : Frame st st' := by
  simp only [step] at h
  split_ifs at h
  exact ready_frame h

theorem poll_frame {st st' : Store} {s : Nat} {res : Res}
    (h : step st (.poll s) = some (st', res)) : Frame st st' := by
  simp only [step] at h
  split_ifs at h
  exact ready_frame h

theorem new_next_tasks {st st' : Store} {op : Op} {r : Res} {t : Nat}
    (h : step st op = some (st', r)) (hop : op = .streamNew ∨ op = .futureNew) :
    st.next ≤ st'.next ∧ st'.tasks t = st.tasks t := by
  rcases hop with rfl | rfl <;>
    simp only [step, Store.alloc2, Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, -⟩ := h <;> exact ⟨Nat.le_add_right _ _, rfl⟩

theorem wsNew_next_tasks {st st' : Store} {r : Res} {t : Nat}
    (h : step st .wsNew = some (st', r)) : st.next ≤ st'.next ∧ st'.tasks t = st.tasks t := by
  simp only [step, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨Nat.le_succ _, rfl⟩

theorem callAsync_next_tasks {st st' : Store} {r : Res} {t : Nat}
    (h : step st .callAsync = some (st', r)) (ht : t < st.next) :
    st.next ≤ st'.next ∧ st'.tasks t = st.tasks t := by
  simp only [step, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨Nat.le_succ _, by simp [upd, Nat.ne_of_lt ht]⟩

theorem drop_next_tasks {st st' : Store} {op : Op} {r : Res} {t : Nat}
    (h : step st op = some (st', r)) (hop : (∃ s, op = .wsDrop s) ∨ ∃ s, op = .subtaskDrop s) :
    st.next ≤ st'.next ∧ st'.tasks t = st.tasks t := by
  rcases hop with ⟨s, rfl⟩ | ⟨s, rfl⟩ <;> simp only [step] at h <;> split_ifs at h <;>
    simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, -⟩ := h <;> exact ⟨Nat.le_refl _, rfl⟩

theorem taskReturn_next_tasks {st st' : Store} {u t : Nat} {vs : List Val} {r : Res}
    (h : step st (.taskReturn u vs) = some (st', r)) (hu : u ≠ t) :
    st.next ≤ st'.next ∧ st'.tasks t = st.tasks t := by
  simp only [step] at h
  split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, -⟩ := h <;> exact ⟨Nat.le_refl _, by simp [Store.post, upd, Ne.symm hu]⟩

/-- **Only `task.return t` and a new task at `t` change the task `t`; `next` never decreases.** -/
theorem step_next_tasks {st st' : Store} {op : Op} {r : Res} (h : step st op = some (st', r))
    {t : Nat} (hop : ∀ vs, op ≠ .taskReturn t vs) (ht : t < st.next) :
    st.next ≤ st'.next ∧ st'.tasks t = st.tasks t := by
  have of_frame : Frame st st' → st.next ≤ st'.next ∧ st'.tasks t = st.tasks t :=
    fun hf => ⟨hf.1 ▸ Nat.le_refl _, congrFun hf.2 t⟩
  cases op with
  | streamWrite => exact of_frame (streamWrite_frame h)
  | streamRead => exact of_frame (streamRead_frame h)
  | streamDropR => exact of_frame (streamDropR_frame h)
  | streamDropW => exact of_frame (streamDropW_frame h)
  | futureWrite => exact of_frame (futureWrite_frame h)
  | futureRead => exact of_frame (futureRead_frame h)
  | futureDropR => exact of_frame (futureDropR_frame h)
  | futureDropW => exact of_frame (futureDropW_frame h)
  | join => exact of_frame (join_frame h)
  | wait => exact of_frame (wait_frame h)
  | poll => exact of_frame (poll_frame h)
  | streamNew => exact new_next_tasks h (Or.inl rfl)
  | futureNew => exact new_next_tasks h (Or.inr rfl)
  | wsNew => exact wsNew_next_tasks h
  | callAsync => exact callAsync_next_tasks h ht
  | wsDrop => exact drop_next_tasks h (Or.inl ⟨_, rfl⟩)
  | subtaskDrop => exact drop_next_tasks h (Or.inr ⟨_, rfl⟩)
  | taskReturn u vs => exact taskReturn_next_tasks h (fun he => hop vs (he ▸ rfl))

/-- `next` never decreases. -/
theorem step_next {st st' : Store} {op : Op} {r : Res} (h : step st op = some (st', r)) :
    st.next ≤ st'.next := by
  by_cases hop : ∃ t vs, op = .taskReturn t vs
  · obtain ⟨t, vs, rfl⟩ := hop
    simp only [step] at h
    split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;> exact Nat.le_refl _
  · cases hn : st.next with
    | zero => exact Nat.zero_le _
    | succ k =>
      have hk : k < st.next := by omega
      have := (step_next_tasks h (fun vs he => hop ⟨k, vs, he⟩) hk).1
      omega

/-- **Task results are write-once.** -/
theorem step_result_stable {st st' : Store} {op : Op} {r : Res} (h : step st op = some (st', r))
    {t : Nat} (ht : t < st.next) {vs : List Val} (hv : (st.tasks t).result = some vs) :
    (st'.tasks t).result = some vs := by
  by_cases hop : ∃ ws, op = .taskReturn t ws
  · obtain ⟨ws, rfl⟩ := hop
    rw [taskReturn_twice (by simp [hv])] at h
    cases h
  · have hop' : ∀ ws, op ≠ .taskReturn t ws := fun ws he => hop ⟨ws, he⟩
    rw [(step_next_tasks h hop' ht).2]
    exact hv

/-- **Only `task.return` sets a task's result.** -/
theorem result_set_by {st st' : Store} {op : Op} {r : Res} (h : step st op = some (st', r))
    {t : Nat} (ht : t < st.next) (h0 : (st.tasks t).result = none) {vs : List Val}
    (h1 : (st'.tasks t).result = some vs) : op = .taskReturn t vs := by
  by_cases hop : ∃ ws, op = .taskReturn t ws
  · obtain ⟨ws, rfl⟩ := hop
    rw [taskReturn_result h] at h1
    cases h1
    rfl
  · have hop' : ∀ ws, op ≠ .taskReturn t ws := fun ws he => hop ⟨ws, he⟩
    rw [(step_next_tasks h hop' ht).2, h0] at h1
    cases h1

/-! ## Sync lowering -/

/-- The caller's steps do not decrease `next`. -/
theorem syncStep_next {st st' : Store} {pc pc' : SyncPc} (h : syncStep st pc = some (st', pc')) :
    st.next ≤ st'.next := by
  cases pc with
  | start =>
    simp only [syncStep, startSync, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Nat.le_succ _
  | waiting t =>
    simp only [syncStep, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, -, rfl, -⟩ := h
    exact Nat.le_refl _
  | done _ => cases h

/-- The invariant of a sync-lowered caller on the task `t`: `t` is allocated, and the caller is
suspended on `t`, or resumed with the stored results of `t`. -/
def SyncInv (t : Nat) (st : Store) : SyncPc → Prop
  | .start => False
  | .waiting u => t < st.next ∧ u = t
  | .done vs => t < st.next ∧ (st.tasks t).result = some vs

/-- **The invariant holds along every interleaving with other parties.** -/
theorem syncRun_inv {st st' : Store} {pc pc' : SyncPc} (hr : SyncRun st pc st' pc') {t : Nat}
    (hi : SyncInv t st pc) : SyncInv t st' pc' := by
  induction hr with
  | refl => exact hi
  | @caller st pc st₁ pc₁ st₂ pc₂ hs _ ih =>
    apply ih
    cases pc with
    | start => exact hi.elim
    | waiting u =>
      obtain ⟨ht, rfl⟩ := hi
      simp only [syncStep, Option.map_eq_some_iff, Prod.mk.injEq] at hs
      obtain ⟨ws, hw, rfl, rfl⟩ := hs
      exact ⟨ht, hw⟩
    | done _ => cases hs
  | @env st pc st₁ r st₂ pc₂ op hs _ ih =>
    apply ih
    have hn := step_next hs
    cases pc with
    | start => exact hi.elim
    | waiting u => exact ⟨Nat.lt_of_lt_of_le hi.1 hn, hi.2⟩
    | done ws => exact ⟨Nat.lt_of_lt_of_le hi.1 hn, step_result_stable hs hi.1 hi.2⟩

/-- **Sync lowering resumes with the stored results**: along every interleaving with other
parties, a caller suspended on `t` resumes with `(tasks t).result`, which no later step
changes. -/
theorem syncRun_result {st st' : Store} {vs : List Val} {t : Nat}
    (hr : SyncRun st (.waiting t) st' (.done vs)) (ht : t < st.next) :
    (st'.tasks t).result = some vs :=
  (syncRun_inv hr (t := t) ⟨ht, rfl⟩).2

/-- From the call: the caller is not started yet, or the invariant holds for a task
`t ≥ st.next`. -/
theorem syncRun_start {st st' : Store} {pc pc' : SyncPc} (hr : SyncRun st pc st' pc')
    (hpc : pc = .start) : pc' = .start ∨ ∃ t, st.next ≤ t ∧ SyncInv t st' pc' := by
  induction hr with
  | refl => exact Or.inl hpc
  | @caller st pc st₁ pc₁ st₂ pc₂ hs hrest _ =>
    subst hpc
    simp only [syncStep, startSync, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact Or.inr ⟨st.next, Nat.le_refl _, syncRun_inv hrest ⟨Nat.lt_succ_self _, rfl⟩⟩
  | @env st pc st₁ r st₂ pc₂ op hs _ ih =>
    rcases ih hpc with h | ⟨t, ht, hv⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, Nat.le_trans (step_next hs) ht, hv⟩

/-- **Sync lowering from the call**: a caller started at `st` resumes with the results stored
for the task `t ≥ st.next` it started (which, by `result_set_by`, only `task.return t` sets). -/
theorem sync_from_start {st st' : Store} {vs : List Val}
    (hr : SyncRun st .start st' (.done vs)) :
    ∃ t, st.next ≤ t ∧ (st'.tasks t).result = some vs := by
  rcases syncRun_start hr rfl with h | ⟨t, ht, hv⟩
  · cases h
  · exact ⟨t, ht, hv.2⟩

/-- **The caller can resume as soon as the callee has returned.** -/
theorem sync_resumes {st : Store} {t : Nat} {vs : List Val} (h : (st.tasks t).result = some vs) :
    syncStep st (.waiting t) = some (st, .done vs) := by
  simp [syncStep, h]

/-! ## A worked run -/

/-- Two items. -/
def demoItems : List Val := [.u8 104, .u8 105]

/-- `stream.new`, `waitable-set.new`, a blocked `stream.write` of two items, `waitable.join`
of the writer, the peer's `stream.read` of `8` items, and `waitable-set.wait`. -/
def demo : Option (Store × Res) := do
  let (s1, _) ← step .empty .streamNew        -- r = 1, w = 2
  let (s2, _) ← step s1 .wsNew                 -- set 3
  let (s3, _) ← step s2 (.streamWrite 2 demoItems)
  let (s4, _) ← step s3 (.join 2 3)
  let (s5, _) ← step s4 (.streamRead 1 8)
  step s5 (.wait 3)

/-- **The worked run**: `wait` returns the writer's `stream-write COMPLETED 2` event. -/
theorem demo_events :
    (demo.map fun p => match p.2 with
      | .event e => (e.code, e.index, e.payload)
      | _ => (.none, 0, 0)) = some (.streamWrite, 2, packCopy .completed 2) := by
  decide

end Silmaril.Wasm.Component.Async
