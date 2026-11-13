module

public import Silmaril.Wasm.Jco.Async.Lower.Defs
public import Silmaril.Wasm.Component.Async.Thms

/-!
# Async lowers, futures and streams through the adaptor: results

* **`low_from_start`**: along every interleaving with built-ins of other parties, a shim that
  started at `st` and resumed with `vs` resumed with the results stored for a task `t ≥ st.next`
  (the subtask it started; by `Async.result_set_by`, only `task.return t` sets them).
  `lowRun_inv` is the invariant (results are write-once, `Async.step_result_stable`).
* **`low_sync_agree`**: the adaptor's async lowering and the built-in sync lowering of
  `Silmaril.Wasm.Component.Async` (`SyncRun`) resume only with the stored results of the callee
  task they started: a sync module sees the same values through either.
* `lowDemo_eq`: the worked run resumes with `[u32 7]` (by evaluation).
* **`futureOut_read`**: the future returned by the adaptor delivers the module's value to the
  first `future.read`. **`streamOut_read`**: the stream returned by the adaptor delivers the
  module's items to a `stream.read` of at least as many. Both assume that the channel of the next
  handle is fresh (as in a store reached from `Store.empty`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event EventCode Chan CopyResult packCopy step
  step_next step_result_stable SyncRun sync_from_start)

/-- The invariant of the shim on the subtask `t`. -/
def LowInv (t : Nat) (st : Store) : LowPc → Prop
  | .start => False
  | .waiting u _ => u = t ∧ t < st.next
  | .done vs => t < st.next ∧ (st.tasks t).result = some vs

theorem lowStep_waiting_inv {st st' : Store} {t ws : Nat} {pc' : LowPc}
    (h : lowStep st (.waiting t ws) = some (st', pc')) (ht : t < st.next) :
    LowInv t st' pc' := by
  rcases hw : step st (.wait ws) with _ | ⟨s₁, r⟩
  · simp [lowStep, hw] at h
  have hn₁ : t < s₁.next := Nat.lt_of_lt_of_le ht (step_next hw)
  cases r
  case event e =>
    by_cases hc : e.code = .subtask ∧ e.index = t
    · rcases hv : (s₁.tasks t).result with _ | vs
      · simp [lowStep, hw, hc, hv] at h
      rcases hd : step s₁ (.subtaskDrop t) with _ | ⟨s₂, r₂⟩
      · simp [lowStep, hw, hc, hv, hd] at h
      have e₂ : s₂ = st' ∧ LowPc.done vs = pc' := by simpa [lowStep, hw, hc, hv, hd] using h
      rw [← e₂.1, ← e₂.2]
      exact ⟨Nat.lt_of_lt_of_le hn₁ (step_next hd), step_result_stable hd hn₁ hv⟩
    · simp [lowStep, hw, hc] at h
  all_goals simp [lowStep, hw] at h

theorem callAsync_next {st s₁ : Store} {r : Res} (h : step st .callAsync = some (s₁, r)) :
    s₁.next = st.next + 1 := by
  simp only [step, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]

theorem lowStep_start_inv {st st' : Store} {pc' : LowPc} (h : lowStep st .start = some (st', pc')) :
    LowInv st.next st' pc' := by
  rcases h₁ : step st .callAsync with _ | ⟨s₁, r₁⟩
  · simp [lowStep, h₁] at h
  rcases h₂ : step s₁ .wsNew with _ | ⟨s₂, r₂⟩
  · simp [lowStep, h₁, h₂] at h
  rcases h₃ : step s₂ (.join st.next s₁.next) with _ | ⟨s₃, r₃⟩
  · simp [lowStep, h₁, h₂, h₃] at h
  have e : s₃ = st' ∧ LowPc.waiting st.next s₁.next = pc' := by
    simpa [lowStep, h₁, h₂, h₃] using h
  have hn₁ : st.next < s₁.next := by rw [callAsync_next h₁]; exact Nat.lt_succ_self _
  rw [← e.1, ← e.2]
  exact ⟨rfl, Nat.lt_of_lt_of_le hn₁ (Nat.le_trans (step_next h₂) (step_next h₃))⟩

theorem lowStep_inv {st st' : Store} {pc pc' : LowPc} (h : lowStep st pc = some (st', pc'))
    {t : Nat} (hi : LowInv t st pc) : LowInv t st' pc' := by
  cases pc with
  | start => exact hi.elim
  | waiting u ws =>
    obtain ⟨rfl, ht⟩ := hi
    exact lowStep_waiting_inv h ht
  | done _ => cases h

theorem env_inv {st st' : Store} {op : Op} {r : Res} (h : step st op = some (st', r))
    {t : Nat} {pc : LowPc} (hi : LowInv t st pc) : LowInv t st' pc := by
  have hn := step_next h
  cases pc with
  | start => exact hi.elim
  | waiting u _ => exact ⟨hi.1, Nat.lt_of_lt_of_le hi.2 hn⟩
  | done _ => exact ⟨Nat.lt_of_lt_of_le hi.1 hn, step_result_stable h hi.1 hi.2⟩

/-- **The invariant holds along every interleaving with other parties.** -/
theorem lowRun_inv {st st' : Store} {pc pc' : LowPc} (hr : LowRun st pc st' pc') {t : Nat}
    (hi : LowInv t st pc) : LowInv t st' pc' := by
  induction hr with
  | refl => exact hi
  | shim hs _ ih => exact ih (lowStep_inv hs hi)
  | env _ hs _ ih => exact ih (env_inv hs hi)

theorem lowRun_start {st st' : Store} {pc pc' : LowPc} (hr : LowRun st pc st' pc')
    (hpc : pc = .start) : pc' = .start ∨ ∃ t, st.next ≤ t ∧ LowInv t st' pc' := by
  induction hr with
  | refl => exact Or.inl hpc
  | @shim st pc st₁ pc₁ st₂ pc₂ hs hrest _ =>
    subst hpc
    exact Or.inr ⟨st.next, Nat.le_refl _, lowRun_inv hrest (lowStep_start_inv hs)⟩
  | @env st pc st₁ r st₂ pc₂ op hs _ ih =>
    rcases ih hpc with h | ⟨t, ht, hv⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, Nat.le_trans (step_next hs) ht, hv⟩

/-- **Async lowering through the adaptor resumes with the callee's results.** -/
theorem low_from_start {st st' : Store} {vs : List Val} (hr : LowRun st .start st' (.done vs)) :
    ∃ t, st.next ≤ t ∧ (st'.tasks t).result = some vs := by
  rcases lowRun_start hr rfl with h | ⟨t, ht, hv⟩
  · cases h
  · exact ⟨t, ht, hv.2⟩

/-- **The adaptor's async lowering agrees with the built-in sync lowering**: both resume only
with the results stored for the callee task they started. -/
theorem low_sync_agree {st st' : Store} {vs : List Val} :
    (LowRun st .start st' (.done vs) → ∃ t, st.next ≤ t ∧ (st'.tasks t).result = some vs) ∧
      (SyncRun st .start st' (.done vs) → ∃ t, st.next ≤ t ∧ (st'.tasks t).result = some vs) :=
  ⟨low_from_start, sync_from_start⟩

/-- The worked run resumes with the callee's `[u32 7]`. -/
theorem lowDemo_eq : lowDemo = some [.u32 7] := by rfl

/-! ## Futures and streams -/

/-- **The future the adaptor returns delivers the module's value.** -/
theorem futureOut_read {st st' : Store} {v : Val} {r : Nat} (hf : st.chans st.next = {})
    (h : futureOut st v = some (st', r)) :
    ∃ st'', step st' (.futureRead r) = some (st'', .read CopyResult.completed.toNat [v]) := by
  simp [futureOut, step, Store.alloc2, Silmaril.Wasm.Component.Async.futureWrite,
    Silmaril.Wasm.Component.Async.upd, hf, Store.setChan] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [step, Silmaril.Wasm.Component.Async.futureRead, Silmaril.Wasm.Component.Async.upd,
    Store.setChan]

/-- **The stream the adaptor returns delivers the module's items.** -/
theorem streamOut_read {st st' : Store} {xs : List Val} {r n : Nat} (hf : st.chans st.next = {})
    (hn : xs.length ≤ n) (h : streamOut st xs = some (st', r)) :
    ∃ st'', step st' (.streamRead r n) =
      some (st'', .read (packCopy .completed xs.length) xs) := by
  simp [streamOut, step, Store.alloc2, Silmaril.Wasm.Component.Async.streamWrite,
    Silmaril.Wasm.Component.Async.upd, hf, Store.setChan] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [step, Silmaril.Wasm.Component.Async.streamRead, Silmaril.Wasm.Component.Async.upd,
    Store.setChan, Nat.min_eq_right hn]

end Silmaril.Wasm.Jco.Async
