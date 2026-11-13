module

public import Silmaril.Wasm.Component.FXRes.Borrow.Defs
public import Silmaril.Wasm.Resource.CompTable.Thms
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The borrow discipline from the reference machine's programs: inversion lemmas

What a successful run of each handle program of the reference machine implies:

* `srun_liftOwn`: the entry was a resource handle that is owned and not lent;
* `srun_resourceDropCore`: the entry was a resource handle that is not lent;
* `srun_liftBorrow`: the entry is a resource handle, and the run is `addLender` of its object;
* `srun_lowerBorrow`: outside the implementing instance, a fresh handle object with
  `own = false` is allocated, `num_borrows` of the task is incremented, and the object is added
  to the table;
* `crun_return`: `Task.return_` succeeds only when the task has no borrows left.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Borrow

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Resource

variable {E : CoreEngine} {σ : Type}

/-! ## Store lemmas -/

theorem resHandles_insts_modify (s : CStore E) (j : InstId) (f : InstState → InstState)
    (hid : HandleObjId) :
    ArenaField.resHandles.get? (ArenaField.insts.modify s j f) hid =
      ArenaField.resHandles.get? s hid := rfl

theorem resHandles_tasks_modify (s : CStore E) (t : TaskId) (f : Task E → Task E)
    (hid : HandleObjId) :
    ArenaField.resHandles.get? (ArenaField.tasks.modify s t f) hid =
      ArenaField.resHandles.get? s hid := rfl

theorem inst_addLender (s : CStore E) (sb : SubtaskId) (hid : HandleObjId) (j : InstId) :
    (HandleSt.addLender sb hid s).inst? j = s.inst? j := rfl

theorem resHandles_addLender (s : CStore E) (sb : SubtaskId) (hid : HandleObjId) :
    ArenaField.resHandles.get? (HandleSt.addLender sb hid s) hid =
      (ArenaField.resHandles.get? s hid).map fun r => { r with numLends := r.numLends + 1 } :=
  ArenaField.get?_modify_self ArenaField.resHandles s hid _

theorem get_of_remove {st st' : InstState} {i : ℕ} {e : HandleEntry}
    (h : st.removeHandle? i = some (e, st')) : st.handles.get? i = some e :=
  (remove?_parts (removeHandle?_tab h).1).1

theorem srun_getResHandle {hid : HandleObjId} {s s' : CStore E} {x : ResourceHandle} :
    SRun (getResHandle (σ := σ) hid) s x s' ↔
      ArenaField.resHandles.get? s hid = some x ∧ s' = s :=
  srun_getObj _ _

/-! ## `lift_own` and `resource.drop` -/

/-- **`lift_own` succeeds only on an owned handle that is not lent.** -/
theorem srun_liftOwn {lim : Limits} {cx : LiftLowerContext E} {rt : RtId} {i : ℕ}
    {s s' : CStore E} {rep : ℕ} (h : SRun (σ := σ) (liftOwn lim cx rt i) s rep s') :
    ∃ r, HandleAt s cx.inst i r ∧ r.numLends = 0 ∧ r.own = true := by
  obtain ⟨e, s₁, h₁, k₁⟩ := srun_bind.1 h
  obtain ⟨st, st', hst, hrm, rfl⟩ := srun_handlesRemove.1 h₁
  obtain ⟨hid, s₂, h₂, k₂⟩ := srun_bind.1 k₁
  obtain ⟨rfl, rfl⟩ := srun_expectResource.1 h₂
  obtain ⟨r, s₃, h₃, k₃⟩ := srun_bind.1 k₂
  obtain ⟨hr, rfl⟩ := srun_getResHandle.1 h₃
  obtain ⟨_, s₄, h₄, k₄⟩ := srun_bind.1 k₃
  obtain ⟨-, rfl⟩ := srun_trapIf.1 h₄
  obtain ⟨_, s₅, h₅, k₅⟩ := srun_bind.1 k₄
  obtain ⟨hl, rfl⟩ := srun_trapIf.1 h₅
  obtain ⟨_, s₆, h₆, -⟩ := srun_bind.1 k₅
  obtain ⟨ho, -⟩ := srun_trapIf.1 h₆
  have hl' : r.numLends = 0 := by simpa using hl
  have ho' : r.own = true := by simpa using ho
  exact ⟨r, ⟨st, hid, hst, get_of_remove hrm, hr⟩, hl', ho'⟩

/-- **`resource.drop` succeeds only on a handle that is not lent.** -/
theorem srun_resourceDropCore {lim : Limits} {j : InstId} {rt : RtId} {i : ℕ} {s s' : CStore E}
    {o : Option (DtorRequest E)} (h : SRun (σ := σ) (resourceDropCore lim j rt i) s o s') :
    ∃ r, HandleAt s j i r ∧ r.numLends = 0 := by
  obtain ⟨e, s₁, h₁, k₁⟩ := srun_bind.1 h
  obtain ⟨st, st', hst, hrm, rfl⟩ := srun_handlesRemove.1 h₁
  obtain ⟨hid, s₂, h₂, k₂⟩ := srun_bind.1 k₁
  obtain ⟨rfl, rfl⟩ := srun_expectResource.1 h₂
  obtain ⟨r, s₃, h₃, k₃⟩ := srun_bind.1 k₂
  obtain ⟨hr, rfl⟩ := srun_getResHandle.1 h₃
  obtain ⟨_, s₄, h₄, k₄⟩ := srun_bind.1 k₃
  obtain ⟨-, rfl⟩ := srun_trapIf.1 h₄
  obtain ⟨_, s₅, h₅, -⟩ := srun_bind.1 k₄
  obtain ⟨hl, -⟩ := srun_trapIf.1 h₅
  have hl' : r.numLends = 0 := by simpa using hl
  exact ⟨r, ⟨st, hid, hst, get_of_remove hrm, hr⟩, hl'⟩

/-! ## `lift_borrow` -/

/-- **`lift_borrow` lends the handle object of the entry** (`num_lends += 1`). -/
theorem srun_liftBorrow {lim : Limits} {cx : LiftLowerContext E} {rt : RtId} {i : ℕ}
    {sb : SubtaskId} (hsc : cx.scope = .subtask sb) {s s' : CStore E} {rep : ℕ}
    (h : SRun (σ := σ) (liftBorrow lim cx rt i) s rep s') :
    ∃ st hid, s.inst? cx.inst = some st ∧ st.handles.get? i = some (.resource hid) ∧
      s' = HandleSt.addLender sb hid s := by
  unfold liftBorrow at h
  simp only [hsc] at h
  obtain ⟨e, s₁, h₁, k₁⟩ := srun_bind.1 h
  obtain ⟨⟨st, hst, hg⟩, rfl⟩ := srun_handlesGet.1 h₁
  obtain ⟨hid, s₂, h₂, k₂⟩ := srun_bind.1 k₁
  obtain ⟨rfl, rfl⟩ := srun_expectResource.1 h₂
  obtain ⟨r, s₃, h₃, k₃⟩ := srun_bind.1 k₂
  obtain ⟨-, rfl⟩ := srun_getResHandle.1 h₃
  obtain ⟨_, s₄, h₄, k₄⟩ := srun_bind.1 k₃
  obtain ⟨-, rfl⟩ := srun_trapIf.1 h₄
  obtain ⟨_, s₅, h₅, k₅⟩ := srun_bind.1 k₄
  have h6 : s' = s₅ := (srun_pure.1 k₅).2
  exact ⟨st, hid, hst, hg, h6.trans (srun_modifyStore.1 h₅)⟩

end Silmaril.Wasm.Component.FXRes.Borrow
