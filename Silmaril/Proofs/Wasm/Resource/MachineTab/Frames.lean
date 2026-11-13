module

public import Silmaril.Proofs.Wasm.Resource.MachineTab.Frame
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# Handle tables along whole machine runs: the store updates that keep the instance arena

The named store updates of the reference programs that are not handle-table operations leave
the instance arena unchanged (or change an instance but not its handle table). Most are
updates of another arena and hold by `rfl`; the ones defined by cases (memory writes, waitable
bookkeeping, stream ends, lends) are proved here.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Value

variable {E : CoreEngine}

theorem writeMemSt_insts (m : E.MemAddr) (p : ℕ) (bs : ByteArray) (s : CStore E) :
    (writeMemSt m p bs s).insts = s.insts := by
  unfold writeMemSt; split <;> rfl

theorem modifyWaitableCommon_insts (w : Waitable) (f : WaitableCommon → WaitableCommon)
    (s : CStore E) : (CStore.modifyWaitableCommon w f s).insts = s.insts := by
  cases w <;> rfl

theorem joinSt_insts (w : Waitable) (ws : Option WsetId) (s : CStore E) :
    (CStore.joinSt w ws s).insts = s.insts := by
  unfold CStore.joinSt
  split
  · rfl
  · rename_i c _
    cases c.wset <;> cases ws <;> exact modifyWaitableCommon_insts _ _ _

theorem foldl_insts {g : CStore E → HandleObjId → CStore E}
    (hg : ∀ s h, (g s h).insts = s.insts) (l : List HandleObjId) (s : CStore E) :
    (l.foldl g s).insts = s.insts := by
  induction l generalizing s with
  | nil => rfl
  | cons h l ih => exact (ih _).trans (hg s h)

theorem deliverResolveSt_insts (st : SubtaskId) (s : CStore E) :
    (CStore.deliverResolveSt st s).insts = s.insts := by
  unfold CStore.deliverResolveSt
  split
  · rfl
  · exact foldl_insts (g := fun s h => ArenaField.resHandles.modify s h fun r =>
      { r with numLends := r.numLends - 1 }) (fun _ _ => rfl) _ _

theorem releaseLendsSt_insts (st : SubtaskId) (s : CStore E) :
    (LowerSt.releaseLendsSt st s).insts = s.insts := by
  unfold LowerSt.releaseLendsSt
  split
  · rfl
  · split
    · rfl
    · exact foldl_insts (g := fun s h => ArenaField.resHandles.modify s h fun r =>
        { r with numLends := r.numLends - 1 }) (fun _ _ => rfl) _ _

theorem deliver_insts (e : EndId) (p : ℕ) (s : CStore E) : (deliver e p s).1.insts = s.insts := by
  unfold deliver; split <;> rfl

theorem takeEvent_insts (e : EndId) (s : CStore E) : (takeEvent e s).1.insts = s.insts := by
  unfold takeEvent
  split
  · rfl
  · split <;> first | rfl | exact deliver_insts _ _ _

theorem subtaskEvent_insts (st : SubtaskId) (s : CStore E) :
    (CStore.subtaskEvent st s).1.insts = s.insts := by
  unfold CStore.subtaskEvent
  split
  · rfl
  · split
    · exact deliverResolveSt_insts _ _
    · rfl

theorem takeWaitableEventSt_insts (w : Waitable) (s : CStore E) :
    (CStore.takeWaitableEventSt w s).insts = s.insts := by
  unfold CStore.takeWaitableEventSt CStore.takeWaitableEvent
  cases w with
  | end_ e => exact takeEvent_insts e s
  | subtask st =>
    simp only
    split
    · rfl
    · split
      · exact (subtaskEvent_insts _ _).trans (modifyWaitableCommon_insts _ _ _)
      · rfl

theorem copyCore_insts {e : EndId} {b : BufferDesc E} {r : Bool} {s : CStore E}
    {s' : CStore E × CopyAction E} (h : copyCore e b r s = .ok s') : s'.1.insts = s.insts := by
  unfold copyCore at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

theorem copySt_insts (e : EndId) (b : BufferDesc E) (r : Bool) (s : CStore E) :
    (copySt e b r s).insts = s.insts := by
  unfold copySt
  split
  · rename_i h; exact copyCore_insts h
  · rfl

set_option linter.unusedSimpArgs false in
theorem dropEnd_insts (e : EndId) (s : CStore E) : (Runtime.dropEnd e s).insts = s.insts := by
  unfold Runtime.dropEnd leaveSet
  split
  · rfl
  · rename_i x _
    cases ho : x.other <;> cases hw : x.common.wset <;> simp only [ho, hw]
    all_goals first | rfl | (split <;> (try split) <;> rfl)

theorem forward_insts (src dst : EndId) (s : CStore E) (s' : CStore E × CopyAction E)
    (h : forward src dst s = .ok s') : s'.1.insts = s.insts := by
  unfold forward at h
  repeat' split at h
  all_goals first | (cases h; rfl) | (cases h; exact (dropEnd_insts _ _).trans (dropEnd_insts _ _)) | cases h | (dsimp only at h; exact (copyCore_insts h).trans rfl)

theorem forwardSt_insts (src dst : EndId) (s : CStore E) :
    (forwardSt src dst s).insts = s.insts := by
  unfold forwardSt
  split
  · rename_i h; exact forward_insts _ _ _ _ h
  · rfl

theorem cancel_insts (e : EndId) (b : Bool) (s : CStore E) :
    (Runtime.cancel e b s).insts = s.insts := by
  unfold Runtime.cancel
  repeat' split
  all_goals rfl

theorem TabMove.of_vtab {j : InstId} {s s' : CStore E} (h : vtab s' j = vtab s j) :
    TabMove j s s' :=
  ⟨[], h ▸ .nil _⟩

theorem vtab_set_frame {j : InstId} {s : CStore E} {i : InstId} {st st' : InstState}
    (hst : s.inst? i = some st) (hh : st'.handles = st.handles) :
    vtab (ArenaField.insts.set s i st') j = vtab s j := by
  unfold vtab handles? CStore.inst?
  rw [ArenaField.get?_set]
  split
  · rename_i h
    subst h
    have hst' : ArenaField.insts.get? s i = some st := hst
    simp [hst', hh]
  · rfl

/-- `register_thread` changes an instance's thread table, not its handle table. -/
theorem tabMove_registerThreadSt {j : InstId} (task : TaskId) (t : ThreadId) (s : CStore E) :
    TabMove j s (CStore.registerThreadSt task t s) := by
  unfold CStore.registerThreadSt
  split
  · exact TabMove.refl _
  · rename_i tk _
    split
    · exact TabMove.refl _
    · rename_i i st' hb
      obtain ⟨st, hst, ha⟩ := Option.bind_eq_some_iff.1 hb
      obtain ⟨⟨i', tb⟩, -, he⟩ := Option.map_eq_some_iff.1 ha
      have hh : st'.handles = st.handles := by cases he; rfl
      exact TabMove.of_vtab (vtab_set_frame (s := ArenaField.tasks.modify s task fun x =>
        { x with threads := x.threads ++ [t] }) hst hh)

end Silmaril.Wasm.Resource
