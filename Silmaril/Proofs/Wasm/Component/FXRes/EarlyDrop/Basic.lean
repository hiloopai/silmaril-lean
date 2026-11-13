module

public import Silmaril.Wasm.Component.FXRes.EarlyDrop.Defs
public import Silmaril.Wasm.Component.FXRes.Borrow.Thms

/-!
# Early drops of borrowed handles: proofs

* `srun_drop_borrowed`: `resource.drop` of an entry whose handle object is borrowed (of the
  dropped resource type, not lent, with a borrow scope) has a successful run, returning `none`
  (no destructor call) and decrementing the scope's `num_borrows`;
* `lowered_then_dropped`: so right after `lower_borrow` gives a callee a borrowed handle at `i`,
  `resource.drop` of `i` in that instance succeeds (the hypotheses of
  `Borrow.lowered_borrow_at`);
* `obProto_rejects_early_drop`: the ownership reading of that two-event history,
  `[lend i, free i]`, is rejected by `obProto`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.EarlyDrop

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Resource Silmaril.Wasm.Component.FXRes.Borrow

variable {E : CoreEngine} {σ : Type}

/-- **`resource.drop` of a borrowed handle succeeds**: no destructor, `num_borrows - 1`. -/
theorem srun_drop_borrowed {lim : Limits} {j : InstId} {rt : RtId} {i : ℕ} {s : CStore E}
    {r : ResourceHandle} {τ : TaskId} (hat : HandleAt s j i r) (hrt : r.rt = rt)
    (hl : r.numLends = 0) (ho : r.own = false) (hsc : r.scope = some τ) :
    ∃ s', SRun (σ := σ) (resourceDropCore lim j rt i) s none s' := by
  obtain ⟨st, hid, hst, hg, hr⟩ := hat
  have hrm : st.removeHandle? i =
      some (.resource hid, { st with handles := ⟨st.handles.array.setIfInBounds i none,
        i :: st.handles.free⟩ }) := by
    simp [InstState.removeHandle?, Table.remove?, hg]
  let s₁ := ArenaField.insts.modify s j (InstState.removeHandle i)
  have hr₁ : ArenaField.resHandles.get? s₁ hid = some r :=
    (resHandles_insts_modify s j _ hid).trans hr
  refine ⟨HandleSt.decBorrows τ s₁, ?_⟩
  unfold resourceDropCore
  refine srun_bind.2 ⟨.resource hid, s₁, srun_handlesRemove.2 ⟨st, _, hst, hrm, rfl⟩, ?_⟩
  refine srun_bind.2 ⟨hid, s₁, srun_expectResource.2 ⟨rfl, rfl⟩, ?_⟩
  refine srun_bind.2 ⟨r, s₁, srun_getResHandle.2 ⟨hr₁, rfl⟩, ?_⟩
  refine srun_bind.2 ⟨(), s₁, srun_trapIf.2 ⟨by simp [hrt], rfl⟩, ?_⟩
  refine srun_bind.2 ⟨(), s₁, srun_trapIf.2 ⟨by simp [hl], rfl⟩, ?_⟩
  unfold dropHandleTail
  simp only [ho, Bool.false_eq_true, ite_false, hsc]
  exact srun_bind.2 ⟨(), _, srun_modifyStore.2 rfl, srun_pure.2 ⟨rfl, rfl⟩⟩

/-- **A borrowed handle can be dropped right after it is lowered.** -/
theorem lowered_then_dropped {lim lim' : Limits} {cx : LiftLowerContext E} {rt : RtId} {rep : ℕ}
    {τ : TaskId} (hsc : cx.scope = .task τ) {s s₁ : CStore E} {i : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? s rt = some rty → rty.impl ≠ some cx.inst)
    (hwf : ∀ st, s.inst? cx.inst = some st → FreeOK st.handles)
    (h : SRun (σ := σ) (lowerBorrow lim cx rt rep) s i s₁) :
    ∃ s₂, SRun (σ := σ) (resourceDropCore lim' cx.inst rt i) s₁ none s₂ :=
  srun_drop_borrowed (lowered_borrow_at hsc himpl hwf h) rfl rfl rfl rfl

/-- **`obProto` rejects the early drop of a borrow.** -/
theorem obProto_rejects_early_drop (i : ℕ) : ¬ (obProto ℕ).Accepts [.lend i, .free i] := by
  simp [Protocol.Accepts, Protocol.run, obProto, obStep, held, owns]

/-- **The machine allows a history that `obProto` rejects**: after `lower_borrow` gives a callee
a borrowed handle at `i` (entry `e`), `resource.drop` of `i` succeeds, and the ownership reading of
the table history `[added i e, removed i e]`, with the modes of the store after the lowering, is
rejected by `obProto`. -/
theorem early_drop_rejected {lim lim' : Limits} {cx : LiftLowerContext E} {rt : RtId} {rep : ℕ}
    {τ : TaskId} (hsc : cx.scope = .task τ) {s s₁ : CStore E} {i : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? s rt = some rty → rty.impl ≠ some cx.inst)
    (hwf : ∀ st, s.inst? cx.inst = some st → FreeOK st.handles)
    (h : SRun (σ := σ) (lowerBorrow lim cx rt rep) s i s₁) :
    ∃ st e, s₁.inst? cx.inst = some st ∧ st.handles.get? i = some e ∧
      ([Table.Event.added i e, .removed i e].map (obEvOf (modeOf s₁))) = [.lend i, .free i] ∧
      ¬ (obProto ℕ).Accepts ([Table.Event.added i e, .removed i e].map (obEvOf (modeOf s₁))) ∧
      ∃ s₂, SRun (σ := σ) (resourceDropCore lim' cx.inst rt i) s₁ none s₂ := by
  obtain ⟨st, hid, hst, hg, hr⟩ := lowered_borrow_at hsc himpl hwf h
  have hm : modeOf s₁ (.resource hid) = .borrowed := by
    simp [modeOf, hr, borrowObj]
  have he : ([Table.Event.added i (HandleEntry.resource hid), .removed i (.resource hid)].map
      (obEvOf (modeOf s₁))) = [.lend i, .free i] := by
    simp [obEvOf, hm]
  exact ⟨st, .resource hid, hst, hg, he, he ▸ obProto_rejects_early_drop i,
    lowered_then_dropped hsc himpl hwf h⟩

end Silmaril.Wasm.Component.FXRes.EarlyDrop
