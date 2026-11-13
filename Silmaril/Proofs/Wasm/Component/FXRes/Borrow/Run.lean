module

public import Silmaril.Proofs.Wasm.Component.FXRes.Borrow.Basic
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The borrow discipline from the reference machine's programs: two-program runs

* `srun_lowerBorrow`, `lowered_borrow_at`: outside the implementing instance, `lower_borrow`
  puts a handle object with `own = false` at the index it returns;
* **`borrow_not_given`**: so a `lift_own` of that index right after (a transfer of the borrowed
  handle by the callee) has no successful run;
* `lent_at`: after `lift_borrow`, the lent handle has `num_lends ≥ 1`;
* **`lent_not_given`**, **`lent_not_dropped`**: so the lender can neither transfer nor drop it
  while it is lent;
* **`crun_return`**: `Task.return_` (the end of an export call) succeeds only when no borrow of
  the task is left (`num_borrows = 0`), whatever its late-bound `on_resolve` call answers.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Borrow

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Resource

variable {E : CoreEngine} {σ : Type}

/-- The handle object of an entry is determined by the store. -/
theorem handleAt_unique {s : CStore E} {j : InstId} {i : ℕ} {x y : ResourceHandle}
    (hx : HandleAt s j i x) (hy : HandleAt s j i y) : x = y := by
  obtain ⟨st, hid, hst, hg, hr⟩ := hx
  obtain ⟨st', hid', hst', hg', hr'⟩ := hy
  have hst'' : st' = st := Option.some.inj (hst'.symm.trans hst)
  have hid'' : HandleEntry.resource hid' = .resource hid := by
    rw [hst''] at hg'; exact Option.some.inj (hg'.symm.trans hg)
  have hid₃ : hid' = hid := by cases hid''; rfl
  rw [hid₃] at hr'
  exact Option.some.inj (hr.symm.trans hr')

/-! ## `lower_borrow` -/

/-- The id of the next handle object. -/
def freshHid (s : CStore E) : HandleObjId :=
  (ArenaField.resHandles (E := E)).mkId ((ArenaField.resHandles (E := E)).size s)

/-- The borrowed handle object of `lower_borrow` at task `τ`. -/
def borrowObj (rt : RtId) (rep : ℕ) (τ : TaskId) : ResourceHandle :=
  { rt := rt, rep := rep, own := false, scope := some τ }

theorem srun_lowerBorrow {lim : Limits} {cx : LiftLowerContext E} {rt : RtId} {rep : ℕ}
    {τ : TaskId} (hsc : cx.scope = .task τ) {s s' : CStore E} {i : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? s rt = some rty → rty.impl ≠ some cx.inst)
    (h : SRun (σ := σ) (lowerBorrow lim cx rt rep) s i s') :
    ∃ s₃, s₃ = HandleSt.incBorrows τ (ArenaOps.allocSt ArenaField.resHandles (borrowObj rt rep τ) s) ∧
      SRun (σ := σ) (handlesAdd cx.inst (.resource (freshHid s))) s₃ i s' := by
  unfold lowerBorrow at h
  simp only [hsc] at h
  obtain ⟨rty, s₁, h₁, k₁⟩ := srun_bind.1 h
  obtain ⟨hrty, e₁⟩ := (srun_getObj _ _).1 h₁
  have hne : rty.impl ≠ some cx.inst := himpl rty hrty
  simp only [hne, ite_false] at k₁
  obtain ⟨hid, s₂, h₂, k₂⟩ := srun_bind.1 k₁
  obtain ⟨e₂, e₃⟩ := (srun_allocObj _ _).1 h₂
  obtain ⟨u, s₃, h₃, k₃⟩ := srun_bind.1 k₂
  have e₄ : s₃ = HandleSt.incBorrows τ s₂ := srun_modifyStore.1 h₃
  rw [e₂, e₁] at k₃
  rw [e₃, e₁] at e₄
  exact ⟨s₃, e₄, k₃⟩

/-- **`lower_borrow` puts a non-owning handle at the index it returns.** -/
theorem lowered_borrow_at {lim : Limits} {cx : LiftLowerContext E} {rt : RtId} {rep : ℕ}
    {τ : TaskId} (hsc : cx.scope = .task τ) {s s' : CStore E} {i : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? s rt = some rty → rty.impl ≠ some cx.inst)
    (hwf : ∀ st, s.inst? cx.inst = some st → FreeOK st.handles)
    (h : SRun (σ := σ) (lowerBorrow lim cx rt rep) s i s') :
    HandleAt s' cx.inst i (borrowObj rt rep τ) := by
  obtain ⟨s₃, rfl, ha⟩ := srun_lowerBorrow hsc himpl h
  obtain ⟨st, st', hst, hadd, rfl⟩ := srun_handlesAdd.1 ha
  obtain ⟨hadd', hst'⟩ := addHandle?_tab hadd
  have hst₀ : s.inst? cx.inst = some st := hst
  have hget : st'.handles.get? i = some (.resource (freshHid s)) :=
    (add?_fresh (hwf st hst₀) hadd').2.1
  refine ⟨st', _, ?_, hget, ArenaField.get?_alloc_self ArenaField.resHandles s _⟩
  rw [CStore.inst?, ArenaField.get?_modify_self]
  change (s.inst? cx.inst).map _ = _
  rw [hst₀, Option.map_some, hst']

/-- **A borrowed handle cannot be transferred**: right after `lower_borrow`, `lift_own` of the
returned index in the same instance has no successful run. -/
theorem borrow_not_given {lim lim' : Limits} {cx cx' : LiftLowerContext E} {rt rt' : RtId}
    {rep : ℕ} {τ : TaskId} (hsc : cx.scope = .task τ) (hj : cx'.inst = cx.inst)
    {s s₁ s₂ : CStore E} {i r : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? s rt = some rty → rty.impl ≠ some cx.inst)
    (hwf : ∀ st, s.inst? cx.inst = some st → FreeOK st.handles)
    (h₁ : SRun (σ := σ) (lowerBorrow lim cx rt rep) s i s₁) :
    ¬ SRun (σ := σ) (liftOwn lim' cx' rt' i) s₁ r s₂ := by
  intro h₂
  obtain ⟨x, hx, -, hown⟩ := srun_liftOwn h₂
  have hx' : x = borrowObj rt rep τ :=
    handleAt_unique (hj ▸ hx) (lowered_borrow_at hsc himpl hwf h₁)
  rw [hx'] at hown
  cases hown

/-! ## `lift_borrow` -/

/-- **After `lift_borrow`, the lent handle has `num_lends ≥ 1`.** -/
theorem lent_at {lim : Limits} {cx : LiftLowerContext E} {rt : RtId} {i : ℕ} {sb : SubtaskId}
    (hsc : cx.scope = .subtask sb) {s s₁ : CStore E} {r : ℕ}
    (h₁ : SRun (σ := σ) (liftBorrow lim cx rt i) s r s₁) {x : ResourceHandle}
    (hx : HandleAt s₁ cx.inst i x) : 1 ≤ x.numLends := by
  obtain ⟨st, hid, hst, hg, rfl⟩ := srun_liftBorrow hsc h₁
  obtain ⟨st', hid', hst', hg', hr⟩ := hx
  have hst'' : st' = st := Option.some.inj (hst'.symm.trans ((inst_addLender s sb hid _).trans hst))
  have hid'' : HandleEntry.resource hid' = .resource hid := by
    rw [hst''] at hg'; exact Option.some.inj (hg'.symm.trans hg)
  have hid₃ : hid' = hid := by cases hid''; rfl
  rw [hid₃, resHandles_addLender] at hr
  obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hr
  exact Nat.le_add_left 1 y.numLends

/-- **A lent handle cannot be transferred by its owner.** -/
theorem lent_not_given {lim lim' : Limits} {cx cx' : LiftLowerContext E} {rt rt' : RtId}
    {i : ℕ} {sb : SubtaskId} (hsc : cx.scope = .subtask sb) (hj : cx'.inst = cx.inst)
    {s s₁ s₂ : CStore E} {r r' : ℕ} (h₁ : SRun (σ := σ) (liftBorrow lim cx rt i) s r s₁) :
    ¬ SRun (σ := σ) (liftOwn lim' cx' rt' i) s₁ r' s₂ := by
  intro h₂
  obtain ⟨x, hx, hl, -⟩ := srun_liftOwn h₂
  have h1 : 1 ≤ x.numLends := lent_at hsc h₁ (hj ▸ hx)
  omega

/-- **A lent handle cannot be dropped by its owner.** -/
theorem lent_not_dropped {lim lim' : Limits} {cx : LiftLowerContext E} {rt rt' : RtId} {i : ℕ}
    {sb : SubtaskId} (hsc : cx.scope = .subtask sb) {s s₁ s₂ : CStore E} {r : ℕ}
    {o : Option (DtorRequest E)} (h₁ : SRun (σ := σ) (liftBorrow lim cx rt i) s r s₁) :
    ¬ SRun (σ := σ) (resourceDropCore lim' cx.inst rt' i) s₁ o s₂ := by
  intro h₂
  obtain ⟨x, hx, hl⟩ := srun_resourceDropCore h₂
  have h1 : 1 ≤ x.numLends := lent_at hsc h₁ hx
  omega

/-! ## `Task.return_` -/

theorem crun_getStore {s s' r : CStore E} :
    CRunP (getStore (σ := σ)) s r s' ↔ r = s ∧ s' = s := by
  unfold getStore perform
  exact Prog.eval_lift_iff

theorem not_crun_trap {r : TrapReason} {s s' : CStore E} {α : Type} {a : α} :
    ¬ CRunP (trap (σ := σ) r : P E σ α) s a s' := by
  intro h
  obtain ⟨_, _, hH, _⟩ := Prog.Eval.op_inv h
  exact hH

theorem crun_trapIf {c : Bool} {r : TrapReason} {s s' : CStore E} {u : Unit} :
    CRunP (trapIf (σ := σ) c r) s u s' → c = false ∧ s' = s := by
  cases c
  · intro h; exact ⟨rfl, (Prog.eval_pure_iff.1 h).2⟩
  · intro h; exact absurd h not_crun_trap

theorem crun_getObj {Id α : Type} (F : ArenaField E Id α) (i : Id) {s s' : CStore E} {x : α}
    (h : CRunP (getObj (σ := σ) F i) s x s') : F.get? s i = some x ∧ s' = s := by
  unfold getObj at h
  obtain ⟨s₀, s₁, h₁, k₁⟩ := Prog.eval_bind_iff.1 h
  obtain ⟨e₀, e₁⟩ := crun_getStore.1 h₁
  rw [e₀, e₁] at k₁
  cases hg : F.get? s i with
  | none => rw [hg] at k₁; exact absurd k₁ not_crun_trap
  | some y =>
    rw [hg] at k₁
    obtain ⟨hx, hs⟩ := Prog.eval_pure_iff.1 k₁
    exact ⟨hx ▸ rfl, hs⟩

/-- **An export call cannot end while it holds borrows.** -/
theorem crun_return {τ : TaskId} {vs : List Silmaril.Wasm.Component.Value.Val} {s s' : CStore E}
    {u : Unit} (h : CRunP (σ := σ) (Task.return_ τ vs) s u s') :
    ∃ tk, ArenaField.tasks.get? s τ = some tk ∧ tk.numBorrows = 0 := by
  unfold Task.return_ at h
  obtain ⟨tk, s₁, h₁, k₁⟩ := Prog.eval_bind_iff.1 h
  obtain ⟨htk, rfl⟩ := crun_getObj _ _ h₁
  obtain ⟨_, s₂, h₂, k₂⟩ := Prog.eval_bind_iff.1 k₁
  obtain ⟨-, rfl⟩ := crun_trapIf h₂
  obtain ⟨_, s₃, h₃, -⟩ := Prog.eval_bind_iff.1 k₂
  obtain ⟨hb, -⟩ := crun_trapIf h₃
  have hb' : tk.numBorrows = 0 := by simpa using hb
  exact ⟨tk, htk, hb'⟩

end Silmaril.Wasm.Component.FXRes.Borrow
