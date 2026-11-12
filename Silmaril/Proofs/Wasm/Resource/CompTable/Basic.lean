module

public import Silmaril.Wasm.Resource.CompTable.Defs
public import Silmaril.Wasm.Resource.Table.Thms
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# The resource built-ins of the reference machine and their handle tables: proofs

* `srun_getStore`, `srun_modifyStore`, `not_srun_trap`, `srun_getObj`, ...: the store-only
  semantics of the primitive operations; `srun_handlesAdd`, `srun_handlesGet`,
  `srun_handlesRemove`: the table accesses of `Canon` are `Table.add?`, `get?`, `remove?` on the
  instance's table.
* `resourceNewCore_tab`, `resourceRepCore_tab`, `resourceDropCore_tab`: a successful run of a
  core is one table event on its instance (`added i (resource hid)`, `got i (resource hid)`,
  `removed i (resource hid)`) and leaves the other instances' tables unchanged.
* `resScript_tab`, `resScript_run`, `resScript_accepts`: a successful run of a script of core
  calls is, on each instance, a successful table history whose handle events are the calls'
  `hev`s; from an empty table they are accepted by `handleProto ℕ r` in both orientations.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type} {α β : Type}

/-! ## The store-only semantics of the primitives -/

theorem srun_pure {a b : α} {s s' : CStore E} :
    SRun (σ := σ) (Pure.pure a) s b s' ↔ b = a ∧ s' = s :=
  Prog.eval_pure_iff
theorem srun_bind {p : P E σ α} {f : α → P E σ β} {s s' : CStore E} {b : β} :
    SRun (p >>= f) s b s' ↔ ∃ a s₁, SRun p s a s₁ ∧ SRun (f a) s₁ b s' :=
  Prog.eval_bind_iff
theorem srun_getStore {s s' r : CStore E} :
    SRun (getStore (σ := σ)) s r s' ↔ r = s ∧ s' = s := by
  unfold getStore perform
  exact Prog.eval_lift_iff
theorem srun_modifyStore {f : CStore E → CStore E} {s s' : CStore E} {u : Unit} :
    SRun (modifyStore (σ := σ) f) s u s' ↔ s' = f s := by
  unfold modifyStore perform
  exact Prog.eval_lift_iff
theorem not_srun_trap {r : TrapReason} {s s' : CStore E} {a : α} :
    ¬ SRun (trap (σ := σ) r : P E σ α) s a s' := by
  intro h
  obtain ⟨_, _, hH, _⟩ := Prog.Eval.op_inv h
  exact hH
theorem srun_trap_iff {r : TrapReason} {s s' : CStore E} {a : α} :
    SRun (trap (σ := σ) r : P E σ α) s a s' ↔ False := iff_false_intro not_srun_trap
theorem srun_internal_iff {msg : String} {s s' : CStore E} {a : α} :
    SRun (internal (σ := σ) msg : P E σ α) s a s' ↔ False := iff_false_intro not_srun_trap
theorem srun_trapIf {c : Bool} {r : TrapReason} {s s' : CStore E} {u : Unit} :
    SRun (trapIf (σ := σ) c r) s u s' ↔ c = false ∧ s' = s := by
  cases c
  · simp [trapIf, eq_comm]
  · simp [trapIf, srun_trap_iff]
theorem srun_getObj {Id : Type} (F : ArenaField E Id α) (i : Id) {s s' : CStore E} {x : α} :
    SRun (getObj (σ := σ) F i) s x s' ↔ F.get? s i = some x ∧ s' = s := by
  unfold getObj
  simp only [srun_bind, srun_getStore]
  cases h : F.get? s i <;> simp [h, srun_internal_iff, eq_comm]
theorem srun_allocObj {Id : Type} (F : ArenaField E Id α) (x : α) {s s' : CStore E} {i : Id} :
    SRun (allocObj (σ := σ) F x) s i s' ↔ i = F.mkId (F.size s) ∧ s' = ArenaOps.allocSt F x s := by
  unfold allocObj
  simp only [srun_bind, srun_getStore, srun_modifyStore, srun_pure]
  simp
theorem srun_handlesAdd {inst : InstId} {e : HandleEntry} {s s' : CStore E} {i : ℕ} :
    SRun (handlesAdd (σ := σ) inst e) s i s' ↔ ∃ st st', s.inst? inst = some st ∧
      st.addHandle? e = some (i, st') ∧
      s' = ArenaField.insts.modify s inst (InstState.addHandle e) := by
  unfold handlesAdd getInst modifyInst modifyObj
  simp only [srun_bind, srun_getObj]
  constructor
  · rintro ⟨st, _, ⟨hst, rfl⟩, h⟩
    cases ha : st.addHandle? e with
    | none => rw [ha] at h; exact absurd h not_srun_trap
    | some p =>
      obtain ⟨j, st'⟩ := p
      rw [ha] at h
      simp only [srun_bind, srun_modifyStore, srun_pure] at h
      obtain ⟨_, _, rfl, rfl, rfl⟩ := h
      exact ⟨st, st', hst, ha, rfl⟩
  · rintro ⟨st, st', hst, ha, rfl⟩
    refine ⟨st, s, ⟨hst, rfl⟩, ?_⟩
    rw [ha]
    exact srun_bind.2 ⟨(), _, srun_modifyStore.2 rfl, srun_pure.2 ⟨rfl, rfl⟩⟩

theorem srun_handlesGet {inst : InstId} {i : ℕ} {s s' : CStore E} {e : HandleEntry} :
    SRun (handlesGet (σ := σ) inst i) s e s' ↔
      (∃ st, s.inst? inst = some st ∧ st.handles.get? i = some e) ∧ s' = s := by
  unfold handlesGet getInst
  simp only [srun_bind, srun_getObj]
  constructor
  · rintro ⟨st, _, ⟨hst, rfl⟩, h⟩
    cases hg : st.handles.get? i with
    | none => rw [hg] at h; exact absurd h not_srun_trap
    | some e' =>
      rw [hg] at h
      obtain ⟨rfl, rfl⟩ := srun_pure.1 h
      exact ⟨⟨st, hst, hg⟩, rfl⟩
  · rintro ⟨⟨st, hst, hg⟩, rfl⟩
    refine ⟨st, _, ⟨hst, rfl⟩, ?_⟩
    rw [hg]
    exact srun_pure.2 ⟨rfl, rfl⟩

theorem srun_handlesRemove {inst : InstId} {i : ℕ} {s s' : CStore E} {e : HandleEntry} :
    SRun (handlesRemove (σ := σ) inst i) s e s' ↔ ∃ st st', s.inst? inst = some st ∧
      st.removeHandle? i = some (e, st') ∧
      s' = ArenaField.insts.modify s inst (InstState.removeHandle i) := by
  unfold handlesRemove getInst modifyInst modifyObj
  simp only [srun_bind, srun_getObj]
  constructor
  · rintro ⟨st, _, ⟨hst, rfl⟩, h⟩
    cases ha : st.removeHandle? i with
    | none => rw [ha] at h; exact absurd h not_srun_trap
    | some p =>
      obtain ⟨e', st'⟩ := p
      rw [ha] at h
      simp only [srun_bind, srun_modifyStore, srun_pure] at h
      obtain ⟨_, _, rfl, rfl, rfl⟩ := h
      exact ⟨st, st', hst, ha, rfl⟩
  · rintro ⟨st, st', hst, ha, rfl⟩
    refine ⟨st, s, ⟨hst, rfl⟩, ?_⟩
    rw [ha]
    exact srun_bind.2 ⟨(), _, srun_modifyStore.2 rfl, srun_pure.2 ⟨rfl, rfl⟩⟩

/-! ## Handle tables of the store -/

theorem handles?_modify_self (s : CStore E) (inst : InstId) (f : InstState → InstState) :
    handles? (ArenaField.insts.modify s inst f) inst = (s.inst? inst).map fun st => (f st).handles := by
  simp only [handles?, CStore.inst?, ArenaField.get?_modify_self, Option.map_map]
  rfl

theorem handles?_modify_ne (s : CStore E) {inst j : InstId} (f : InstState → InstState)
    (h : j ≠ inst) : handles? (ArenaField.insts.modify s inst f) j = handles? s j := by
  simp [handles?, CStore.inst?, ArenaField.get?_modify_ne _ _ _ (Ne.symm h)]

theorem addHandle?_tab {e : HandleEntry} {st st' : InstState} {i : ℕ}
    (h : st.addHandle? e = some (i, st')) :
    st.handles.add? e = some (i, st'.handles) ∧ st.addHandle e = st' := by
  refine ⟨?_, InstState.addHandle_eq h⟩
  obtain ⟨⟨j, t⟩, hp, he⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hp

theorem removeHandle?_tab {i : ℕ} {st st' : InstState} {e : HandleEntry}
    (h : st.removeHandle? i = some (e, st')) :
    st.handles.remove? i = some (e, st'.handles) ∧ st.removeHandle i = st' := by
  refine ⟨?_, InstState.removeHandle_eq h⟩
  obtain ⟨⟨e', t⟩, hp, he⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hp

/-- The table history of one table event, from the step function. -/
theorem steps_single {t t' : Silmaril.Wasm.Component.Runtime.Table HandleEntry} {ev : Table.Event HandleEntry}
    (h : t.step? ev.op = some (ev, t')) : Table.Steps t [ev] t' :=
  .cons h (.nil _)

theorem handlesAdd_tab {inst : InstId} {e : HandleEntry} {s s' : CStore E} {i : ℕ}
    (h : SRun (handlesAdd (σ := σ) inst e) s i s') :
    TabSteps s s' inst [.added i e] ∧ ∀ j, j ≠ inst → handles? s' j = handles? s j := by
  obtain ⟨st, st', hst, ha, rfl⟩ := srun_handlesAdd.1 h
  obtain ⟨hadd, hst'⟩ := addHandle?_tab ha
  refine ⟨fun t ht => ⟨st'.handles, ?_, steps_single ?_⟩, fun j hj => handles?_modify_ne _ _ hj⟩
  · rw [handles?_modify_self, hst, Option.map_some, hst']
  · have ht' : st.handles = t := by simpa [handles?, hst] using ht
    subst ht'
    simp [Table.Event.op, Table.step?, hadd]

theorem handlesGet_tab {inst : InstId} {i : ℕ} {s s' : CStore E} {e : HandleEntry}
    (h : SRun (handlesGet (σ := σ) inst i) s e s') :
    TabSteps s s' inst [.got i e] ∧ s' = s := by
  obtain ⟨⟨st, hst, hg⟩, rfl⟩ := srun_handlesGet.1 h
  refine ⟨fun t ht => ⟨t, ht, steps_single ?_⟩, rfl⟩
  have ht' : st.handles = t := by simpa [handles?, hst] using ht
  subst ht'
  simp [Table.Event.op, Table.step?, hg]

theorem handlesRemove_tab {inst : InstId} {i : ℕ} {s s' : CStore E} {e : HandleEntry}
    (h : SRun (handlesRemove (σ := σ) inst i) s e s') :
    TabSteps s s' inst [.removed i e] ∧ ∀ j, j ≠ inst → handles? s' j = handles? s j := by
  obtain ⟨st, st', hst, ha, rfl⟩ := srun_handlesRemove.1 h
  obtain ⟨hrem, hst'⟩ := removeHandle?_tab ha
  refine ⟨fun t ht => ⟨st'.handles, ?_, steps_single ?_⟩, fun j hj => handles?_modify_ne _ _ hj⟩
  · rw [handles?_modify_self, hst, Option.map_some, hst']
  · have ht' : st.handles = t := by simpa [handles?, hst] using ht
    subst ht'
    simp [Table.Event.op, Table.step?, hrem]

theorem TabSteps.of_left {s₀ s s' : CStore E} {j : InstId} {evs : List (Table.Event HandleEntry)}
    (he : handles? s₀ j = handles? s j) (h : TabSteps s s' j evs) : TabSteps s₀ s' j evs :=
  fun t ht => h t (he ▸ ht)

theorem TabSteps.of_right {s s' s₂ : CStore E} {j : InstId} {evs : List (Table.Event HandleEntry)}
    (h : TabSteps s s' j evs) (he : handles? s₂ j = handles? s' j) : TabSteps s s₂ j evs :=
  fun t ht => (h t ht).imp fun _ h' => ⟨he.trans h'.1, h'.2⟩

theorem handles?_resHandles_alloc (s : CStore E) (x : ResourceHandle) (j : InstId) :
    handles? (ArenaOps.allocSt ArenaField.resHandles x s) j = handles? s j := rfl

theorem handles?_tasks_modify (s : CStore E) (t : TaskId) (f : Task E → Task E) (j : InstId) :
    handles? (ArenaField.tasks.modify s t f) j = handles? s j := rfl

theorem srun_expectResource {e : HandleEntry} {s s' : CStore E} {hid : HandleObjId} :
    SRun (expectResource (σ := σ) e) s hid s' ↔ e = .resource hid ∧ s' = s := by
  cases e <;> simp [expectResource, srun_trap_iff, eq_comm]

/-- **`resource.new` adds one entry**: a successful run of `resourceNewCore` returning `i` is the
table event `added i (resource hid)` on `inst`, for the fresh handle object `hid` holding
`ResourceHandle(rt, rep, own)`; the other instances' tables are unchanged. -/
theorem resourceNewCore_tab {lim : Silmaril.Wasm.Component.Limits} {inst : InstId} {rt : RtId} {rep : ℕ}
    {s s' : CStore E} {i : ℕ} (h : SRun (resourceNewCore (σ := σ) lim inst rt rep) s i s') :
    ∃ hid, ArenaField.resHandles.get? s' hid = some { rt := rt, rep := rep, own := true } ∧
      TabSteps s s' inst [.added i (.resource hid)] ∧
      ∀ j, j ≠ inst → handles? s' j = handles? s j := by
  unfold resourceNewCore addResHandle at h
  obtain ⟨hid, s₁, h₁, h₂⟩ := srun_bind.1 h
  obtain ⟨rfl, rfl⟩ := srun_allocObj _ _ |>.1 h₁
  obtain ⟨hT, hF⟩ := handlesAdd_tab h₂
  obtain ⟨st, st', -, -, rfl⟩ := srun_handlesAdd.1 h₂
  exact ⟨_, ArenaField.get?_alloc_self (E := E) ArenaField.resHandles s _, hT, hF⟩

/-- **`resource.rep` reads one entry**: a successful run of `resourceRepCore` returning `n` is the
table event `got i (resource hid)` on `inst`, the store is unchanged, and `n` is the
representation of the handle object `hid`, of resource type `rt`. -/
theorem resourceRepCore_tab {lim : Silmaril.Wasm.Component.Limits} {inst : InstId} {rt : RtId} {i : ℕ}
    {s s' : CStore E} {n : ℕ} (h : SRun (resourceRepCore (σ := σ) lim inst rt i) s n s') :
    ∃ hid rh, ArenaField.resHandles.get? s hid = some rh ∧ rh.rt = rt ∧ rh.rep = n ∧
      TabSteps s s inst [.got i (.resource hid)] ∧ s' = s := by
  unfold resourceRepCore at h
  obtain ⟨e, s₁, h₁, h₂⟩ := srun_bind.1 h
  obtain ⟨hT, rfl⟩ := handlesGet_tab h₁
  obtain ⟨hid, s₂, h₃, h₄⟩ := srun_bind.1 h₂
  obtain ⟨rfl, rfl⟩ := srun_expectResource.1 h₃
  obtain ⟨rh, s₃, h₅, h₆⟩ := srun_bind.1 h₄
  obtain ⟨hrh, rfl⟩ := (srun_getObj _ _).1 h₅
  obtain ⟨u, s₄, h₇, h₈⟩ := srun_bind.1 h₆
  obtain ⟨hrt, rfl⟩ := srun_trapIf.1 h₇
  obtain ⟨rfl, rfl⟩ := srun_pure.1 h₈
  exact ⟨hid, rh, hrh, by simpa using hrt, rfl, hT, rfl⟩

theorem dropHandleTail_handles {rt : RtId} {rh : ResourceHandle} {s s' : CStore E}
    {r : Option (DtorRequest E)} (h : SRun (dropHandleTail (σ := σ) rt rh) s r s') (j : InstId) :
    handles? s' j = handles? s j := by
  unfold dropHandleTail at h
  cases ho : rh.own
  · rw [ho] at h
    cases hs : rh.scope with
    | none => rw [hs] at h; exact absurd h not_srun_trap
    | some task =>
      rw [hs] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨u, s₁, h₁, h₂⟩ := srun_bind.1 h
      obtain ⟨rfl, rfl⟩ := srun_pure.1 h₂
      rw [srun_modifyStore.1 h₁]
      rfl
  · rw [ho] at h
    simp only [↓reduceIte] at h
    obtain ⟨rty, s₁, h₁, h₂⟩ := srun_bind.1 h
    obtain ⟨-, rfl⟩ := (srun_getObj _ _).1 h₁
    obtain ⟨rfl, rfl⟩ := srun_pure.1 h₂
    rfl

/-- **`resource.drop` removes one entry**: a successful run of `resourceDropCore` (up to the
destructor call) is the table event `removed i (resource hid)` on `inst`, where `hid` is a
handle object of resource type `rt` with no outstanding lends; the other instances' tables
are unchanged. -/
theorem resourceDropCore_tab {lim : Silmaril.Wasm.Component.Limits} {inst : InstId} {rt : RtId} {i : ℕ}
    {s s' : CStore E} {r : Option (DtorRequest E)}
    (h : SRun (resourceDropCore (σ := σ) lim inst rt i) s r s') :
    ∃ hid rh, ArenaField.resHandles.get? s hid = some rh ∧ rh.rt = rt ∧ rh.numLends = 0 ∧
      TabSteps s s' inst [.removed i (.resource hid)] ∧
      ∀ j, j ≠ inst → handles? s' j = handles? s j := by
  unfold resourceDropCore at h
  obtain ⟨e, s₁, h₁, h₂⟩ := srun_bind.1 h
  obtain ⟨hT, hF⟩ := handlesRemove_tab h₁
  obtain ⟨st, st', -, -, rfl⟩ := srun_handlesRemove.1 h₁
  obtain ⟨hid, s₂, h₃, h₄⟩ := srun_bind.1 h₂
  obtain ⟨rfl, rfl⟩ := srun_expectResource.1 h₃
  obtain ⟨rh, s₃, h₅, h₆⟩ := srun_bind.1 h₄
  obtain ⟨hrh, rfl⟩ := (srun_getObj _ _).1 h₅
  obtain ⟨u, s₄, h₇, h₈⟩ := srun_bind.1 h₆
  obtain ⟨hrt, rfl⟩ := srun_trapIf.1 h₇
  obtain ⟨u', s₅, h₉, h₁₀⟩ := srun_bind.1 h₈
  obtain ⟨hl, rfl⟩ := srun_trapIf.1 h₉
  have hD := dropHandleTail_handles h₁₀
  refine ⟨hid, rh, hrh, by simpa using hrt, by simpa using hl, TabSteps.of_right hT (hD inst),
    fun j hj => (hD j).trans (hF j hj)⟩

/-! ## Scripts of built-in calls -/

theorem steps_append {α : Type} {t₁ t₂ t₃ : Silmaril.Wasm.Component.Runtime.Table α} {e₁ e₂ : List (Table.Event α)}
    (h₁ : Table.Steps t₁ e₁ t₂) (h₂ : Table.Steps t₂ e₂ t₃) : Table.Steps t₁ (e₁ ++ e₂) t₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

theorem TabSteps.trans {s₁ s₂ s₃ : CStore E} {j : InstId} {e₁ e₂ : List (Table.Event HandleEntry)}
    (h₁ : TabSteps s₁ s₂ j e₁) (h₂ : TabSteps s₂ s₃ j e₂) : TabSteps s₁ s₃ j (e₁ ++ e₂) := by
  intro t ht
  obtain ⟨t₂, ht₂, hs₁⟩ := h₁ t ht
  obtain ⟨t₃, ht₃, hs₂⟩ := h₂ t₂ ht₂
  exact ⟨t₃, ht₃, steps_append hs₁ hs₂⟩

theorem TabSteps.of_eq {s s' : CStore E} {j : InstId} (h : handles? s' j = handles? s j) :
    TabSteps s s' j [] :=
  fun t ht => ⟨t, h.trans ht, .nil t⟩

/-- One call of a built-in core is one table event on its instance, read as its `hev`. -/
theorem ResCall.prog_tab {lim : Silmaril.Wasm.Component.Limits} {c : ResCall} {s s' : CStore E} {n : ℕ}
    (h : SRun (σ := σ) (c.prog lim) s n s') :
    ∃ ev, TabSteps s s' c.inst [ev] ∧ tableEv ev = c.hev n ∧
      ∀ j, j ≠ c.inst → handles? s' j = handles? s j := by
  cases c with
  | new inst rt v =>
    obtain ⟨hid, -, hT, hF⟩ := resourceNewCore_tab (lim := lim) h
    exact ⟨_, hT, rfl, hF⟩
  | rep inst rt i =>
    obtain ⟨hid, -, -, -, -, hT, rfl⟩ := resourceRepCore_tab (lim := lim) h
    exact ⟨_, hT, rfl, fun _ _ => rfl⟩
  | drop inst rt i =>
    obtain ⟨r, s₁, h₁, h₂⟩ := srun_bind.1 h
    obtain ⟨rfl, rfl⟩ := srun_pure.1 h₂
    obtain ⟨hid, -, -, -, -, hT, hF⟩ := resourceDropCore_tab h₁
    exact ⟨_, hT, rfl, hF⟩

theorem instEvs_cons (j : InstId) (c : ResCall) (cs : List ResCall) (n : ℕ) (ns : List ℕ) :
    instEvs j (c :: cs) (n :: ns) =
      if c.inst = j then c.hev n :: instEvs j cs ns else instEvs j cs ns := by
  by_cases hc : c.inst = j <;> simp [instEvs, hc]

/-- **A script of built-in calls is a table history on every instance**: for each instance `j`,
the table of `j` evolves through a successful history whose handle events are the `hev`s of the
calls on `j`. -/
theorem resScript_tab {lim : Silmaril.Wasm.Component.Limits} {cs : List ResCall} {s s' : CStore E} {ns : List ℕ}
    (h : SRun (σ := σ) (resScript lim cs) s ns s') (j : InstId) :
    ∃ evs, TabSteps s s' j evs ∧ evs.map tableEv = instEvs j cs ns := by
  induction cs generalizing s ns with
  | nil =>
    obtain ⟨rfl, rfl⟩ := srun_pure.1 h
    exact ⟨[], TabSteps.of_eq rfl, rfl⟩
  | cons c cs ih =>
    obtain ⟨n, s₁, h₁, h₂⟩ := srun_bind.1 h
    obtain ⟨ns', s₂, h₃, h₄⟩ := srun_bind.1 h₂
    obtain ⟨rfl, rfl⟩ := srun_pure.1 h₄
    obtain ⟨evs, hT, hE⟩ := ih h₃
    obtain ⟨ev, hT₁, hE₁, hF₁⟩ := ResCall.prog_tab h₁
    rw [instEvs_cons]
    by_cases hc : c.inst = j
    · subst hc
      refine ⟨ev :: evs, TabSteps.trans hT₁ hT, ?_⟩
      simp [hE₁, hE]
    · refine ⟨evs, TabSteps.trans (TabSteps.of_eq (hF₁ j (Ne.symm hc))) hT, ?_⟩
      simp [hc, hE]

/-- **The built-ins respect the handle protocol, from any related table state.** -/
theorem resScript_run {lim : Silmaril.Wasm.Component.Limits} {cs : List ResCall} {s s' : CStore E} {ns : List ℕ}
    (h : SRun (σ := σ) (resScript lim cs) s ns s') {j : InstId} {t : Silmaril.Wasm.Component.Runtime.Table HandleEntry}
    (ht : handles? s j = some t) (hf : FreeOK t) {L : List ℕ} (hL : TabRel L t) (r : Role) :
    ∃ L', (handleProto ℕ r).run (some L) (instEvs j cs ns) = some (some L') := by
  obtain ⟨evs, hT, hE⟩ := resScript_tab h j
  obtain ⟨t', -, hs⟩ := hT t ht
  obtain ⟨L', hL', -⟩ := table_steps_run hs r hf hL
  exact ⟨L', hE ▸ hL'⟩

/-- **The reference machine's resource built-ins respect the handle protocol**: for every
successful run of a script of `resource.new`/`rep`/`drop` cores, the handle events of the calls
on an instance whose table was empty are accepted by `handleProto ℕ r`, in both orientations:
`resource.new` returns a fresh index, `rep` and `drop` only touch live indices. -/
theorem resScript_accepts {lim : Silmaril.Wasm.Component.Limits} {cs : List ResCall} {s s' : CStore E} {ns : List ℕ}
    (h : SRun (σ := σ) (resScript lim cs) s ns s') {j : InstId}
    (hj : handles? s j = some Table.empty) (r : Role) :
    (handleProto ℕ r).Accepts (instEvs j cs ns) := by
  obtain ⟨evs, hT, hE⟩ := resScript_tab h j
  obtain ⟨t', -, hs⟩ := hT _ hj
  rw [← hE]
  exact table_steps_accepts hs r

end Silmaril.Wasm.Resource
