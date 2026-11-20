module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.Acc

/-!
# Accepting runs of the task methods of a synchronous lift

`Spec` rules (`Silmaril.Proofs.Wasm.Component.Reference.ListLift.Acc`) for the task methods a
synchronous `canon lift` runs on its implicit thread, generic in the engine and dispatcher:
`Task.enterImplicitThread`, `Task.start` (up to its `on_start` call), `Task.return_` (up to its
`on_resolve` call) and `Task.exitImplicitThread`.

They track what later steps read: the core store, the caller records, and for every task its
*key* (`tkey`: function type, options, instance and caller record, which no task method
changes) and its state (`tview`). Checks are not tracked: a failing check traps, and a trap has
no accepting continuation (`Spec.trap`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.AsyncRef (TaskState)

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-! ## Task keys -/

/-- The fields of a task that the task methods never change. -/
def tkey (tk : Task E) : WIT.FuncType Empty RtId × CanonOpts E × InstId × CallerId :=
  (tk.ft, tk.opts, tk.inst, tk.caller)

/-- The keys and states of the tasks. -/
def tview (s : CStore E) : List ((WIT.FuncType Empty RtId × CanonOpts E × InstId × CallerId) ×
    TaskState) :=
  s.tasks.map fun tk => (tkey tk, tk.state)

theorem map_modify_of {α β : Type} (g : α → β) (f : α → α) (hf : ∀ x, g (f x) = g x)
    (l : List α) (i : Nat) : (l.modify i f).map g = l.map g := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_modify]
  split
  · cases l[j]? <;> simp [hf]
  · simp

/-- The task view after modifying one task with a key- and state-preserving update. -/
theorem tview_modify (s : CStore E) (T : TaskId) (f : Task E → Task E)
    (hk : ∀ tk, tkey (f tk) = tkey tk) (hs : ∀ tk, (f tk).state = tk.state) :
    tview (ArenaField.tasks.modify s T f) = tview s := by
  unfold tview
  exact map_modify_of _ f (fun tk => by
    show (tkey (f tk), (f tk).state) = (tkey tk, tk.state)
    rw [hk, hs]) _ _

theorem tview_setImplicitThread (s : CStore E) (T : TaskId) (t : ThreadId) :
    tview (CStore.setImplicitThread T t s) = tview s :=
  tview_modify s T _ (fun _ => rfl) (fun _ => rfl)

theorem tview_registerThreadSt (s : CStore E) (T : TaskId) (t : ThreadId) :
    tview (CStore.registerThreadSt T t s) = tview s := by
  unfold CStore.registerThreadSt
  split
  · rfl
  · split
    · rfl
    · exact tview_modify s T _ (fun _ => rfl) (fun _ => rfl)

theorem tview_unregisterThreadSt (s : CStore E) (T : TaskId) (t : ThreadId) (i : Nat) :
    tview (CStore.unregisterThreadSt T t i s) = tview s := by
  unfold CStore.unregisterThreadSt
  split
  · rfl
  · exact tview_modify s T _ (fun _ => rfl) (fun _ => rfl)

theorem registerThreadSt_callers (s : CStore E) (T : TaskId) (t : ThreadId) :
    (CStore.registerThreadSt T t s).callers = s.callers := by
  unfold CStore.registerThreadSt
  split
  · rfl
  · split
    · rfl
    · rfl

theorem unregisterThreadSt_callers (s : CStore E) (T : TaskId) (t : ThreadId) (i : Nat) :
    (CStore.unregisterThreadSt T t i s).callers = s.callers := by
  unfold CStore.unregisterThreadSt
  split
  · rfl
  · rfl

theorem registerThreadSt_lockdown (s : CStore E) (T : TaskId) (t : ThreadId) :
    (CStore.registerThreadSt T t s).lockdown = s.lockdown := by
  unfold CStore.registerThreadSt
  split
  · rfl
  · split <;> rfl

theorem unregisterThreadSt_lockdown (s : CStore E) (T : TaskId) (t : ThreadId) (i : Nat) :
    (CStore.unregisterThreadSt T t i s).lockdown = s.lockdown := by
  unfold CStore.unregisterThreadSt
  split <;> rfl

/-- The key of a task read from the store is the key the view records. -/
theorem tkey_of_get {s : CStore E} {T : TaskId} {tk : Task E} {k : _} {st : TaskState}
    (hv : (tview s)[T.idx]? = some (k, st)) (hg : ArenaField.tasks.get? s T = some tk) :
    tkey tk = k ∧ tk.state = st := by
  have hg' : s.tasks[T.idx]? = some tk := hg
  simp only [tview, List.getElem?_map, hg', Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at hv
  exact hv

/-- The view after setting the state of task `T`. -/
theorem tview_setTaskState (s : CStore E) (T : TaskId) (st : TaskState) :
    tview (CStore.setTaskState T st s) = (tview s).modify T.idx (fun x => (x.1, st)) := by
  unfold tview CStore.setTaskState
  apply List.ext_getElem?
  intro j
  simp only [ArenaField.modify, ArenaField.tasks, Arena.modify, List.getElem?_map,
    List.getElem?_modify]
  split
  · cases s.tasks[j]? <;> rfl
  · simp

/-! ## Current thread -/

namespace Spec

variable {α : Type} {m : Config E σ}

theorem currentThreadId (t : ThreadId) :
    Spec prof hr dispatch (some t) (Canon.currentThreadId : P E σ ThreadId) m
      (fun t' m' => t' = t ∧ m' = m) := by
  unfold Canon.currentThreadId
  refine bind currentThread fun t' m' ⟨ht, hm⟩ _ _ => ?_
  subst ht m'
  exact pure t

theorem getTask (th : Option ThreadId) (T : TaskId) :
    Spec prof hr dispatch th (Canon.getTask T : P E σ (Task E)) m
      (fun tk m' => ArenaField.tasks.get? m.store T = some tk ∧ m' = m) :=
  getObj _ _

theorem ite_false {c : Bool} {p q : P E σ α} {th : Option ThreadId} {R : α → Config E σ → Prop}
    (hc : c = false) (h : Spec prof hr dispatch th q m R) :
    Spec prof hr dispatch th (if c = true then p else q) m R := by
  subst hc
  exact h

theorem ite_true {c : Bool} {p q : P E σ α} {th : Option ThreadId} {R : α → Config E σ → Prop}
    (hc : c = true) (h : Spec prof hr dispatch th p m R) :
    Spec prof hr dispatch th (if c = true then p else q) m R := by
  subst hc
  exact h

end Spec

/-! ## Task methods -/

/-- The frame of the task methods: core store and callers unchanged, task view `v`. -/
def TFrame (m m' : Config E σ)
    (v : List ((WIT.FuncType Empty RtId × CanonOpts E × InstId × CallerId) × TaskState)) :
    Prop :=
  m'.core = m.core ∧ m'.store.callers = m.store.callers ∧ tview m'.store = v

/-- `Task.registerThread`: one store update (or a trap). -/
theorem spec_registerThread (th : Option ThreadId) (T : TaskId) (t : ThreadId) {m : Config E σ} :
    Spec prof hr dispatch th (Task.registerThread T t) m
      (fun _ m' => m' = { m with store := CStore.registerThreadSt T t m.store }) := by
  unfold Task.registerThread
  refine Spec.bind (Spec.getTask _ _) fun tk m₁ ⟨_, hm⟩ _ _ => ?_
  subst m₁
  refine Spec.bind (Spec.getObj _ _) fun st m₂ ⟨_, hm⟩ _ _ => ?_
  subst m₂
  split
  · exact Spec.trap _ _
  · refine Spec.bind (Spec.modify _ (registerThreadSt_lockdown _ _ _)) fun _ m₃ hm _ _ => ?_
    subst m₃
    exact Spec.mono (Spec.pure _) fun _ m' ⟨_, hm⟩ _ _ => hm

/-- **`Task.enterImplicitThread`** of a synchronous task: it enters (or traps). -/
theorem spec_enterImplicitThread (q : Quirks) {t : ThreadId} {T : TaskId} {m : Config E σ}
    {k : _} {st : TaskState} (hv : (tview m.store)[T.idx]? = some (k, st))
    (ha : k.1.async_ = false) :
    Spec prof hr dispatch (some t) (Task.enterImplicitThread q T) m
      (fun b m' => b = true ∧ TFrame m m' (tview m.store)) := by
  unfold Task.enterImplicitThread
  refine Spec.bind (Spec.currentThreadId t) fun t' m₁ ⟨ht, hm⟩ _ _ => ?_
  subst t' m₁
  refine Spec.bind (Spec.modify _ rfl) fun _ m₂ hm _ _ => ?_
  subst m₂
  refine Spec.bind (Spec.getTask _ _) fun tk m₃ ⟨htk, hm⟩ _ _ => ?_
  subst m₃
  have hv' : (tview (CStore.setImplicitThread T t m.store))[T.idx]? = some (k, st) := by
    rw [tview_setImplicitThread]; exact hv
  obtain ⟨hk, -⟩ := tkey_of_get hv' htk
  have hft : tk.ft.async_ = false := by rw [← ha, ← hk]; rfl
  refine Spec.bind (Spec.ite_false hft (Spec.pure true)) fun b m₄ ⟨hb, hm⟩ _ _ => ?_
  subst b m₄
  refine Spec.ite_true rfl ?_
  refine Spec.bind (spec_registerThread _ _ _) fun i m₅ hm _ _ => ?_
  subst m₅
  refine Spec.mono (Spec.pure true) fun b m' ⟨hb, hm⟩ _ _ => ⟨hb, ?_⟩
  subst m'
  refine ⟨rfl, registerThreadSt_callers _ _ _, ?_⟩
  rw [tview_registerThreadSt, tview_setImplicitThread]

theorem setTaskState_lockdown (s : CStore E) (T : TaskId) (st : TaskState) :
    (CStore.setTaskState T st s).lockdown = s.lockdown := rfl

/-- **`Task.start`** of task `T` whose caller record answers `on_start` with `args` without
changing the configuration. -/
theorem spec_start {th : Option ThreadId} {T : TaskId} {m : Config E σ} {k : _} {st : TaskState}
    (hv : (tview m.store)[T.idx]? = some (k, st)) {args : List Value.Val}
    (hcall : Spec prof hr dispatch th (dispatch (.onStart k.2.2.2))
      { m with store := CStore.setTaskState T .started m.store }
      (fun r m' => r = .vals args ∧
        m' = { m with store := CStore.setTaskState T .started m.store })) :
    Spec prof hr dispatch th (Task.start T) m
      (fun vs m' => vs = args ∧
        m' = { m with store := CStore.setTaskState T .started m.store }) := by
  unfold Task.start
  refine Spec.bind (Spec.getTask _ _) fun tk m₁ ⟨htk, hm⟩ _ _ => ?_
  subst m₁
  obtain ⟨hk, -⟩ := tkey_of_get hv htk
  refine Spec.bind (Spec.modify _ rfl) fun _ m₂ hm _ _ => ?_
  subst m₂
  unfold callVals
  have hc : tk.caller = k.2.2.2 := by rw [← hk]; rfl
  rw [hc]
  refine Spec.bind (Spec.call hcall) fun r m₃ ⟨hr, hm⟩ _ _ => ?_
  subst r m₃
  exact Spec.pure _

/-- **`Task.return_`** of task `T` whose caller record's `on_resolve` of `vs` has a `Spec`
returning `Ret.unit`: afterwards the task is resolved. -/
theorem spec_return {th : Option ThreadId} {T : TaskId} {m : Config E σ} {k : _} {st : TaskState}
    (hv : (tview m.store)[T.idx]? = some (k, st)) {vs : List Value.Val}
    {R : Config E σ → Prop}
    (hcall : Spec prof hr dispatch th (dispatch (.onResolve k.2.2.2 (some vs))) m
      (fun r m' => r = .unit ∧ R m')) :
    Spec prof hr dispatch th (Task.return_ T vs) m
      (fun _ m' => ∃ m₁, R m₁ ∧
        m' = { m₁ with store := CStore.setTaskState T .resolved m₁.store }) := by
  unfold Task.return_
  refine Spec.bind (Spec.getTask _ _) fun tk m₁ ⟨htk, hm⟩ _ _ => ?_
  subst m₁
  obtain ⟨hk, -⟩ := tkey_of_get hv htk
  refine Spec.bind (Spec.trapIf _ _) fun _ m₂ ⟨_, hm⟩ _ _ => ?_
  subst m₂
  refine Spec.bind (Spec.trapIf _ _) fun _ m₃ ⟨_, hm⟩ _ _ => ?_
  subst m₃
  unfold callUnit
  have hc : tk.caller = k.2.2.2 := by rw [← hk]; rfl
  rw [hc]
  refine Spec.bind (R := fun _ m' => R m')
    (Spec.bind (Spec.call hcall) fun r m₄ ⟨hr, hR⟩ _ _ => ?_) fun _ m₅ hR' _ _ => ?_
  · subst r
    exact Spec.mono (Spec.pure ()) fun _ m' ⟨_, hm⟩ _ _ => hm ▸ hR
  · exact Spec.mono (Spec.modify _ rfl) fun _ m' hm _ _ => ⟨m₅, hR', hm⟩

/-- **`Task.exitImplicitThread`** of a synchronous task: unregisters its thread (or traps). -/
theorem spec_exitImplicitThread {th : Option ThreadId} {T : TaskId} {m : Config E σ} {k : _}
    {st : TaskState} (hv : (tview m.store)[T.idx]? = some (k, st))
    (ha : k.1.async_ = false) :
    Spec prof hr dispatch th (Task.exitImplicitThread T) m
      (fun _ m' => ∃ t i, m' = { m with store := CStore.unregisterThreadSt T t i m.store }) := by
  unfold Task.exitImplicitThread
  refine Spec.bind (Spec.getTask _ _) fun tk m₁ ⟨htk, hm⟩ _ _ => ?_
  subst m₁
  obtain ⟨hk, -⟩ := tkey_of_get hv htk
  have hft : tk.ft.async_ = false := by rw [← ha, ← hk]; rfl
  refine Spec.bind (Spec.orTrap _ _) fun t m₂ ⟨_, hm⟩ _ _ => ?_
  subst m₂
  refine Spec.bind
    (R := fun _ m' => ∃ i, m' = { m with store := CStore.unregisterThreadSt T t i m.store })
    (Spec.bind (Spec.getTask _ _) fun tk' m₃ ⟨_, hm⟩ _ _ => ?_) fun _ m₄ hR _ _ => ?_
  · subst m₃
    refine Spec.bind (Spec.trapIf _ _) fun _ m₄ ⟨_, hm⟩ _ _ => ?_
    subst m₄
    refine Spec.bind (Spec.getObj _ _) fun th' m₅ ⟨_, hm⟩ _ _ => ?_
    subst m₅
    refine Spec.bind (Spec.orTrap _ _) fun i m₆ ⟨_, hm⟩ _ _ => ?_
    subst m₆
    refine Spec.bind (Spec.getObj _ _) fun ist m₇ ⟨_, hm⟩ _ _ => ?_
    subst m₇
    split
    · exact Spec.trap _ _
    · exact Spec.mono (Spec.modify _ (unregisterThreadSt_lockdown _ _ _ _))
        fun _ m' hm _ _ => ⟨i, hm⟩
  · obtain ⟨i, hm⟩ := hR
    subst m₄
    simp only [hft, Bool.false_and]
    exact Spec.mono (Spec.pure ()) fun _ m' ⟨_, hm⟩ _ _ => ⟨t, i, hm⟩

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
