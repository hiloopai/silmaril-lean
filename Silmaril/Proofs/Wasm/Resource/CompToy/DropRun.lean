module

public import Silmaril.Proofs.Wasm.Resource.CompToy.MakeCall
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# The toy resource component: the destructor run of `resource.drop`

Dropping an own handle of the toy's resource (`impl = some 0`, no destructor) runs REF's no-op
destructor (`destructorCall` → `canonLiftNoop`): a new task and thread of instance `0`,
`Thread.resume`, the thread body `liftNoopThreadBody` (`enter_implicit_thread`, `Task.start` and
`Task.return_` through the `Caller.sub (.destructor rep)` record, the lowering of the `u32`
argument and the lift of no results, `exit_implicit_thread`), then the synchronous loop.

* `runs_enterN`, `runs_startD`, `runs_returnD`, `runs_lowerDtor`, `runs_liftDtor`,
  `runs_handlesRemove`, `runs_dropCore`: the pieces as big-step runs;
* `RunsQ.chunk3`, `RunsQ.chunk4`: `RunsQ.chunk` under more continuations;
* **`lrun_dropCallout`**: the live run of the whole callout program to its result `[]`, with
  one more task, thread and caller record (`dStore`) and the destructor's slot of the
  instance's thread table freed again.

New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs

variable {P : Silmaril.Wasm.Numerics.Profile}

/-- `enter_implicit_thread` of a synchronous task of instance `0` (last in the task arena),
registered at any slot `n` of the instance's thread table. -/
theorem runs_enterN {m : Machine.Config (E3 P) Unit} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {t : ThreadId} {ι ι' : InstState} {n : ℕ}
    (htasks : m.store.tasks = Gt ++ [y]) (hasync : y.ft.async_ = false) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hadd : ι.addThread? t = some (n, ι')) :
    RunsQ (D P) (some t) (Task.enterImplicitThread Quirks.none ⟨Gt.length⟩) m
      [.tau, .tau, .tau, .tau, .tau, .tau] true
      { m with store := (CStore.registerThreadSt ⟨Gt.length⟩ t
        (CStore.setImplicitThread ⟨Gt.length⟩ t m.store)) } := by
  have h₁ : (CStore.setImplicitThread ⟨Gt.length⟩ t m.store).tasks =
      Gt ++ [{ y with implicitThread := some t }] := tasks_modify_last htasks _
  have hi : ArenaField.insts.get? (CStore.setImplicitThread ⟨Gt.length⟩ t m.store) y.inst =
      some ι := by
    rw [hinst]
    exact insts_get_zero hinsts
  unfold Task.enterImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_currentThreadId m)
  apply RunsQ.bind (runs_modifyStore _ m rfl)
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last h₁))
  apply RunsQ.bind (runs_ite_pure hasync _ true _)
  show RunsQ _ _ (Task.registerThread ⟨Gt.length⟩ t >>= fun _ => pure true) _ _ _ _
  apply RunsQ.bind (f := fun _ => pure true) (a := n) ?_ (.pure _ _)
  rotate_left
  unfold Task.registerThread
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last h₁))
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ (by exact hi))
  rw [hadd]
  exact RunsQ.bind (runs_modifyStore _ _
    (CStore.registerThreadSt_frame (E := E3 P) _ _ _).2.2.2.2.2.2.1) (.pure _ _)
  rfl

/-- The value of `rep` passed to a destructor by `on_start` in store `S` (caller record `c`). -/
def dtorArg (S : CStore (E3 P)) (c : CallerId) (rep : ℕ) : Silmaril.Wasm.Component.Reference.Val :=
  repVal (((callerTaskFt? S c).map paramTypes).getD []) rep

/-- `Task.start` of a task whose caller record is the destructor record of `rep`. -/
theorem runs_startD {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gc : List (Caller (E3 P))}
    {rep : ℕ} (ht : m.store.tasks = Gt ++ [y]) (hy : y.caller = ⟨Gc.length⟩)
    (hc : m.store.callers = Gc ++ [.sub (.destructor rep)]) :
    RunsQ (D P) th (Task.start ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .tau, .tau, .tau]
      [dtorArg (CStore.setTaskState ⟨Gt.length⟩ .started m.store) ⟨Gc.length⟩ rep]
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } := by
  let S := CStore.setTaskState ⟨Gt.length⟩ .started m.store
  have hc' : ArenaField.callers.get? S ⟨Gc.length⟩ = some (.sub (.destructor rep)) :=
    callers_get_last (s := S) hc
  unfold Task.start
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_modifyStore _ _ rfl)
  rw [hy]
  unfold callVals callRet perform Prog.lift
  refine RunsQ.call (r := .vals [dtorArg S ⟨Gc.length⟩ rep]) (tr₁ := [.tau, .tau, .tau]) ?_
    (.pure _ _)
  show RunsQ _ _ (callerOnStart Limits.spec Quirks.none ⟨Gc.length⟩) _ _ _ _
  unfold callerOnStart
  refine RunsQ.getObj_bind _ _ hc' ?_
  show RunsQ _ _ (onStartProg ⟨Gc.length⟩) _ _ _ _
  unfold onStartProg
  exact RunsQ.getObj_bind _ _ hc' (RunsQ.get (.pure _ _))

theorem dtorArg_int (S : CStore (E3 P)) (c : CallerId) (rep : ℕ) :
    ∃ k : Value.IntKind, dtorArg S c rep = .int k rep := by
  unfold dtorArg repVal
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- `Task.return_` of a task whose caller record is a destructor record. -/
theorem runs_returnD {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gc : List (Caller (E3 P))}
    {rep : ℕ} (vs : List Silmaril.Wasm.Component.Reference.Val) (ht : m.store.tasks = Gt ++ [y]) (hy : y.caller = ⟨Gc.length⟩)
    (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : m.store.callers = Gc ++ [.sub (.destructor rep)]) :
    RunsQ (D P) th (Task.return_ ⟨Gt.length⟩ vs) m [.tau, .tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .resolved m.store } := by
  have hc' : ArenaField.callers.get? m.store ⟨Gc.length⟩ = some (.sub (.destructor rep)) :=
    callers_get_last hc
  unfold Task.return_
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hb]; rfl) _ _)
  rw [hy]
  unfold callUnit callRet perform Prog.lift
  refine RunsQ.bind (RunsQ.call (r := .unit) (tr₁ := [.tau, .tau]) ?_ (.pure _ _)) (runs_modifyStore _ _ rfl)
  show RunsQ _ _ (callerOnResolve Limits.spec Quirks.none ⟨Gc.length⟩ (some vs)) _ _ _ _
  unfold callerOnResolve
  refine RunsQ.getObj_bind _ _ hc' ?_
  show RunsQ _ _ (onResolveProg ⟨Gc.length⟩ (some vs)) _ _ _ _
  unfold onResolveProg
  exact RunsQ.getObj_bind _ _ hc' (.pure _ _)

/-- The lowering of an integer at the destructor's parameter type. -/
theorem runs_lowerDtor {th : Option ThreadId} (cx : LiftLowerContext (E3 P)) (v : Silmaril.Wasm.Component.Reference.Val)
    (k : Value.IntKind) (n : ℤ) (hv : v = .int k n) (m : Machine.Config (E3 P) Unit) :
    RunsQ (D P) th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
      [v] (paramTypes (dtorType .i32)) none) m [.tau] ([lowerFlatInt .u32 n] ++ []) m := by
  subst hv
  have e : (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams [.int k n]
      (paramTypes (dtorType .i32)) none : Canon.P (E3 P) Unit _) =
      ptrType cx >>= fun p => lowerFlatTypes Limits.spec Quirks.none cx p [.int k n]
        [.prim .u32] := by
    unfold lowerFlatValues
    congr 1
    funext p
    cases p <;> (rw [ite_eq_right_iff.mpr (by intro h; exact absurd h (by decide +kernel))]; rfl)
  rw [e]
  apply RunsQ.get
  show RunsQ _ _ (lowerFlatTypes Limits.spec Quirks.none cx (ptrTypeIn m.store cx) [.int k n]
    [.prim .u32]) _ _ _ _
  unfold lowerFlatTypes
  rw [lowerFlatAt.eq_def]
  exact RunsQ.bind (.pure _ _) (RunsQ.bind (.pure _ _) (.pure _ _))

/-- The lift of no flat values at the destructor's result type. -/
theorem runs_liftDtor {th : Option ThreadId} (cx : LiftLowerContext (E3 P))
    (m : Machine.Config (E3 P) Unit) :
    RunsQ (D P) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList []) (resultTypes (dtorType .i32))) m [.tau] ([], .ofList []) m := by
  have e : (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList [])
      (resultTypes (dtorType .i32)) : Canon.P (E3 P) Unit _) =
      ptrType cx >>= fun p => liftFlatTypes Limits.spec Quirks.none cx p [] (.ofList []) := by
    unfold liftFlatValues
    congr 1
    funext p
    cases p <;> (rw [ite_eq_right_iff.mpr (by intro h; exact absurd h (by decide +kernel))]; rfl)
  rw [e]
  apply RunsQ.get
  show RunsQ _ _ (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn m.store cx) [] (.ofList []))
    _ _ _ _
  unfold liftFlatTypes
  exact .pure _ _

namespace RunsQ

variable {d : Call (E3 P) → Canon.P (E3 P) Unit (Ret (E3 P))} {prof : ProfileKind}
  {hr : HostReady Unit}

/-- A big-step chunk under two more continuations. -/
theorem chunk3 {α β γ : Type} {th : Option ThreadId} {p : Canon.P (E3 P) Unit α}
    {f : α → Canon.P (E3 P) Unit β} {g : β → Canon.P (E3 P) Unit γ}
    {h : γ → Canon.P (E3 P) Unit (Ret (E3 P))} {M m' M₂ : Machine.Config (E3 P) Unit}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    {tr tr' : List (Label (E3 P) Unit)} {a : α}
    (hc : M.ctl = ⟨th, .prog (((p >>= f) >>= g) >>= h), segs⟩ :: rest)
    (hR : RunsQ d th p M tr a m') (hl : M.store.lockdown = false)
    (r : LRun prof hr d { m' with ctl := ⟨th, .prog ((f a >>= g) >>= h), segs⟩ :: rest } tr'
      M₂) :
    LRun prof hr d M (tr ++ tr') M₂ := by
  have hc' : M.ctl = ⟨th, .prog ((p >>= f) >>= fun b => g b >>= h), segs⟩ :: rest := by
    rw [hc, Prog.bind_eq, Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
    rfl
  refine RunsQ.chunk2 hc' hR hl ?_
  have e : (f a >>= fun b => g b >>= h) = ((f a >>= g) >>= h) := by
    rw [Prog.bind_eq, Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
    rfl
  rw [e]
  exact r

/-- A big-step chunk under three more continuations. -/
theorem chunk4 {α β γ δ : Type} {th : Option ThreadId} {p : Canon.P (E3 P) Unit α}
    {f : α → Canon.P (E3 P) Unit β} {g : β → Canon.P (E3 P) Unit γ}
    {h : γ → Canon.P (E3 P) Unit δ} {k : δ → Canon.P (E3 P) Unit (Ret (E3 P))}
    {M m' M₂ : Machine.Config (E3 P) Unit}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    {tr tr' : List (Label (E3 P) Unit)} {a : α}
    (hc : M.ctl = ⟨th, .prog ((((p >>= f) >>= g) >>= h) >>= k), segs⟩ :: rest)
    (hR : RunsQ d th p M tr a m') (hl : M.store.lockdown = false)
    (r : LRun prof hr d { m' with ctl := ⟨th, .prog (((f a >>= g) >>= h) >>= k), segs⟩ :: rest }
      tr' M₂) :
    LRun prof hr d M (tr ++ tr') M₂ := by
  have hc' : M.ctl = ⟨th, .prog (((p >>= f) >>= g) >>= fun c => h c >>= k), segs⟩ :: rest := by
    rw [hc, Prog.bind_eq, Prog.bind_eq, Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
    rfl
  refine chunk3 hc' hR hl ?_
  have e : ((f a >>= g) >>= fun c => h c >>= k) = (((f a >>= g) >>= h) >>= k) := by
    simp only [Prog.bind_eq, Prog.bind_assoc]
  rw [e]
  exact r

end RunsQ

/-- `handlesRemove` of a live entry of instance `0`'s table. -/
theorem runs_handlesRemove {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {ι₁ ι₂ : InstState} {i : ℕ} {e : HandleEntry} (hins : m.store.insts = [ι₁])
    (hrem : ι₁.removeHandle? i = some (e, ι₂)) :
    RunsQ (D P) th (handlesRemove ⟨0⟩ i) m [.tau, .tau] e
      { m with store := { m.store with insts := [ι₂] } } := by
  have hgi : ArenaField.insts.get? m.store ⟨0⟩ = some ι₁ := insts_get₀ hins
  have hst : ArenaOps.updateSt ArenaField.insts ⟨0⟩ (InstState.removeHandle i) m.store =
      { m.store with insts := [ι₂] } := by
    have hl : List.modify m.store.insts 0 (InstState.removeHandle i) = [ι₂] := by
      rw [hins]
      simp [InstState.removeHandle, hrem]
    show ({ m.store with insts := List.modify m.store.insts 0 _ } : CStore (E3 P)) = _
    rw [hl]
  unfold handlesRemove
  refine RunsQ.bind (tr₂ := [.tau]) (runs_getObj ArenaField.insts _ m hgi) ?_
  rw [hrem]
  rw [← hst]
  exact RunsQ.bind (runs_modifyStore _ _ rfl) (.pure _ _)

/-- `resource.drop` up to the destructor call, for an own handle of the toy's resource type:
the entry is removed and the destructor request is returned. -/
theorem runs_dropCore {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {ι₁ ι₂ : InstState} {i : ℕ} {hid : HandleObjId} {h : ResourceHandle}
    (hins : m.store.insts = [ι₁]) (hrem : ι₁.removeHandle? i = some (.resource hid, ι₂))
    (hH : ArenaField.resHandles.get? m.store hid = some h) (hrt : h.rt = ⟨0⟩)
    (hlend : h.numLends = 0) (hown : h.own = true)
    (hty : m.store.resourceTypes = [{ impl := some ⟨0⟩ }]) :
    ∃ tr, RunsQ (D P) th (resourceDropCore Limits.spec ⟨0⟩ ⟨0⟩ i) m tr
      (some { rt := ⟨0⟩, impl := some ⟨0⟩, dtor := none, rep := h.rep })
      { m with store := { m.store with insts := [ι₂] } } := by
  have hH' : ArenaField.resHandles.get? { m.store with insts := [ι₂] } hid = some h := hH
  have hty' : ArenaField.resourceTypes.get? { m.store with insts := [ι₂] } (⟨0⟩ : RtId) =
      some ({ impl := some ⟨0⟩ } : ResourceType (E3 P)) := by
    simp only [ArenaField.get?, ArenaField.resourceTypes, hty, Arena.get?_eq_getElem?]
    rfl
  apply Exists.intro
  unfold resourceDropCore
  apply RunsQ.bind (runs_handlesRemove hins hrem)
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind (runs_getObj ArenaField.resHandles hid
    { m with store := { m.store with insts := [ι₂] } } hH')
  apply RunsQ.bind (runs_trapIf (by rw [hrt]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hlend]; rfl) _ _)
  unfold dropHandleTail
  rw [ite_eq_left hown]
  exact RunsQ.bind (runs_getObj ArenaField.resourceTypes _
    { m with store := { m.store with insts := [ι₂] } } hty') (.pure _ _)

/-- One step of a non-choice program in focus whose store is not locked down by `h`. -/
macro "dstep " h:term : tactic => `(tactic| apply LRun.prog rfl (fun _ _ e => by cases e)
  (by exact $h)
  (by first
    | exact Step.get rfl | exact Step.modify rfl | exact Step.call rfl | exact Step.popProg rfl
    | exact Step.currentThread rfl | exact Step.hostGet rfl | exact Step.hostSet rfl
    | exact Step.emit rfl | exact Step.popCore rfl
    | exact Step.resumeThread rfl rfl | exact Step.newThread rfl rfl | exact Step.threadExit rfl
    | exact Step.hostDone rfl | exact Step.callCore rfl))

/-- The store `S` with the instance `ι` and one more caller record (the destructor record of
`rep`), task and thread. -/
def dStore (S : CStore (E3 P)) (rep : ℕ) (ι : InstState) (dtk : Runtime.Task (E3 P))
    (dthr : Runtime.Thread) : CStore (E3 P) :=
  { S with
    insts := [ι]
    callers := S.callers ++ [.sub (.destructor rep)]
    tasks := S.tasks ++ [dtk]
    threads := S.threads ++ [dthr] }

/-- The destructor task of a drop from store `S`, as allocated. -/
def dTask₀ (S : CStore (E3 P)) : Runtime.Task (E3 P) :=
  { ft := dtorType .i32, opts := {}, inst := ⟨0⟩, caller := ⟨S.callers.length⟩ }

/-- The destructor task once its implicit thread `t` is registered. -/
def dTask₁ (S : CStore (E3 P)) (t : ThreadId) : Runtime.Task (E3 P) :=
  ({ dTask₀ S with implicitThread := some t } : Runtime.Task (E3 P)).addThread t

/-- **The callout to `resource.drop` of an own handle**: the entry is removed, and REF's no-op
destructor runs in a new task and thread of instance `0` (registered at slot `n` and freed
again); the callout returns `[]`. -/
theorem lrun_dropCallout {prof : ProfileKind} {M : Machine.Config (E3 P) Unit} {t : ThreadId}
    {a : FlatValue} {sg : List (Seg (E3 P) Unit)} {R : List (Activation (E3 P) Unit)}
    {thr : Runtime.Thread} {tk : Runtime.Task (E3 P)} {ι₁ ι₂ ι₃ ι₄ : InstState}
    {hid : HandleObjId} {h : ResourceHandle} {n : ℕ} {t₀ : ThreadId}
    (hc : M.ctl = ⟨some t, .prog (D P (.hostCallout (dropH P) [a])), sg⟩ :: R)
    (hl : M.store.lockdown = false)
    (hthr : ArenaField.threads.get? M.store t = some thr)
    (htk : ArenaField.tasks.get? M.store thr.task = some tk) (hinst : tk.inst = ⟨0⟩)
    (hi : M.store.insts = [ι₁]) (hleave : ι₁.mayLeave = true)
    (hrem : ι₁.removeHandle? (flatNat a) = some (.resource hid, ι₂)) (hleave₂ : ι₂.mayLeave = true)
    (hH : ArenaField.resHandles.get? M.store hid = some h) (hrt : h.rt = ⟨0⟩)
    (hlend : h.numLends = 0) (hown : h.own = true)
    (hty : M.store.resourceTypes = [{ impl := some ⟨0⟩ }])
    (hadd : ι₂.addThread? ⟨M.store.threads.length⟩ = some (n, ι₃))
    (hrm : ι₃.removeThread? n = some (t₀, ι₄)) :
    ∃ dtk dthr C tr, LRun prof (refHost P).hr (D P) M tr
      { M with
        store := { M.store with
          insts := [ι₄]
          callers := M.store.callers ++ [.sub (.destructor h.rep)]
          tasks := M.store.tasks ++ [dtk]
          threads := M.store.threads ++ [dthr] }
        conts := C
        ctl := ⟨some t, .prog (pure (.flat [])), sg⟩ :: R } := by
  have hentry := calloutEntry_builtin (b := .resourceDrop ⟨0⟩) hthr htk hinst
  obtain ⟨kd, hkd⟩ := dtorArg_int (P := P) (CStore.setTaskState ⟨M.store.tasks.length⟩ .started
    (dStore M.store h.rep ι₃ (dTask₁ M.store ⟨M.store.threads.length⟩)
      ((thread₁ M.store.tasks).withIndex n))) ⟨M.store.callers.length⟩ h.rep
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply LRun.prog hc (fun _ _ e => by cases e) hl (Step.currentThread hc)
  apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl) (Step.get rfl)
  show LRun _ _ _ { M with ctl := ⟨some t, .prog (match calloutEntry M.store (some t) (dropH P)
    with | some r => trap r | none => _), sg⟩ :: R } _ _
  rw [hentry]
  show LRun _ _ _ { M with ctl := ⟨some t, .prog (Builtins.resourceDrop Limits.spec Quirks.none
    (destructorCall Limits.spec Quirks.none) ⟨0⟩ (flatNat a) >>= fun fl => pure (Ret.flat fl)),
    sg⟩ :: R } _ _
  unfold Builtins.resourceDrop
  apply RunsQ.chunk2 rfl (runs_resourceEnter (by exact hthr) (by exact htk) hinst
    (by exact hi) hleave).choose_spec (by exact hl)
  apply RunsQ.chunk2 rfl (runs_dropCore (by exact hi) hrem (by exact hH) hrt hlend
    hown (by exact hty)).choose_spec (by exact hl)
  dsimp only
  unfold destructorCall
  dsimp only
  have hty' : ArenaField.resourceTypes.get? { M.store with insts := [ι₂] } (⟨0⟩ : RtId) =
      some ({ impl := some ⟨0⟩ } : ResourceType (E3 P)) := by
    simp only [ArenaField.get?, ArenaField.resourceTypes, hty, Arena.get?_eq_getElem?]
    rfl
  apply RunsQ.chunk3 rfl (runs_getObj ArenaField.insts ⟨0⟩ _ (by exact insts_get₀ rfl))
    (by exact hl)
  apply RunsQ.chunk3 rfl (runs_trapIf (by rw [hleave₂]; rfl) _ _) (by exact hl)
  apply RunsQ.chunk3 rfl (runs_getObj ArenaField.resourceTypes ⟨0⟩ _ (by exact hty'))
    (by exact hl)
  apply RunsQ.chunk3 rfl (runs_allocObj ArenaField.callers _ _ rfl) (by exact hl)
  dsimp only
  unfold canonLiftNoop
  apply RunsQ.chunk4 rfl (runs_allocObj ArenaField.tasks _ _ rfl) (by exact hl)
  apply RunsQ.chunk4 rfl (RunsQ.newThread rfl rfl (.pure _ _)) (by exact hl)
  unfold Thread.resume
  simp only [Prog.bind_eq, Prog.bind_assoc]
  apply RunsQ.chunk rfl (RunsQ.get (.pure _ _)) (by exact hl)
  apply RunsQ.chunk rfl (runs_ite_false (by exact threadIs_last rfl) _ _) (by exact hl)
  apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl)
    (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
  have e₁ : ∀ S : CStore (E3 P),
      S.threads = M.store.threads ++ [{ task := ⟨M.store.tasks.length⟩ }] →
      threadStatusSt ⟨M.store.threads.length⟩ .running S =
        { S with threads := M.store.threads ++ [thread₁ M.store.tasks] } :=
    fun S h => threadStatus_last h _
  apply LRun.store_congr (S' := dStore M.store h.rep ι₂ (dTask₀ M.store) (thread₁ M.store.tasks))
    (by exact (e₁ _ rfl).trans rfl)
  dsimp only
  apply RunsQ.chunk rfl (runs_enterN (Gt := M.store.tasks) (y := dTask₀ M.store) rfl rfl rfl rfl
    hadd) (by exact hl)
  apply LRun.store_congr (S' := dStore M.store h.rep ι₃ (dTask₁ M.store ⟨M.store.threads.length⟩)
    ((thread₁ M.store.tasks).withIndex n))
    (by exact (registerThreadSt_eq (tasks_modify_last rfl _) rfl rfl hadd rfl).trans rfl)
  apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (by exact tasks_get_last rfl))
    (by exact hl)
  apply RunsQ.chunk rfl (runs_startD (Gt := M.store.tasks) (Gc := M.store.callers)
    (y := dTask₁ M.store ⟨M.store.threads.length⟩) (by exact rfl) rfl (by exact rfl)) (by exact hl)
  apply LRun.store_congr (S' := dStore M.store h.rep ι₃
    ((dTask₁ M.store ⟨M.store.threads.length⟩).withState .started)
    ((thread₁ M.store.tasks).withIndex n))
    (by
      exact setTaskState_last (Gt := M.store.tasks) (y := dTask₁ M.store ⟨M.store.threads.length⟩)
        rfl _)
  apply RunsQ.chunk rfl (runs_lowerDtor _ _ _ _ hkd _) (by exact hl)
  apply RunsQ.chunk rfl (runs_liftDtor _ _) (by exact hl)
  apply RunsQ.chunk rfl (runs_returnD (Gt := M.store.tasks) (Gc := M.store.callers)
    (y := (dTask₁ M.store ⟨M.store.threads.length⟩).withState .started) _
    (by exact rfl) rfl rfl rfl (by exact rfl)) (by exact hl)
  apply LRun.store_congr (S' := dStore M.store h.rep ι₃
    (((dTask₁ M.store ⟨M.store.threads.length⟩).withState .started).withState .resolved)
    ((thread₁ M.store.tasks).withIndex n))
    (by
      exact setTaskState_last (Gt := M.store.tasks)
        (y := (dTask₁ M.store ⟨M.store.threads.length⟩).withState .started) rfl _)
  apply RunsQ.chunk rfl (runs_exit (Gt := M.store.tasks) (Gth := M.store.threads)
    (y := ((dTask₁ M.store ⟨M.store.threads.length⟩).withState .started).withState .resolved)
    (z := (thread₁ M.store.tasks).withIndex n) (ι := ι₃) rfl rfl rfl rfl rfl rfl rfl rfl hrm)
    (by exact hl)
  have hι₄ : InstState.removeThread n ι₃ = ι₄ := by simp [InstState.removeThread, hrm]
  apply LRun.store_congr (S' := dStore M.store h.rep ι₄
    { ((dTask₁ M.store ⟨M.store.threads.length⟩).withState .started).withState .resolved with
      threads := (((dTask₁ M.store ⟨M.store.threads.length⟩).withState .started).withState
        .resolved).threads.erase ⟨M.store.threads.length⟩ }
    ((thread₁ M.store.tasks).withIndex n))
    (by rw [← hι₄]; exact unregisterThreadSt_eq _ _ rfl rfl rfl)
  dstep hl
  apply LRun.store_congr (S' := dStore M.store h.rep ι₄
    { ((dTask₁ M.store ⟨M.store.threads.length⟩).withState .started).withState .resolved with
      threads := (((dTask₁ M.store ⟨M.store.threads.length⟩).withState .started).withState
        .resolved).threads.erase ⟨M.store.threads.length⟩ }
    { (thread₁ M.store.tasks).withIndex n with status := .exited })
    (by exact threadStatus_last (Gth := M.store.threads) rfl _)
  apply RunsQ.chunk rfl (runs_ite_loop (Gt := M.store.tasks) rfl rfl rfl) (by exact hl)
  exact .refl _

end Silmaril.Wasm.Resource.CompToy
