module

public import Silmaril.Proofs.Wasm.Resource.CompToy.DropCore
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# The toy resource component: export calls whose core phase adds records

`toy_callAtX` is `toy_callAt` (`Silmaril.Proofs.Wasm.Resource.CompToy.Call`) whose return half
allows tasks, threads and caller records appended after the call's own during the core phase
(as a destructor call of `resource.drop` leaves), and any saved-continuation slots. The head
lemmas of `Task.return_`, `exit_implicit_thread` and the synchronous loop are restated for a
call's records with records on both sides (`runs_returnMT`, `runs_exitMT`, `runs_ite_loopM`; the
analogues of `LinkCallK.runs_returnM` … for the toy's single instance). New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs

variable {P : Silmaril.Wasm.Numerics.Profile}

/-! ## Arenas with records on both sides -/

theorem getElem?_mid {α : Type} {l r : List α} {a : α} : (l ++ [a] ++ r)[l.length]? = some a := by
  rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem modify_midT {α : Type} (l r : List α) (a : α) (f : α → α) :
    (l ++ [a] ++ r).modify l.length f = l ++ [f a] ++ r := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    show (b :: (l ++ [a] ++ r)).modify (l.length + 1) f = b :: (l ++ [f a] ++ r)
    rw [List.modify_succ_cons, ih]

theorem setTaskState_midT {s : CStore (E3 P)} {Gt R : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} (h : s.tasks = Gt ++ [y] ++ R) (st : Async.TaskState) :
    CStore.setTaskState ⟨Gt.length⟩ st s = { s with tasks := Gt ++ [y.withState st] ++ R } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [CStore.setTaskState, ArenaField.modify, ArenaField.tasks, Arena.modify, modify_midT]

theorem threadStatus_midT {s : CStore (E3 P)} {Gth R : List Runtime.Thread} {z : Runtime.Thread}
    (h : s.threads = Gth ++ [z] ++ R) (st : ThreadStatus) :
    threadStatusSt ⟨Gth.length⟩ st s =
      { s with threads := Gth ++ [{ z with status := st }] ++ R } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [threadStatusSt, ArenaField.modify, ArenaField.threads, Arena.modify, modify_midT]

theorem unregisterThreadSt_midT {s : CStore (E3 P)} {Gt R : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {ι : InstState} (t : ThreadId) (i : Nat)
    (ht : s.tasks = Gt ++ [y] ++ R) (hinst : y.inst = ⟨0⟩) (hi : s.insts = [ι]) :
    CStore.unregisterThreadSt ⟨Gt.length⟩ t i s =
      { s with
        tasks := Gt ++ [{ y with threads := y.threads.erase t }] ++ R
        insts := [InstState.removeThread i ι] } := by
  have h₁ : s.task? ⟨Gt.length⟩ = some y := by
    show s.tasks[Gt.length]? = some y
    rw [ht]
    exact getElem?_mid
  unfold CStore.unregisterThreadSt
  rw [h₁]
  obtain ⟨⟩ := s
  dsimp only at ht hi ⊢
  subst ht hi
  simp only [ArenaField.modify, ArenaField.tasks, ArenaField.insts, Arena.modify, modify_midT,
    show y.inst.idx = 0 by rw [hinst]]
  rfl

/-- `Task.return_` of a task with records on both sides, its caller a host record. -/
theorem runs_returnMT {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gt R : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gc CL : List (Caller (E3 P))}
    {c : CallId} {args : List Val} (vs : List Val) (ht : m.store.tasks = Gt ++ [y] ++ R)
    (hy : y.caller = ⟨Gc.length⟩) (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : m.store.callers = Gc ++ [.host c args 0] ++ CL) :
    RunsQ (D P) th (Task.return_ ⟨Gt.length⟩ vs) m
      [.tau, .tau, .tau, .obs (.resolved c (some vs)), .tau, .tau] ()
      { m.resolve c (some vs) with
        store := CStore.setTaskState ⟨Gt.length⟩ .resolved m.store } := by
  have hgt : ArenaField.tasks.get? m.store (⟨Gt.length⟩ : TaskId) = some y := by
    show m.store.tasks[Gt.length]? = some y
    rw [ht]
    exact getElem?_mid
  have hgc : ArenaField.callers.get? m.store (⟨Gc.length⟩ : CallerId) = some (.host c args 0) := by
    show m.store.callers[Gc.length]? = some _
    rw [hc]
    exact getElem?_mid
  have hor : RunsQ (D P) th (D P (.onResolve ⟨Gc.length⟩ (some vs))) m
      [.tau, .obs (.resolved c (some vs))] .unit (m.resolve c (some vs)) := by
    show RunsQ _ _ (callerOnResolve Limits.spec Quirks.none ⟨Gc.length⟩ (some vs)) _ _ _ _
    unfold callerOnResolve
    exact RunsQ.bind (runs_getObj ArenaField.callers _ _ hgc)
      (RunsQ.bind (tr₁ := [.obs (.resolved c (some vs))]) (.emit (.pure _ _)) (.pure _ _))
  unfold Task.return_
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ hgt)
  apply RunsQ.bind (runs_trapIf (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hb]; rfl) _ _)
  rw [hy]
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call hor (.pure _ _))
  exact runs_modifyStore _ _ rfl
  rfl

/-- `exit_implicit_thread` of a task of instance `0` with records on both sides. -/
theorem runs_exitMT {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gt R : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gth R' : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y] ++ R) (himp : y.implicitThread = some ⟨Gth.length⟩)
    (hst : y.state = .resolved) (hasync : y.ft.async_ = false)
    (hthr : m.store.threads = Gth ++ [z] ++ R') (hidx : z.index = some i) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (D P) th (Task.exitImplicitThread ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  have hgt : ArenaField.tasks.get? m.store (⟨Gt.length⟩ : TaskId) = some y := by
    show m.store.tasks[Gt.length]? = some y
    rw [ht]
    exact getElem?_mid
  have hgz : ArenaField.threads.get? m.store (⟨Gth.length⟩ : ThreadId) = some z := by
    show m.store.threads[Gth.length]? = some z
    rw [hthr]
    exact getElem?_mid
  have hi : ArenaField.insts.get? m.store y.inst = some ι := by
    rw [hinst]
    exact insts_get_zero hinsts
  have hu : RunsQ (D P) th (Task.unregisterThread ⟨Gt.length⟩ ⟨Gth.length⟩) m
      [.tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
    unfold Task.unregisterThread
    apply RunsQ.of_tr
    apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ hgt)
    apply RunsQ.bind (runs_trapIf (by rw [hst]; simp) _ _)
    apply RunsQ.bind (runs_getObj ArenaField.threads _ _ hgz)
    rw [hidx]
    apply RunsQ.bind (.pure _ _)
    apply RunsQ.bind (runs_getObj ArenaField.insts _ _ hi)
    rw [hrem]
    exact runs_modifyStore _ _
      (CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.2.1
    rfl
  unfold Task.exitImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ hgt)
  rw [himp]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind hu
  exact runs_ite_false (by rw [hasync]; rfl) _ _
  rfl

/-- The synchronous loop of a resolved task with records on both sides. -/
theorem runs_ite_loopM {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gt R : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)}
    (ht : m.store.tasks = Gt ++ [y] ++ R) (hst : y.state = .resolved) {b : Bool} (hb : b = false) :
    RunsQ (D P) th (if !b then callUnit (.loop (.syncLiftLoop ⟨Gt.length⟩)) else pure () :
      Canon.P (E3 P) Unit Unit) m [.tau, .tau, .tau] () m := by
  subst hb
  have hgt : ArenaField.tasks.get? m.store (⟨Gt.length⟩ : TaskId) = some y := by
    show m.store.tasks[Gt.length]? = some y
    rw [ht]
    exact getElem?_mid
  have hl : RunsQ (D P) th (D P (.loop (.syncLiftLoop ⟨Gt.length⟩))) m [.tau] .unit m := by
    show RunsQ _ _ (syncLiftLoopBody (fun _ _ => false) ⟨Gt.length⟩) _ _ _ _
    unfold syncLiftLoopBody
    apply RunsQ.bind (tr₂ := []) (runs_getObj ArenaField.tasks _ _ hgt)
    rw [hst]
    exact .pure _ _
  show RunsQ _ _ (callUnit (.loop (.syncLiftLoop ⟨Gt.length⟩))) _ _ _ _
  unfold callUnit callRet perform Prog.lift
  exact RunsQ.call hl (.pure _ _)

/-! ## Stores and leftovers with appended records -/

variable (P) in
/-- The store at the return of a call whose core phase appended the records `Xt`, `Xth`, `Xc`. -/
noncomputable def tStoreX (ft : WIT.FuncType Empty RtId) (c : ℕ) (ι ι' : InstState)
    (G : ToyGarb P) (k : ℕ) (args : List Val) (ιx : InstState) (Hx : List ResourceHandle)
    (cs : (core3P P).Store (CanonHost (core3P P))) (Xt : List (Runtime.Task (E3 P)))
    (Xth : List Runtime.Thread) (Xc : List (Caller (E3 P))) : CStore (E3 P) :=
  { tStore₄ P ft c ι ι' G k args ιx Hx with
    core := cs
    tasks := G.tasks ++ [(tTask₁ P ft G.callers ⟨G.threads.length⟩).withState .started] ++ Xt
    threads := G.threads ++ [(thread₁ G.tasks).withIndex 1] ++ Xth
    callers := G.callers ++ [.host ⟨k⟩ args 0] ++ Xc }

variable (P) in
/-- The leftovers after a call whose core phase appended `Xt`, `Xth`, `Xc`, with the
saved-continuation slots `C`. -/
noncomputable def nextGX (G : ToyGarb P) (ft : WIT.FuncType Empty RtId) (k j addr : ℕ)
    (args rs : List Val) (H : List ResourceHandle) (Xt : List (Runtime.Task (E3 P)))
    (Xth : List Runtime.Thread) (Xc : List (Caller (E3 P)))
    (C : List (Option (Activation (E3 P) Unit))) : ToyGarb P :=
  { nextG P G ft k j addr args rs H with
    tasks := G.tasks ++ [tTask₂ P ft G.callers ⟨G.threads.length⟩] ++ Xt
    threads := G.threads ++ [{ (thread₁ G.tasks).withIndex 1 with status := .exited }] ++ Xth
    callers := G.callers ++ [.host ⟨k⟩ args 0] ++ Xc
    conts := C }

theorem nextGX_ok {G : ToyGarb P} (hG : G.Ok) (ft : WIT.FuncType Empty RtId) (k j addr : ℕ)
    (args rs : List Val) (H : List ResourceHandle) (Xt : List (Runtime.Task (E3 P)))
    (Xth : List Runtime.Thread) (Xc : List (Caller (E3 P)))
    (C : List (Option (Activation (E3 P) Unit))) :
    (nextGX P G ft k j addr args rs H Xt Xth Xc C).Ok :=
  nextG_ok hG ft k j addr args rs H

theorem result?_nextGX {G : ToyGarb P} (hG : G.Ok) {k : ℕ} (hk : ∀ x ∈ G.pending, x.1 ≠ ⟨k⟩)
    (c : ℕ) (ι : InstState) (ft : WIT.FuncType Empty RtId) (j addr : ℕ) (args rs : List Val)
    (H : List ResourceHandle) (Xt : List (Runtime.Task (E3 P))) (Xth : List Runtime.Thread)
    (Xc : List (Caller (E3 P))) (C : List (Option (Activation (E3 P) Unit))) :
    (toyCfgX P c ι (nextGX P G ft k j addr args rs H Xt Xth Xc C)).result? ⟨k⟩ =
      some (some rs) :=
  result?_nextG hG hk c ι ft j addr args rs H

/-! ## The call -/

/-- `toy_callAt` whose return half allows records `Xt`, `Xth`, `Xc` appended to the task, thread
and caller arenas during the core phase, and any saved-continuation slots `C`. -/
theorem toy_callAtX (prof : ProfileKind) (ft : WIT.FuncType Empty RtId) (j addr : ℕ)
    (args : List Val) (xs : List FlatValue) (c : ℕ) (ι ι' ι₄ : InstState) (G : ToyGarb P) (k : ℕ)
    (H₄ : List ResourceHandle) (trL : List (Label (E3 P) Unit))
    (hf : (toyFuncs P)[j]? = some (.lifted (show (core3P P).FuncAddr from addr) ft {} ⟨0⟩))
    (hasync : ft.async_ = false)
    (hadd : ι.addThread? ⟨G.threads.length⟩ = some (1, ι'))
    (hlow : ∀ m : Machine.Config (E3 P) Unit, m.store = tStore₃ P ft c ι ι' G k args →
      RunsQ (D P) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
        ABI.maxFlatParams args (paramTypes ft) none) m trL xs
        { m with store := tStore₄ P ft c ι ι' G k args ι₄ H₄ }) :
    ∃ M₀ th K segs rest tr₁, LRun prof (refHost P).hr (D P) (toyInvoked P c ι G k ⟨j⟩ args) tr₁ M₀ ∧
      th = some ⟨G.threads.length⟩ ∧ M₀.ctl =
        ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat addr xs) K, segs⟩ :: rest ∧
      M₀.store = tStore₄ P ft c ι ι' G k args ι₄ H₄ ∧
      (∀ ys, ∃ (β : Type) (f : List Val × FlatCursor → Canon.P (E3 P) Unit β)
        (g : β → Canon.P (E3 P) Unit (Ret (E3 P))), K ys = (liftFlatValues Limits.spec Quirks.none
          ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
          ABI.maxFlatResults (.ofList ys) (resultTypes ft) >>= f) >>= g) ∧
      ∀ (cs' : (core3P P).Store (CanonHost (core3P P))) (ιc ι₅ : InstState)
        (Hc H₅ : List ResourceHandle) (ys : List FlatValue) (ws : List Val) (cur : FlatCursor)
        (trF : List (Label (E3 P) Unit)) (c' : ℕ) (Xt : List (Runtime.Task (E3 P)))
        (Xth : List Runtime.Thread) (Xc : List (Caller (E3 P)))
        (C : List (Option (Activation (E3 P) Unit))),
        (∀ m : Machine.Config (E3 P) Unit,
          m.store = tStoreX P ft c ι ι' G k args ιc Hc cs' Xt Xth Xc →
          RunsQ (D P) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none
            ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
            ABI.maxFlatResults (.ofList ys) (resultTypes ft)) m trF (ws, cur)
            { m with store := tStoreX P ft c ι ι' G k args ι₅ H₅ cs' Xt Xth Xc }) →
        cs' = setCtr P (toyInst P).store.core c' →
        ι₅.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι₅) →
        ∃ tr, LRun prof (refHost P).hr (D P)
          { M₀ with store := tStoreX P ft c ι ι' G k args ιc Hc cs' Xt Xth Xc, conts := C,
                    ctl := ⟨th, .prog (K ys), segs⟩ :: rest } tr
          (toyCfgX P c' (InstState.removeThread 1 ι₅)
            (nextGX P G ft k j addr args ws H₅ Xt Xth Xc C)) := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  unfold toyInvoked
  apply RunsQ.chunk rfl (runs_allocObj ArenaField.callers (.host ⟨k⟩ args 0) _ rfl) rfl
  apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
  apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
  have hget : ∀ s : CStore (E3 P), s.funcs = toyFuncs P →
      ArenaField.funcs.get? s (⟨j⟩ : FuncId) =
        some (.lifted (show (core3P P).FuncAddr from addr) ft {} ⟨0⟩) := by
    intro s e
    simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
    exact hf
  apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
  apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
  apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
  apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
  apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) rfl
  apply LRun.prog rfl (fun _ _ e => by cases e) rfl
    (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
  have e₁ : ∀ S : CStore (E3 P), S.threads = G.threads ++ [{ task := ⟨G.tasks.length⟩ }] →
      threadStatusSt ⟨G.threads.length⟩ .running S =
        { S with threads := G.threads ++ [thread₁ G.tasks] } :=
    fun S h => threadStatus_last h _
  apply LRun.store_congr (S' := tStore₁ P ft c ι G k args) ((e₁ _ rfl).trans rfl)
  have hS₁ : (tStore₁ P ft c ι G k args).insts = [ι] := rfl
  apply RunsQ.chunk (th := some ⟨G.threads.length⟩)
    (p := Task.enterImplicitThread Quirks.none ⟨G.tasks.length⟩) (a := true) rfl
    (runs_enter (Gt := G.tasks) (y := tTask₀ P ft G.callers) rfl hasync rfl hS₁ hadd) rfl
  have e₂ : CStore.registerThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩
      (CStore.setImplicitThread ⟨G.tasks.length⟩ ⟨G.threads.length⟩
        (tStore₁ P ft c ι G k args)) = tStore₂ P ft c ι ι' G k args :=
    enter_eq rfl rfl rfl hadd rfl
  apply LRun.store_congr (S' := tStore₂ P ft c ι ι' G k args) (by exact e₂)
  have hS₂ : (tStore₂ P ft c ι ι' G k args).tasks =
      G.tasks ++ [tTask₁ P ft G.callers ⟨G.threads.length⟩] := rfl
  apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last (Gt := G.tasks) hS₂))
    rfl
  apply RunsQ.chunk rfl (runs_start (Gt := G.tasks) (Gc := G.callers) hS₂ rfl rfl) rfl
  apply RunsQ.chunk rfl (hlow _ (setTaskState_last (Gt := G.tasks) rfl _)) rfl
  mstep
  exact .refl _
  refine ⟨rfl, rfl, rfl, fun ys => ⟨_, _, _, rfl⟩, ?_⟩
  intro cs' ιc ι₅ Hc H₅ ys ws cur trF c' Xt Xth Xc C hlift hcs hrem
  apply Exists.intro
  apply RunsQ.chunk2 rfl (hlift _ rfl) rfl
  apply RunsQ.chunk2 rfl
    (runs_returnMT (Gt := G.tasks) (Gc := G.callers) _ (R := Xt) (CL := Xc) rfl rfl rfl rfl rfl) rfl
  apply LRun.store_congr (S' := { tStoreX P ft c ι ι' G k args ι₅ H₅ cs' Xt Xth Xc with
      tasks := G.tasks ++ [((tTask₁ P ft G.callers ⟨G.threads.length⟩).withState .started).withState
        .resolved] ++ Xt })
    (by refine setTaskState_midT (Gt := G.tasks) ?_ _; rfl)
  apply RunsQ.chunk rfl
    (runs_exitMT (Gt := G.tasks) (Gth := G.threads) (R := Xt) (R' := Xth)
      (y := ((tTask₁ P ft G.callers ⟨G.threads.length⟩).withState .started).withState .resolved)
      (z := (thread₁ G.tasks).withIndex 1) (ι := ι₅) rfl rfl rfl hasync rfl rfl rfl rfl hrem) rfl
  apply LRun.store_congr (S' := { tStoreX P ft c ι ι' G k args ι₅ H₅ cs' Xt Xth Xc with
      tasks := G.tasks ++ [tTask₂ P ft G.callers ⟨G.threads.length⟩] ++ Xt
      insts := [InstState.removeThread 1 ι₅] }) (unregisterThreadSt_midT _ _ rfl rfl rfl)
  mstep
  apply LRun.store_congr (S' := { tStoreX P ft c ι ι' G k args ι₅ H₅ cs' Xt Xth Xc with
      tasks := G.tasks ++ [tTask₂ P ft G.callers ⟨G.threads.length⟩] ++ Xt
      insts := [InstState.removeThread 1 ι₅]
      threads := G.threads ++ [{ (thread₁ G.tasks).withIndex 1 with status := .exited }] ++ Xth })
    (threadStatus_midT (z := (thread₁ G.tasks).withIndex 1) rfl _)
  apply RunsQ.chunk rfl (runs_ite_loopM (Gt := G.tasks) (R := Xt) rfl rfl hasync) rfl
  mstep
  mstep
  mstep
  rw [hostFinish_cancel _ G.pending ⟨k⟩ ⟨j⟩ args _ rfl]
  subst hcs
  exact .refl _

end Silmaril.Wasm.Resource.CompToy
