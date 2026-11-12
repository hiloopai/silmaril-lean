module

public import Silmaril.Proofs.Wasm.Resource.MachineTab.Frames
public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# Handle tables along whole machine runs: the dispatcher

**`tabDispatch_canon`**: every program of the reference dispatcher `Canon.dispatch lim q hr
host` is table-moving, for a host whose own programs are (`TabHost`). The proof instantiates
the `P.Inv` lemmas of the reference programs (`canon_lift`, `canon_lower`, the loops, every
canon built-in, the caller records, nested instantiation) at the invariant `TabFrom j s₀` and
discharges each of their store-update hypotheses: the handle-table updates are table moves
(`tabMove_addHandle`, `tabMove_removeHandle`, including `LowerSt.addSubtaskSt`), every other
named update leaves the instance arena or the instance's handle table unchanged
(`Silmaril.Proofs.Wasm.Resource.MachineTab.Frames`). Instantiation allocates instances with an
empty table (`tabMove_allocInst`): `tabProg_instantiateClosure`, `tabProg_instantiateProg`.
`tabHost_none`: the host without functions is table-moving.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type} {j : InstId} {s₀ : CStore E}

/-! ## The store-update hypotheses at `TabFrom j s₀` -/

theorem tf_insts {g : CStore E → CStore E} (hg : ∀ s, (g s).insts = s.insts) :
    ∀ s, TabFrom j s₀ s → TabFrom j s₀ (g s) := tabFrom_of_insts hg

theorem tf_frame {i : InstId} {g : InstState → InstState} (hg : ∀ st, (g st).handles = st.handles) :
    ∀ s, TabFrom j s₀ s → TabFrom j s₀ (ArenaField.insts.modify s i g) :=
  tabFrom_of_move fun s => tabMove_modify_frame s i hg

theorem tf_addHandle : P.Inv.AddHandlePres (TabFrom j s₀ : CStore E → Prop) :=
  fun s i e hs => hs.trans (tabMove_addHandle s i e.1)

theorem tf_removeHandle : P.Inv.RemoveHandlePres (TabFrom j s₀ : CStore E → Prop) :=
  fun s i k hs => hs.trans (tabMove_removeHandle s i k)

theorem removeThread_handles (i : ℕ) (st : InstState) :
    (InstState.removeThread i st).handles = st.handles := by
  unfold InstState.removeThread InstState.removeThread?
  cases st.threads.remove? i <;> rfl

theorem tf_unregisterThread (task : TaskId) (t : ThreadId) (i : ℕ) :
    ∀ s, TabFrom j s₀ s → TabFrom j s₀ (CStore.unregisterThreadSt (E := E) task t i s) := by
  intro s hs
  unfold CStore.unregisterThreadSt
  split
  · exact hs
  · exact hs.trans (tabMove_modify_frame _ _ (removeThread_handles i))

theorem invHyps_tab : Task.InvHyps (TabFrom j s₀ : CStore E → Prop) where
  setTaskState _ _ := tf_insts fun _ => rfl
  setImplicitThread _ _ := tf_insts fun _ => rfl
  registerThread _ _ s hs := hs.trans (tabMove_registerThreadSt _ _ s)
  unregisterThread := tf_unregisterThread
  incWaitingToEnter _ := tf_frame fun _ => rfl
  decWaitingToEnter _ := tf_frame fun _ => rfl
  withExclusive _ _ := tf_frame fun _ => rfl
  startWaiting _ _ _ := tf_insts fun _ => rfl
  stopWaiting _ := tf_insts fun _ => rfl

theorem loadPres_tab : P.Inv.LoadPres (TabFrom j s₀ : CStore E → Prop) where
  remove := tf_removeHandle
  lender sub st h := tf_insts (g := HandleSt.addLender sub h) (fun _ => rfl) st
  release _ := tf_insts fun _ => rfl

theorem storePres_tab : P.Inv.StorePres (TabFrom j s₀ : CStore E → Prop) where
  write m p bs := tf_insts (writeMemSt_insts m p bs)
  allocRes _ _ := tf_insts (fun _ => rfl) _
  addHandle := tf_addHandle
  incBorrows _ := tf_insts fun _ => rfl
  setEndOwner _ _ := tf_insts fun _ => rfl
  setEndIndex _ _ := tf_insts fun _ => rfl

theorem tf_releaseCallback (inst : InstId) (t : ThreadId) :
    ∀ s, TabFrom j s₀ s → TabFrom j s₀ (LiftSt.releaseCallbackSt (E := E) inst t s) :=
  fun s hs => hs.trans ((tabMove_modify_frame (g := fun st => { st with exclusive := none }) s inst
    fun _ => rfl).trans (TabMove.of_insts rfl))

theorem tf_retakeCallback (inst : InstId) (t : ThreadId) :
    ∀ s, TabFrom j s₀ s → TabFrom j s₀ (LiftSt.retakeCallbackSt (E := E) inst t s) :=
  fun s hs => hs.trans ((TabMove.of_insts (s' := ArenaField.threads.modify s t fun th =>
    { th with cancellable := false }) rfl).trans
      (tabMove_modify_frame (g := fun st => { st with exclusive := some t }) _ inst fun _ => rfl))

theorem liftHyps_tab : LiftHyps (TabFrom j s₀ : CStore E → Prop) where
  task := invHyps_tab
  load := loadPres_tab
  store := storePres_tab
  allocTask _ _ _ _ := tf_insts fun _ => rfl
  allocCaller _ := tf_insts fun _ => rfl
  updateCaller _ _ := tf_insts fun _ => rfl
  stopWaiting _ := tf_insts fun _ => rfl
  startWaiting _ _ := tf_insts fun _ => rfl
  wsetIncWaiting _ := tf_insts fun _ => rfl
  wsetDecWaiting _ := tf_insts fun _ => rfl
  wsetSetElems _ _ := tf_insts fun _ => rfl
  takeWaitableEvent w := tf_insts (takeWaitableEventSt_insts w)
  setMayLeave _ _ _ := tf_frame fun _ => rfl
  release := tf_releaseCallback
  retake := tf_retakeCallback
  incNesting := tf_insts fun _ => rfl
  decNesting := tf_insts fun _ => rfl

theorem tf_addSubtask (inst : InstId) (sub : SubtaskId) (i : ℕ) :
    ∀ s, TabFrom j s₀ s → TabFrom j s₀ (LowerSt.addSubtaskSt (E := E) inst sub i s) := by
  intro s hs
  unfold LowerSt.addSubtaskSt
  split
  · exact hs
  · exact (hs.trans (tabMove_addHandle s inst _)).trans (TabMove.of_insts rfl)

theorem lowerPres_tab : P.Inv.LowerPres (TabFrom j s₀ : CStore E → Prop) where
  load := loadPres_tab
  store := storePres_tab
  allocSubtask _ := tf_insts fun _ => rfl
  allocCaller _ := tf_insts fun _ => rfl
  setOnCancel _ _ := tf_insts fun _ => rfl
  start _ := tf_insts fun _ => rfl
  setCallerPos _ _ := tf_insts fun _ => rfl
  releaseLends sub := tf_insts (releaseLendsSt_insts sub)
  setPending w _ := tf_insts fun s => modifyWaitableCommon_insts w _ s
  resolve _ _ _ := tf_insts fun _ => rfl
  deliver sub := tf_insts (deliverResolveSt_insts sub)
  startWaiting _ _ := tf_insts fun _ => rfl
  addSubtask := tf_addSubtask

theorem awaitPres_tab : Builtins.Inv.AwaitPres (TabFrom j s₀ : CStore E → Prop) where
  syncWaiter w _ := tf_insts fun s => modifyWaitableCommon_insts w _ s
  startWaiting _ _ := tf_insts fun _ => rfl
  takeEvent w := tf_insts (takeWaitableEventSt_insts w)

/-! ## Built-ins -/

local notation "TI" => P.Inv (TabFrom j s₀)

theorem tab_withArgs0 {α : Type} {args : List FlatValue} {k : P E σ α} (hk : TI k) :
    TI (withArgs0 args k) := by
  unfold withArgs0; split
  · exact hk
  · exact P.Inv.internal _

theorem tab_withArgs1 {α : Type} {args : List FlatValue} {k : ℕ → P E σ α} (hk : ∀ n, TI (k n)) :
    TI (withArgs1 args k) := by
  unfold withArgs1; split
  · exact hk _
  · exact P.Inv.internal _

theorem tab_withArgs2 {α : Type} {args : List FlatValue} {k : ℕ → ℕ → P E σ α}
    (hk : ∀ a b, TI (k a b)) : TI (withArgs2 args k) := by
  unfold withArgs2; split
  · exact hk _ _
  · exact P.Inv.internal _

theorem tab_withArgs3 {α : Type} {args : List FlatValue} {k : ℕ → ℕ → ℕ → P E σ α}
    (hk : ∀ a b c, TI (k a b c)) : TI (withArgs3 args k) := by
  unfold withArgs3; split
  · exact hk _ _ _
  · exact P.Inv.internal _

theorem tf_memWrite : Builtins.Inv.MemWritePres (TabFrom j s₀ : CStore E → Prop) :=
  fun m p _ => tf_insts (writeMemSt_insts m p _)

theorem tab_newBuiltin (lim : Limits) (k : Async.EndKind) (t : Option (WIT.ClosedType RtId)) :
    TI (Builtins.newBuiltin (σ := σ) lim k t) :=
  Builtins.Inv.newBuiltin tf_addHandle (fun _ _ _ => tf_insts fun _ => rfl)
    (fun _ _ => tf_insts fun _ => rfl) lim k t

theorem tab_copyBuiltin (lim : Limits) (q : Quirks) (k : Async.EndKind)
    (t : Option (WIT.ClosedType RtId)) (opts : CanonOpts E) (i p n : ℕ) :
    TI (Builtins.copyBuiltin (σ := σ) lim q k t opts i p n) :=
  Builtins.Inv.copyBuiltin loadPres_tab storePres_tab awaitPres_tab
    (fun e b r => tf_insts (copySt_insts e b r)) lim q k t opts i p n

theorem tab_cancelCopy (lim : Limits) (k : Async.EndKind) (t : Option (WIT.ClosedType RtId))
    (a : Bool) (i : ℕ) : TI (Builtins.cancelCopy (σ := σ) lim k t a i) :=
  Builtins.Inv.cancelCopy awaitPres_tab (fun e b => tf_insts (cancel_insts e b)) lim k t a i

theorem tab_dropEnd (lim : Limits) (k : Async.EndKind) (t : Option (WIT.ClosedType RtId))
    (i : ℕ) : TI (Builtins.dropEnd (σ := σ) lim k t i) :=
  Builtins.Inv.dropEnd tf_removeHandle (fun e => tf_insts (dropEnd_insts e)) lim k t i

theorem tab_forwardBuiltin (lim : Limits) (q : Quirks) (k : Async.EndKind)
    (t : Option (WIT.ClosedType RtId)) (ri wi : ℕ) :
    TI (Builtins.forwardBuiltin (σ := σ) lim q k t ri wi) :=
  Builtins.Inv.forwardBuiltin loadPres_tab storePres_tab tf_removeHandle
    (fun a b => tf_insts (forwardSt_insts a b)) lim q k t ri wi

theorem tab_threadNewIndirect (tbl : E.TableAddr) (ft : Silmaril.Wasm.V1.FuncType) (args : List FlatValue) :
    TI (match args with
      | [fi, c] => Builtins.threadNewIndirect (σ := σ) tbl ft (flatNat fi) c
      | _ => internal "built-in: wrong number of arguments") := by
  split
  · exact Builtins.P.Inv.threadNewIndirect tbl ft _ _ fun task t s hs =>
      hs.trans (tabMove_registerThreadSt task t s)
  · exact P.Inv.internal _

theorem tab_resourceDrop (lim : Limits) (q : Quirks) (rt : RtId) (i : ℕ) :
    TI (Builtins.resourceDrop (σ := σ) lim q (destructorCall lim q) rt i) :=
  Builtins.Inv.resourceDrop tf_removeHandle (fun t => tf_insts (g := HandleSt.decBorrows t)
    fun _ => rfl) lim q (fun inst req => P.Inv.destructorCall liftHyps_tab lim q inst req) rt i

/-- **Every canon built-in is table-moving.** -/
theorem tab_builtinProg (lim : Limits) (q : Quirks) (hr : HostReady σ) (b : ResolvedBuiltin E)
    (args : List FlatValue) : TI (builtinProg lim q hr b args) := by
  cases b with
  | resourceNew rt _ =>
    exact tab_withArgs1 fun rep =>
      Builtins.Inv.resourceNew (fun s rh => tf_insts (g := ArenaOps.allocSt ArenaField.resHandles rh)
        (fun _ => rfl) s) tf_addHandle lim rt rep
  | resourceDrop rt =>
    exact tab_withArgs1 fun i => tab_resourceDrop lim q rt i
  | resourceRep rt _ =>
    exact tab_withArgs1 fun i => Builtins.Inv.resourceRep lim rt i
  | backpressureInc =>
    exact tab_withArgs0 (Builtins.P.Inv.backpressureInc fun _ =>
      tf_frame fun _ => rfl)
  | backpressureDec =>
    exact tab_withArgs0 (Builtins.P.Inv.backpressureDec fun _ =>
      tf_frame fun _ => rfl)
  | taskReturn result opts =>
    exact Builtins.P.Inv.taskReturn loadPres_tab
      (fun _ => tf_insts fun _ => rfl) lim q result opts args
  | taskCancel =>
    exact tab_withArgs0 (Builtins.P.Inv.taskCancel fun _ => tf_insts fun _ => rfl)
  | contextGet t i =>
    exact tab_withArgs0 (Builtins.P.Inv.contextGet t i)
  | contextSet t i =>
    exact tab_withArgs1 fun v =>
      Builtins.P.Inv.contextSet t i v fun _ => tf_insts fun _ => rfl
  | subtaskCancel a =>
    exact tab_withArgs1 fun i => Builtins.Inv.subtaskCancel lim a i
      (fun _ _ => tf_insts fun _ => rfl) (fun _ _ => tf_insts fun _ => rfl)
      (fun _ => tf_insts fun s => modifyWaitableCommon_insts _ _ s)
      (fun w => tf_insts (takeWaitableEventSt_insts w))
  | subtaskDrop =>
    exact tab_withArgs1 fun i => Builtins.Inv.subtaskDrop lim i
      (fun inst s hs => tf_removeHandle s inst i hs) (fun _ => tf_insts (joinSt_insts _ none))
  | streamNew t =>
    exact tab_withArgs0 (tab_newBuiltin lim _ t)
  | streamRead t opts =>
    exact tab_withArgs3 fun i p n => tab_copyBuiltin lim q _ t opts i p n
  | streamWrite t opts =>
    exact tab_withArgs3 fun i p n => tab_copyBuiltin lim q _ t opts i p n
  | streamCancelRead t a =>
    exact tab_withArgs1 fun i => tab_cancelCopy lim _ t a i
  | streamCancelWrite t a =>
    exact tab_withArgs1 fun i => tab_cancelCopy lim _ t a i
  | streamDropReadable t =>
    exact tab_withArgs1 fun i => tab_dropEnd lim _ t i
  | streamDropWritable t =>
    exact tab_withArgs1 fun i => tab_dropEnd lim _ t i
  | streamForward t =>
    exact tab_withArgs2 fun ri wi => tab_forwardBuiltin lim q _ t ri wi
  | futureNew t =>
    exact tab_withArgs0 (tab_newBuiltin lim _ t)
  | futureRead t opts =>
    exact tab_withArgs2 fun i p => tab_copyBuiltin lim q _ t opts i p 1
  | futureWrite t opts =>
    exact tab_withArgs2 fun i p => tab_copyBuiltin lim q _ t opts i p 1
  | futureCancelRead t a =>
    exact tab_withArgs1 fun i => tab_cancelCopy lim _ t a i
  | futureCancelWrite t a =>
    exact tab_withArgs1 fun i => tab_cancelCopy lim _ t a i
  | futureDropReadable t =>
    exact tab_withArgs1 fun i => tab_dropEnd lim _ t i
  | futureDropWritable t =>
    exact tab_withArgs1 fun i => tab_dropEnd lim _ t i
  | futureForward t =>
    exact tab_withArgs2 fun ri wi => tab_forwardBuiltin lim q _ t ri wi
  | errorContextNew opts =>
    exact tab_withArgs2 fun p n => Builtins.P.Inv.errorContextNew lim q
      opts p n (fun _ => tf_insts fun _ => rfl) (fun inst _ s hs => hs.trans
        (tabMove_addHandle s inst _))
  | errorContextDebugMessage opts =>
    exact tab_withArgs2 fun i p =>
      Builtins.P.Inv.errorContextDebugMessage lim q opts i p fun m p bs =>
        tf_insts (writeMemSt_insts m p bs)
  | errorContextDrop =>
    exact tab_withArgs1 fun i => Builtins.P.Inv.errorContextDrop i
      fun inst s hs => hs.trans (tabMove_removeHandle s inst i)
  | waitableSetNew =>
    exact tab_withArgs0 (Builtins.Inv.waitableSetNew lim
      (tf_insts fun _ => rfl) fun inst _ s hs => hs.trans (tabMove_addHandle s inst _))
  | waitableSetWait mem =>
    exact tab_withArgs2 fun si p => Builtins.Inv.waitableSetWait lim mem
      si p (fun _ => tf_insts fun _ => rfl) (fun _ => tf_insts fun _ => rfl)
      (fun _ _ => tf_insts fun _ => rfl) (fun _ _ => tf_insts fun _ => rfl)
      (fun w => tf_insts (takeWaitableEventSt_insts w)) tf_memWrite
  | waitableSetPoll mem =>
    exact tab_withArgs2 fun si p => Builtins.Inv.waitableSetPoll lim mem
      si p (fun _ _ => tf_insts fun _ => rfl) (fun w => tf_insts (takeWaitableEventSt_insts w))
      tf_memWrite
  | waitableSetDrop =>
    exact tab_withArgs1 fun i => Builtins.Inv.waitableSetDrop lim i
      fun inst s hs => hs.trans (tabMove_removeHandle s inst i)
  | waitableJoin =>
    exact tab_withArgs2 fun wi si => Builtins.Inv.waitableJoin lim wi si
      fun w ws => tf_insts (joinSt_insts w ws)
  | threadIndex =>
    exact tab_withArgs0 Builtins.P.Inv.threadIndex
  | threadNewIndirect tbl ft =>
    exact tab_threadNewIndirect tbl ft args
  | threadResumeLater =>
    exact tab_withArgs1 fun i => Builtins.P.Inv.threadResumeLater i
      fun _ => tf_insts fun _ => rfl
  | threadSuspend =>
    exact tab_withArgs0 Builtins.P.Inv.threadSuspend
  | threadYield =>
    exact tab_withArgs0 (Builtins.P.Inv.threadYield fun _ => tf_insts fun _ => rfl)
  | threadSuspendThenResume =>
    exact tab_withArgs1 fun i =>
      Builtins.P.Inv.threadSuspendThenResume i
  | threadYieldThenResume =>
    exact tab_withArgs1 fun i => Builtins.P.Inv.threadYieldThenResume i
      fun _ => tf_insts fun _ => rfl
  | threadSuspendThenPromote =>
    exact tab_withArgs1 fun i =>
      Builtins.P.Inv.threadSuspendThenPromote hr q i fun _ => tf_insts fun _ => rfl
  | threadYieldThenPromote =>
    exact tab_withArgs1 fun i =>
      Builtins.P.Inv.threadYieldThenPromote hr q i (fun _ => tf_insts fun _ => rfl)
        (fun _ => tf_insts fun _ => rfl)

/-! ## The arms of the dispatcher -/

variable {host : HostImpl E σ}

theorem tab_calloutBody (hh : TabHost j host) (lim : Limits) (q : Quirks) (hr : HostReady σ)
    (s : CStore E) (th : Option ThreadId) (h : CanonHost E) (args : List FlatValue) :
    TI (calloutBody lim q hr host s th h args) := by
  unfold calloutBody
  cases h with
  | lowered callee ft opts inst =>
    exact P.Inv.bind (P.Inv.canonLower lowerPres_tab lim q callee ft opts inst args) fun _ =>
      P.Inv.pure _
  | builtin b _ => exact P.Inv.bind (tab_builtinProg lim q hr b args) fun _ => P.Inv.pure _
  | embedder name ft =>
    dsimp only
    split
    · exact P.Inv.bind (hh.embedder name ft args s₀) fun _ => P.Inv.pure _
    · exact P.Inv.bind (P.Inv.confine _ _) fun _ => P.Inv.pure _

theorem tab_hostCalloutProg (hh : TabHost j host) (lim : Limits) (q : Quirks) (hr : HostReady σ)
    (h : CanonHost E) (args : List FlatValue) : TI (hostCalloutProg lim q hr host h args) := by
  rw [hostCalloutProg_eq]
  unfold withCalloutEntry
  refine P.Inv.bind P.Inv.currentThread fun th => P.Inv.bind P.Inv.getStore fun s => ?_
  split
  · exact P.Inv.trap _
  · exact tab_calloutBody hh lim q hr s th h args

theorem tab_funcInstProg (hh : TabHost j host) (lim : Limits) (q : Quirks) (f : FuncId)
    (caller : CallerId) : TI (funcInstProg lim q host f caller) := by
  unfold funcInstProg
  refine P.Inv.bind (P.Inv.getObj _ _) fun fi => ?_
  cases fi with
  | lifted core ft opts inst => exact P.Inv.canonLift liftHyps_tab lim q core ft opts inst caller
  | host _ fn => exact hh.funcs fn caller s₀

theorem tab_callerOnStart (lim : Limits) (q : Quirks) (c : CallerId) :
    TI (callerOnStart (σ := σ) lim q c) := by
  unfold callerOnStart
  refine P.Inv.bind (P.Inv.getObj _ _) fun cr => ?_
  split
  · dsimp only
    split
    · exact P.Inv.bind (P.Inv.emit _) fun _ => P.Inv.pure _
    · exact P.Inv.pure _
  · exact P.Inv.bind (P.Inv.lowerOnStart lowerPres_tab lim q c) fun _ => P.Inv.pure _
  · exact P.Inv.pure _
  · exact P.Inv.onStartProg c

theorem tab_callerOnResolve (lim : Limits) (q : Quirks) (c : CallerId) (r : Option (List Val)) :
    TI (callerOnResolve (σ := σ) lim q c r) := by
  unfold callerOnResolve
  refine P.Inv.bind (P.Inv.getObj _ _) fun cr => ?_
  split
  · dsimp only
    split
    · exact P.Inv.bind (P.Inv.emit _) fun _ => P.Inv.pure _
    · exact P.Inv.pure _
  · exact P.Inv.bind (P.Inv.lowerOnResolve lowerPres_tab lim q c r) fun _ => P.Inv.pure _
  · exact P.Inv.bind (P.Inv.modifyObj _ _ _ (tf_insts fun _ => rfl)) fun _ => P.Inv.pure _
  · exact P.Inv.onResolveProg liftHyps_tab c r

theorem tab_onCancelProg (hh : TabHost j host) (hr : HostReady σ) (r : CancelRef) :
    TI (onCancelProg hr host r) := by
  cases r with
  | task t =>
    exact P.Inv.bind (Task.requestCancellation_inv hr t invHyps_tab) fun _ => P.Inv.pure _
  | host n => exact P.Inv.bind (hh.cancel n s₀) fun _ => P.Inv.pure _
  | none => exact P.Inv.pure _

theorem tab_threadBodyProg (hh : TabHost j host) (lim : Limits) (q : Quirks) (b : ThreadBody E) :
    TI (threadBodyProg lim q host b) := by
  cases b with
  | liftImplicit task callee => exact P.Inv.liftThreadBody liftHyps_tab lim q task callee
  | newIndirect task f c =>
    exact P.Inv.bind (P.Inv.callCore _ _) fun _ => P.Inv.bind P.Inv.currentThreadId fun t =>
      P.Inv.bind (Task.unregisterThread_inv task t (tf_unregisterThread task t)) fun _ =>
        P.Inv.pure _
  | host fn task => exact hh.threadBody fn task s₀
  | liftNoop task => exact P.Inv.liftNoopThreadBody liftHyps_tab lim q task

theorem tab_loopProg (lim : Limits) (hr : HostReady σ) (l : LoopPoint E) :
    TI (loopProg lim hr l) := by
  cases l with
  | syncLiftLoop task => exact P.Inv.syncLiftLoopBody liftHyps_tab hr task
  | callbackLoop task thread code si =>
    exact P.Inv.callbackLoopBody liftHyps_tab lim task thread code si

theorem tab_hostInvokeProg (f : FuncId) (args : List Val) :
    TI (hostInvokeProg (E := E) (σ := σ) f args) :=
  P.Inv.bind (P.Inv.allocObj _ _ (tf_insts fun _ => rfl)) fun _ =>
    P.Inv.bind (P.Inv.modifyStore (tf_insts fun _ => rfl)) fun _ =>
      P.Inv.bind (P.Inv.callCancel _) fun _ =>
        P.Inv.bind (P.Inv.modifyStore (tf_insts fun _ => rfl)) fun _ =>
          P.Inv.bind (P.Inv.getObj _ _) fun _ => P.Inv.pure _

theorem tab_hostCancelProg (r : CancelRef) : TI (hostCancelProg (E := E) (σ := σ) r) :=
  P.Inv.bind (P.Inv.modifyStore (tf_insts fun _ => rfl)) fun _ =>
    P.Inv.bind (P.Inv.callUnit _) fun _ =>
      P.Inv.bind (P.Inv.modifyStore (tf_insts fun _ => rfl)) fun _ => P.Inv.pure _

/-! ## Instantiation -/

section Instantiation

open Silmaril.Wasm.Component.Instantiate

theorem tab_need {α : Type} (w : String) (o : Option α) : TI (need (E := E) (σ := σ) w o) :=
  P.Inv.orTrap _ _

theorem tab_pushEntry (f : Frame E) (so : Syntax.Sort_) (e : Entry E) :
    TI (pushEntry (σ := σ) f so e) := tab_need _ _

theorem tab_allocInst : TI (allocInst (E := E) (σ := σ)) :=
  P.Inv.allocObj _ _ (tabFrom_of_move fun s => tabMove_allocInst s rfl)

theorem tab_allocCoreHost (h : CanonHost E) : TI (allocCoreHost (σ := σ) h) :=
  P.Inv.bind P.Inv.getStore fun _ =>
    P.Inv.bind (P.Inv.modifyStore (tf_insts fun _ => rfl)) fun _ => P.Inv.pure _

theorem tab_runStart (inst : InstId) (sf : E.FuncAddr) : TI (runStart (σ := σ) inst sf) :=
  P.Inv.bind (P.Inv.allocObj _ _ (tf_insts fun _ => rfl)) fun _ =>
    P.Inv.bind (P.Inv.allocObj _ _ (tf_insts fun _ => rfl)) fun _ =>
      P.Inv.bind (P.Inv.callCancel _) fun _ => P.Inv.pure _

theorem tab_checkImport (r : Except String Unit) : TI (checkImport (E := E) (σ := σ) r) := by
  cases r with
  | ok u => exact P.Inv.pure _
  | error e => exact P.Inv.trap _

/-- Push an entry and return the scope. -/
theorem tab_push (f : Frame E) (so : Syntax.Sort_) (e : Entry E) (k : Frame E → Scope E) :
    TI (pushEntry (σ := σ) f so e >>= fun f' => (pure (k f') : P E σ (Scope E))) :=
  P.Inv.bind (tab_pushEntry _ _ _) fun _ => P.Inv.pure _

variable [∀ a b, Decidable (E.ExternSub a b)]

theorem tab_instantiateCore (inst : InstId) (f : Frame E) (m : ℕ) (args : List (String × ℕ)) :
    TI (instantiateCore (σ := σ) inst f m args) := by
  refine P.Inv.bind (tab_need _ _) fun md => P.Inv.bind P.Inv.getStore fun s =>
    P.Inv.bind (tab_need _ _) fun imports => ?_
  rcases E.prepare? s.core md imports with _ | ⟨core', ci, start⟩
  · exact P.Inv.trap _
  · refine P.Inv.bind (P.Inv.modifyStore (tf_insts fun _ => rfl)) fun _ => ?_
    rcases start with _ | sf
    · exact P.Inv.bind (P.Inv.pure _) fun _ => P.Inv.pure _
    · exact P.Inv.bind (tab_runStart _ _) fun _ => P.Inv.pure _

theorem tab_instantiateDef_coreInstance {recurse : Recurse E σ} (inst : InstId)
    (outer : List (Frame E)) (args : Exports E) (sc : Scope E) (e : Syntax.CoreInstanceExpr) :
    TI (instantiateDef recurse inst outer args sc (.coreInstance e)) := by
  cases e with
  | instantiate m cargs => exact P.Inv.bind (tab_instantiateCore ..) fun _ => tab_push ..
  | exports items => exact P.Inv.bind (tab_need _ _) fun _ => tab_push ..

theorem tab_instantiateDef_instance {recurse : Recurse E σ} (hrec : ∀ c a, TI (recurse c a))
    (inst : InstId) (outer : List (Frame E)) (args : Exports E) (sc : Scope E)
    (e : Syntax.InstanceExpr) : TI (instantiateDef recurse inst outer args sc (.instance_ e)) := by
  cases e with
  | instantiate c iargs =>
    exact P.Inv.bind (tab_need _ _) fun cl => P.Inv.bind (tab_need _ _) fun vs =>
      P.Inv.bind (hrec cl vs) fun _ => tab_push ..
  | exports items => exact P.Inv.bind (tab_need _ _) fun _ => tab_push ..

theorem tab_instantiateDef_alias {recurse : Recurse E σ} (inst : InstId)
    (outer : List (Frame E)) (args : Exports E) (sc : Scope E) (a : Syntax.Alias) :
    TI (instantiateDef recurse inst outer args sc (.alias a)) := by
  cases a with
  | export_ i name so =>
    exact P.Inv.bind (tab_need _ _) fun _ => P.Inv.bind (tab_need _ _) fun _ => tab_push ..
  | coreExport i name so =>
    exact P.Inv.bind (tab_need _ _) fun _ => P.Inv.bind (tab_need _ _) fun _ =>
      P.Inv.bind (tab_need _ _) fun _ => tab_push ..
  | outer ct idx so =>
    exact P.Inv.bind (tab_need _ _) fun _ => P.Inv.bind (tab_need _ _) fun _ => tab_push ..

theorem tab_instantiateDef_type {recurse : Recurse E σ} (inst : InstId)
    (outer : List (Frame E)) (args : Exports E) (sc : Scope E) (t : Syntax.DefType) :
    TI (instantiateDef recurse inst outer args sc (.type t)) := by
  cases t with
  | resource rep dtor =>
    refine P.Inv.bind ?_ fun _ =>
      P.Inv.bind (P.Inv.allocObj _ _ (tf_insts fun _ => rfl)) fun _ => tab_push ..
    cases dtor
    · exact P.Inv.pure _
    · exact P.Inv.map (tab_need _ _)
  | _ => exact P.Inv.bind (tab_need _ _) fun _ => tab_push ..

theorem tab_instantiateDef_canon {recurse : Recurse E σ} (inst : InstId)
    (outer : List (Frame E)) (args : Exports E) (sc : Scope E) (c : Syntax.Canon) :
    TI (instantiateDef recurse inst outer args sc (.canon c)) := by
  cases c with
  | lift cf opts ft =>
    exact P.Inv.bind (tab_need _ _) fun _ =>
      P.Inv.bind (P.Inv.allocObj _ _ (tf_insts fun _ => rfl)) fun _ => tab_push ..
  | lower g opts =>
    exact P.Inv.bind (tab_need _ _) fun _ => P.Inv.bind (P.Inv.getObj _ _) fun _ =>
      P.Inv.bind (tab_allocCoreHost _) fun _ => tab_push ..
  | builtin b =>
    exact P.Inv.bind P.Inv.getStore fun _ => P.Inv.bind (tab_need _ _) fun _ =>
      P.Inv.bind (tab_allocCoreHost _) fun _ => tab_push ..

/-- Every definition of a component instantiates by table moves. -/
theorem tab_instantiateDef {recurse : Recurse E σ} (hrec : ∀ c a, TI (recurse c a))
    (inst : InstId) (outer : List (Frame E)) (args : Exports E) (sc : Scope E)
    (d : Syntax.Definition E.Module) : TI (instantiateDef recurse inst outer args sc d) := by
  cases d with
  | coreModule m => exact tab_push ..
  | coreType t => exact P.Inv.pure _
  | component defs => exact tab_push ..
  | import_ n d =>
    exact P.Inv.bind (P.Inv.orTrap _ _) fun _ => P.Inv.bind P.Inv.getStore fun _ =>
      P.Inv.bind (tab_checkImport _) fun _ => tab_push ..
  | coreInstance e => exact tab_instantiateDef_coreInstance inst outer args sc e
  | instance_ e => exact tab_instantiateDef_instance hrec inst outer args sc e
  | «alias» a => exact tab_instantiateDef_alias inst outer args sc a
  | type t => exact tab_instantiateDef_type inst outer args sc t
  | canon c => exact tab_instantiateDef_canon inst outer args sc c
  | start _ _ _ => exact P.Inv.internal _
  | value _ _ => exact P.Inv.internal _
  | export_ n si _ =>
    exact P.Inv.bind (tab_need _ _) fun _ => P.Inv.bind (tab_need _ _) fun _ =>
      P.Inv.bind (tab_pushEntry _ _ _) fun _ => P.Inv.pure _

theorem tab_instantiateComponent {recurse : Recurse E σ} (hrec : ∀ c a, TI (recurse c a))
    (c : Closure E) (args : Exports E) (inst : InstId) :
    TI (instantiateComponent recurse c args inst) :=
  P.Inv.bind (P.Inv.listFoldlM fun sc d _ => tab_instantiateDef hrec inst c.outer args sc d)
    fun _ => P.Inv.pure _

theorem tab_instantiateClosure (c : Closure E) (args : Exports E) :
    TI (instantiateClosure (σ := σ) callRecurse c args) :=
  P.Inv.bind tab_allocInst fun inst =>
    tab_instantiateComponent (fun _ _ => P.Inv.callItems _) c args inst

/-- **Root instantiation is table-moving.** -/
theorem tabProg_instantiateProg (c : Syntax.Component E.Module) (args : Exports E) :
    TabProg j (instantiateProg (σ := σ) c args) := fun _ =>
  P.Inv.bind (P.Inv.modifyStore (tf_insts fun _ => rfl)) fun _ =>
    P.Inv.bind (P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.bind P.Inv.getStore fun _ =>
      P.Inv.bind (tab_checkImport _) fun _ => P.Inv.bind tab_allocInst fun inst =>
        P.Inv.bind (tab_instantiateComponent (fun _ _ => P.Inv.callItems _) _ args inst)
          fun _ => P.Inv.pure _) fun _ =>
      P.Inv.bind (P.Inv.modifyStore (tf_insts fun _ => rfl)) fun _ =>
        P.Inv.bind (P.Inv.emit _) fun _ => P.Inv.pure _

end Instantiation

/-! ## The dispatcher -/

/-- **The reference dispatcher is table-moving**: every program it runs (canon lift and lower,
the loops and thread bodies, every canon built-in, caller records, nested invokes and
cancellations, nested instantiation) moves every handle table by a successful history, given
that the host's own programs do. -/
theorem tabDispatch_canon [∀ a b, Decidable (E.ExternSub a b)] (hh : TabHost j host)
    (lim : Limits) (q : Quirks) (hr : HostReady σ) : TabDispatch j (dispatch lim q hr host) := by
  intro c s₀
  cases c with
  | reallocate cx old oldLen align newLen =>
    exact P.Inv.reallocProg liftHyps_tab lim q cx old oldLen align newLen
  | funcInst f caller => exact tab_funcInstProg hh lim q f caller
  | onStart c => exact tab_callerOnStart lim q c
  | onResolve c r => exact tab_callerOnResolve lim q c r
  | onCancel r => exact tab_onCancelProg hh hr r
  | hostCallout h args => exact tab_hostCalloutProg hh lim q hr h args
  | threadBody b => exact tab_threadBodyProg hh lim q b
  | loop l => exact tab_loopProg lim hr l
  | hostFunc fn caller => exact hh.funcs fn caller s₀
  | hostBuffer op => exact hh.buffer op s₀
  | hostInvoke f args => exact tab_hostInvokeProg f args
  | hostCancel r => exact tab_hostCancelProg r
  | instantiate c args => exact P.Inv.bind (tab_instantiateClosure c args) fun _ => P.Inv.pure _

/-- The host without functions is table-moving. -/
theorem tabHost_none : TabHost j (HostImpl.none : HostImpl E σ) where
  funcs _ _ _ := P.Inv.internal _
  embedder _ _ _ _ := P.Inv.trap _
  threadBody _ _ _ := P.Inv.internal _
  buffer _ _ := P.Inv.internal _
  cancel _ _ := P.Inv.pure _

end Silmaril.Wasm.Resource
