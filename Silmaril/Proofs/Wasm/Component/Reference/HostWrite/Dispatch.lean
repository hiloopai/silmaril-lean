module

public import Silmaril.Proofs.Wasm.Component.Reference.HostWrite.Prog
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs

/-!
# Host-safe programs: the reference dispatcher

**`hostSafe_dispatch`**: every program of the reference dispatcher `Canon.dispatch lim q hr host`
is host-safe (`HostSafe Ext none`) for every `Ext`, for a host whose own programs are
(`HostImplSafe`). The proof follows the structure of the table frame argument
(`Silmaril.Proofs.Wasm.Resource.MachineTab.Dispatch`): it instantiates the `P.InvW` lemmas of
the reference programs (`canon_lift`, `canon_lower`, the loops, every canon built-in, the caller
records, nested instantiation) at the trivial store invariant `TT` and at the host-write
constraint `fun _ => False`, so that their store-update hypotheses hold trivially and their
conclusion says that the program never writes the host state (`HostSafe.of_invW`). The arms that
run host programs (host functions, embedder imports, host thread bodies, buffers and
cancellation hooks) are host-safe by `HostImplSafe`.

**`hostImplSafe_answerLog`**: the logging answering host `answerImplS (HLinked2.logG g)` is
host-safe for `logExt`: its host function reads the host state `s` and, as its next operation,
writes `(s₁, s.2 ++ [e])`, whose log strictly extends `s.2`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HostWrite

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type}

/-- The trivial store invariant. -/
abbrev TT : CStore E → Prop := fun _ => True

/-! ## The store-update hypotheses at `TT` -/

theorem tf_insts' {g : CStore E → CStore E} : ∀ s, (TT : CStore E → Prop) s → TT (g s) :=
  fun _ _ => trivial

theorem tf_frame {i : InstId} {g : InstState → InstState}
    (_hg : ∀ st, (g st).handles = st.handles) :
    ∀ s, (TT : CStore E → Prop) s → TT (ArenaField.insts.modify s i g) := fun _ _ => trivial

theorem tf_addHandle : P.Inv.AddHandlePres (TT : CStore E → Prop) := by (repeat intro); trivial

theorem tf_removeHandle : P.Inv.RemoveHandlePres (TT : CStore E → Prop) := by (repeat intro); trivial

theorem tf_unregisterThread (task : TaskId) (t : ThreadId) (i : ℕ) :
    ∀ s, (TT : CStore E → Prop) s → TT (CStore.unregisterThreadSt (E := E) task t i s) :=
  fun _ _ => trivial

theorem invHyps_tab : Task.InvHyps (TT : CStore E → Prop) := by
  constructor <;> (repeat intro) <;> trivial

theorem loadPres_tab : P.Inv.LoadPres (TT : CStore E → Prop) := by
  constructor <;> (repeat intro) <;> trivial

theorem storePres_tab : P.Inv.StorePres (TT : CStore E → Prop) := by
  constructor <;> (repeat intro) <;> trivial

theorem liftHyps_tab : LiftHyps (TT : CStore E → Prop) := by
  constructor <;> first | exact invHyps_tab | exact loadPres_tab | exact storePres_tab |
    ((repeat intro); trivial)

theorem lowerPres_tab : P.Inv.LowerPres (TT : CStore E → Prop) := by
  constructor <;> first | exact loadPres_tab | exact storePres_tab | ((repeat intro); trivial)

theorem awaitPres_tab : Builtins.Inv.AwaitPres (TT : CStore E → Prop) := by
  constructor <;> (repeat intro) <;> trivial

/-! ## Built-ins -/

local notation "TI" => P.InvW (TT : CStore E → Prop) (fun _ : σ => False)

theorem ns_withArgs0 {α : Type} {args : List FlatValue} {k : P E σ α} (hk : TI k) :
    TI (withArgs0 args k) := by
  unfold withArgs0; split
  · exact hk
  · exact P.Inv.internal _

theorem ns_withArgs1 {α : Type} {args : List FlatValue} {k : ℕ → P E σ α} (hk : ∀ n, TI (k n)) :
    TI (withArgs1 args k) := by
  unfold withArgs1; split
  · exact hk _
  · exact P.Inv.internal _

theorem ns_withArgs2 {α : Type} {args : List FlatValue} {k : ℕ → ℕ → P E σ α}
    (hk : ∀ a b, TI (k a b)) : TI (withArgs2 args k) := by
  unfold withArgs2; split
  · exact hk _ _
  · exact P.Inv.internal _

theorem ns_withArgs3 {α : Type} {args : List FlatValue} {k : ℕ → ℕ → ℕ → P E σ α}
    (hk : ∀ a b c, TI (k a b c)) : TI (withArgs3 args k) := by
  unfold withArgs3; split
  · exact hk _ _ _
  · exact P.Inv.internal _

theorem ns_newBuiltin (lim : Silmaril.Wasm.Component.Limits) (k : Silmaril.Wasm.Component.AsyncRef.EndKind) (t : Option (WIT.ClosedType RtId)) :
    TI (Builtins.newBuiltin (σ := σ) lim k t) :=
  Builtins.Inv.newBuiltin tf_addHandle (fun _ _ _ => tf_insts')
    (fun _ _ => tf_insts') lim k t

theorem ns_copyBuiltin (lim : Silmaril.Wasm.Component.Limits) (q : Quirks) (k : Silmaril.Wasm.Component.AsyncRef.EndKind)
    (t : Option (WIT.ClosedType RtId)) (opts : CanonOpts E) (i p n : ℕ) :
    TI (Builtins.copyBuiltin (σ := σ) lim q k t opts i p n) :=
  Builtins.Inv.copyBuiltin loadPres_tab storePres_tab awaitPres_tab
    (fun _ _ _ => tf_insts') lim q k t opts i p n

theorem ns_cancelCopy (lim : Silmaril.Wasm.Component.Limits) (k : Silmaril.Wasm.Component.AsyncRef.EndKind) (t : Option (WIT.ClosedType RtId))
    (a : Bool) (i : ℕ) : TI (Builtins.cancelCopy (σ := σ) lim k t a i) :=
  Builtins.Inv.cancelCopy awaitPres_tab (fun _ _ => tf_insts') lim k t a i

theorem ns_dropEnd (lim : Silmaril.Wasm.Component.Limits) (k : Silmaril.Wasm.Component.AsyncRef.EndKind) (t : Option (WIT.ClosedType RtId))
    (i : ℕ) : TI (Builtins.dropEnd (σ := σ) lim k t i) :=
  Builtins.Inv.dropEnd tf_removeHandle (fun _ => tf_insts') lim k t i

theorem ns_forwardBuiltin (lim : Silmaril.Wasm.Component.Limits) (q : Quirks) (k : Silmaril.Wasm.Component.AsyncRef.EndKind)
    (t : Option (WIT.ClosedType RtId)) (ri wi : ℕ) :
    TI (Builtins.forwardBuiltin (σ := σ) lim q k t ri wi) :=
  Builtins.Inv.forwardBuiltin loadPres_tab storePres_tab tf_removeHandle
    (fun _ _ => tf_insts') lim q k t ri wi

theorem ns_threadNewIndirect (tbl : E.TableAddr) (ft : Silmaril.Wasm.V1.FuncType) (args : List FlatValue) :
    TI (match args with
      | [fi, c] => Builtins.threadNewIndirect (σ := σ) tbl ft (flatNat fi) c
      | _ => internal "built-in: wrong number of arguments") := by
  split
  · exact Builtins.P.Inv.threadNewIndirect tbl ft _ _ fun _ _ _ _ => trivial
  · exact P.Inv.internal _

theorem ns_resourceDrop (lim : Silmaril.Wasm.Component.Limits) (q : Quirks) (rt : RtId) (i : ℕ) :
    TI (Builtins.resourceDrop (σ := σ) lim q (destructorCall lim q) rt i) :=
  Builtins.Inv.resourceDrop tf_removeHandle (fun _ => tf_insts') lim q (fun inst req => P.Inv.destructorCall liftHyps_tab lim q inst req) rt i

/-- **Every canon built-in never writes the host state.** -/
theorem ns_builtinProg (lim : Silmaril.Wasm.Component.Limits) (q : Quirks) (hr : HostReady σ) (b : ResolvedBuiltin E)
    (args : List FlatValue) : TI (builtinProg lim q hr b args) := by
  cases b with
  | resourceNew rt _ =>
    exact ns_withArgs1 fun rep =>
      Builtins.Inv.resourceNew (fun s _ => tf_insts' s) tf_addHandle lim rt rep
  | resourceDrop rt =>
    exact ns_withArgs1 fun i => ns_resourceDrop lim q rt i
  | resourceRep rt _ =>
    exact ns_withArgs1 fun i => Builtins.Inv.resourceRep lim rt i
  | backpressureInc =>
    exact ns_withArgs0 (Builtins.P.Inv.backpressureInc fun _ =>
      tf_frame fun _ => rfl)
  | backpressureDec =>
    exact ns_withArgs0 (Builtins.P.Inv.backpressureDec fun _ =>
      tf_frame fun _ => rfl)
  | taskReturn result opts =>
    exact Builtins.P.Inv.taskReturn loadPres_tab
      (fun _ => tf_insts') lim q result opts args
  | taskCancel =>
    exact ns_withArgs0 (Builtins.P.Inv.taskCancel fun _ => tf_insts')
  | contextGet t i =>
    exact ns_withArgs0 (Builtins.P.Inv.contextGet t i)
  | contextSet t i =>
    exact ns_withArgs1 fun v =>
      Builtins.P.Inv.contextSet t i v fun _ => tf_insts'
  | subtaskCancel a =>
    exact ns_withArgs1 fun i => Builtins.Inv.subtaskCancel lim a i
      (fun _ _ => tf_insts') (fun _ _ => tf_insts')
      (fun _ => tf_insts')
      (fun _ => tf_insts')
  | subtaskDrop =>
    exact ns_withArgs1 fun i => Builtins.Inv.subtaskDrop lim i
      (fun inst s hs => tf_removeHandle s inst i hs) (fun _ => tf_insts')
  | streamNew t =>
    exact ns_withArgs0 (ns_newBuiltin lim _ t)
  | streamRead t opts =>
    exact ns_withArgs3 fun i p n => ns_copyBuiltin lim q _ t opts i p n
  | streamWrite t opts =>
    exact ns_withArgs3 fun i p n => ns_copyBuiltin lim q _ t opts i p n
  | streamCancelRead t a =>
    exact ns_withArgs1 fun i => ns_cancelCopy lim _ t a i
  | streamCancelWrite t a =>
    exact ns_withArgs1 fun i => ns_cancelCopy lim _ t a i
  | streamDropReadable t =>
    exact ns_withArgs1 fun i => ns_dropEnd lim _ t i
  | streamDropWritable t =>
    exact ns_withArgs1 fun i => ns_dropEnd lim _ t i
  | streamForward t =>
    exact ns_withArgs2 fun ri wi => ns_forwardBuiltin lim q _ t ri wi
  | futureNew t =>
    exact ns_withArgs0 (ns_newBuiltin lim _ t)
  | futureRead t opts =>
    exact ns_withArgs2 fun i p => ns_copyBuiltin lim q _ t opts i p 1
  | futureWrite t opts =>
    exact ns_withArgs2 fun i p => ns_copyBuiltin lim q _ t opts i p 1
  | futureCancelRead t a =>
    exact ns_withArgs1 fun i => ns_cancelCopy lim _ t a i
  | futureCancelWrite t a =>
    exact ns_withArgs1 fun i => ns_cancelCopy lim _ t a i
  | futureDropReadable t =>
    exact ns_withArgs1 fun i => ns_dropEnd lim _ t i
  | futureDropWritable t =>
    exact ns_withArgs1 fun i => ns_dropEnd lim _ t i
  | futureForward t =>
    exact ns_withArgs2 fun ri wi => ns_forwardBuiltin lim q _ t ri wi
  | errorContextNew opts =>
    exact ns_withArgs2 fun p n => Builtins.P.Inv.errorContextNew lim q
      opts p n (fun _ => tf_insts') (fun _ _ _ _ => trivial)
  | errorContextDebugMessage opts =>
    exact ns_withArgs2 fun i p =>
      Builtins.P.Inv.errorContextDebugMessage lim q opts i p
  | errorContextDrop =>
    exact ns_withArgs1 fun i => Builtins.P.Inv.errorContextDrop i
      fun _ _ _ => trivial
  | waitableSetNew =>
    exact ns_withArgs0 (Builtins.Inv.waitableSetNew lim
      (tf_insts') fun _ _ _ _ => trivial)
  | waitableSetWait mem =>
    exact ns_withArgs2 fun si p => Builtins.Inv.waitableSetWait lim mem
      si p (fun _ => tf_insts') (fun _ => tf_insts')
      (fun _ _ => tf_insts') (fun _ _ => tf_insts')
      (fun _ => tf_insts')
  | waitableSetPoll mem =>
    exact ns_withArgs2 fun si p => Builtins.Inv.waitableSetPoll lim mem
      si p (fun _ _ => tf_insts') (fun _ => tf_insts')
  | waitableSetDrop =>
    exact ns_withArgs1 fun i => Builtins.Inv.waitableSetDrop lim i
      fun _ _ _ => trivial
  | waitableJoin =>
    exact ns_withArgs2 fun wi si => Builtins.Inv.waitableJoin lim wi si
      fun _ _ => tf_insts'
  | threadIndex =>
    exact ns_withArgs0 Builtins.P.Inv.threadIndex
  | threadNewIndirect tbl ft =>
    exact ns_threadNewIndirect tbl ft args
  | threadResumeLater =>
    exact ns_withArgs1 fun i => Builtins.P.Inv.threadResumeLater i
      fun _ => tf_insts'
  | threadSuspend =>
    exact ns_withArgs0 Builtins.P.Inv.threadSuspend
  | threadYield =>
    exact ns_withArgs0 (Builtins.P.Inv.threadYield fun _ => tf_insts')
  | threadSuspendThenResume =>
    exact ns_withArgs1 fun i =>
      Builtins.P.Inv.threadSuspendThenResume i
  | threadYieldThenResume =>
    exact ns_withArgs1 fun i => Builtins.P.Inv.threadYieldThenResume i
      fun _ => tf_insts'
  | threadSuspendThenPromote =>
    exact ns_withArgs1 fun i =>
      Builtins.P.Inv.threadSuspendThenPromote hr q i fun _ => tf_insts'
  | threadYieldThenPromote =>
    exact ns_withArgs1 fun i =>
      Builtins.P.Inv.threadYieldThenPromote hr q i (fun _ => tf_insts')
        (fun _ => tf_insts')

/-! ## Instantiation -/

section Instantiation

open Silmaril.Wasm.Component.Instantiate

theorem ns_need {α : Type} (w : String) (o : Option α) : TI (need (E := E) (σ := σ) w o) :=
  P.Inv.orTrap _ _

theorem ns_pushEntry (f : Frame E) (so : Syntax.Sort_) (e : Entry E) :
    TI (pushEntry (σ := σ) f so e) := ns_need _ _

theorem ns_allocInst : TI (allocInst (E := E) (σ := σ)) :=
  P.Inv.allocObj _ _ (fun _ _ => trivial)

theorem ns_allocCoreHost (h : CanonHost E) : TI (allocCoreHost (σ := σ) h) :=
  P.Inv.bind P.Inv.readCore fun _ =>
    P.Inv.bind (P.Inv.allocHostOp _ _) fun _ => P.Inv.pure _

theorem ns_runStart (inst : InstId) (sf : E.FuncAddr) : TI (runStart (σ := σ) inst sf) :=
  P.Inv.bind (P.Inv.allocObj _ _ (tf_insts')) fun _ =>
    P.Inv.bind (P.Inv.allocObj _ _ (tf_insts')) fun _ =>
      P.Inv.bind (P.Inv.callCancel _) fun _ => P.Inv.pure _

theorem ns_checkImport (r : Except String Unit) : TI (checkImport (E := E) (σ := σ) r) := by
  cases r with
  | ok u => exact P.Inv.pure _
  | error e => exact P.Inv.trap _

/-- Push an entry and return the scope. -/
theorem ns_push (f : Frame E) (so : Syntax.Sort_) (e : Entry E) (k : Frame E → Scope E) :
    TI (pushEntry (σ := σ) f so e >>= fun f' => (pure (k f') : P E σ (Scope E))) :=
  P.Inv.bind (ns_pushEntry _ _ _) fun _ => P.Inv.pure _

variable [∀ a b, Decidable (E.ExternSub a b)]

theorem ns_instantiateCore (inst : InstId) (f : Frame E) (m : ℕ) (args : List (String × ℕ)) :
    TI (instantiateCore (σ := σ) inst f m args) := by
  refine P.Inv.bind (ns_need _ _) fun md => P.Inv.bind P.Inv.readCore fun v =>
    P.Inv.bind (ns_need _ _) fun imports => ?_
  rcases v.prepare? md imports with _ | ⟨exports, start⟩
  · exact P.Inv.trap _
  · refine P.Inv.bind (P.Inv.prepareOp _ _) fun _ => ?_
    rcases start with _ | sf
    · exact P.Inv.bind (P.Inv.pure _) fun _ => P.Inv.pure _
    · exact P.Inv.bind (ns_runStart _ _) fun _ => P.Inv.pure _

theorem ns_instantiateDef_coreInstance {recurse : Recurse E σ} (inst : InstId)
    (outer : List (Frame E)) (args : Exports E) (sc : Scope E) (e : Syntax.CoreInstanceExpr) :
    TI (instantiateDef recurse inst outer args sc (.coreInstance e)) := by
  cases e with
  | instantiate m cargs => exact P.Inv.bind (ns_instantiateCore ..) fun _ => ns_push ..
  | exports items => exact P.Inv.bind (ns_need _ _) fun _ => ns_push ..

theorem ns_instantiateDef_instance {recurse : Recurse E σ} (hrec : ∀ c a, TI (recurse c a))
    (inst : InstId) (outer : List (Frame E)) (args : Exports E) (sc : Scope E)
    (e : Syntax.InstanceExpr) : TI (instantiateDef recurse inst outer args sc (.instance_ e)) := by
  cases e with
  | instantiate c iargs =>
    exact P.Inv.bind (ns_need _ _) fun cl => P.Inv.bind (ns_need _ _) fun vs =>
      P.Inv.bind (hrec cl vs) fun _ => ns_push ..
  | exports items => exact P.Inv.bind (ns_need _ _) fun _ => ns_push ..

theorem ns_instantiateDef_alias {recurse : Recurse E σ} (inst : InstId)
    (outer : List (Frame E)) (args : Exports E) (sc : Scope E) (a : Syntax.Alias) :
    TI (instantiateDef recurse inst outer args sc (.alias a)) := by
  cases a with
  | export_ i name so =>
    exact P.Inv.bind (ns_need _ _) fun _ => P.Inv.bind (ns_need _ _) fun _ => ns_push ..
  | coreExport i name so =>
    exact P.Inv.bind (ns_need _ _) fun _ => P.Inv.bind (ns_need _ _) fun _ =>
      P.Inv.bind (ns_need _ _) fun _ => ns_push ..
  | outer ct idx so =>
    exact P.Inv.bind (ns_need _ _) fun _ => P.Inv.bind (ns_need _ _) fun _ => ns_push ..

theorem ns_instantiateDef_type {recurse : Recurse E σ} (inst : InstId)
    (outer : List (Frame E)) (args : Exports E) (sc : Scope E) (t : Syntax.DefType) :
    TI (instantiateDef recurse inst outer args sc (.type t)) := by
  cases t with
  | resource rep dtor =>
    refine P.Inv.bind ?_ fun _ =>
      P.Inv.bind (P.Inv.allocObj _ _ (tf_insts')) fun _ => ns_push ..
    cases dtor
    · exact P.Inv.pure _
    · exact P.Inv.map (ns_need _ _)
  | _ => exact P.Inv.bind (ns_need _ _) fun _ => ns_push ..

theorem ns_instantiateDef_canon {recurse : Recurse E σ} (inst : InstId)
    (outer : List (Frame E)) (args : Exports E) (sc : Scope E) (c : Syntax.Canon) :
    TI (instantiateDef recurse inst outer args sc (.canon c)) := by
  cases c with
  | lift cf opts ft =>
    exact P.Inv.bind (ns_need _ _) fun _ =>
      P.Inv.bind (P.Inv.allocObj _ _ (tf_insts')) fun _ => ns_push ..
  | lower g opts =>
    exact P.Inv.bind (ns_need _ _) fun _ => P.Inv.bind (P.Inv.getObj _ _) fun _ =>
      P.Inv.bind (ns_allocCoreHost _) fun _ => ns_push ..
  | builtin b =>
    exact P.Inv.bind P.Inv.getStore fun _ => P.Inv.bind (ns_need _ _) fun _ =>
      P.Inv.bind (ns_allocCoreHost _) fun _ => ns_push ..

/-- No definition of a component writes the host state while it is instantiated. -/
theorem ns_instantiateDef {recurse : Recurse E σ} (hrec : ∀ c a, TI (recurse c a))
    (inst : InstId) (outer : List (Frame E)) (args : Exports E) (sc : Scope E)
    (d : Syntax.Definition E.Module) : TI (instantiateDef recurse inst outer args sc d) := by
  cases d with
  | coreModule m => exact ns_push ..
  | coreType t => exact P.Inv.pure _
  | component defs => exact ns_push ..
  | import_ n d =>
    exact P.Inv.bind (P.Inv.orTrap _ _) fun _ => P.Inv.bind P.Inv.getStore fun _ =>
      P.Inv.bind (ns_checkImport _) fun _ => ns_push ..
  | coreInstance e => exact ns_instantiateDef_coreInstance inst outer args sc e
  | instance_ e => exact ns_instantiateDef_instance hrec inst outer args sc e
  | «alias» a => exact ns_instantiateDef_alias inst outer args sc a
  | type t => exact ns_instantiateDef_type inst outer args sc t
  | canon c => exact ns_instantiateDef_canon inst outer args sc c
  | start _ _ _ => exact P.Inv.internal _
  | value _ _ => exact P.Inv.internal _
  | export_ n si _ =>
    exact P.Inv.bind (ns_need _ _) fun _ => P.Inv.bind (ns_need _ _) fun _ =>
      P.Inv.bind (ns_pushEntry _ _ _) fun _ => P.Inv.pure _

theorem ns_instantiateComponent {recurse : Recurse E σ} (hrec : ∀ c a, TI (recurse c a))
    (c : Closure E) (args : Exports E) (inst : InstId) :
    TI (instantiateComponent recurse c args inst) :=
  P.Inv.bind (P.Inv.listFoldlM fun sc d _ => ns_instantiateDef hrec inst c.outer args sc d)
    fun _ => P.Inv.pure _

theorem ns_instantiateClosure (c : Closure E) (args : Exports E) :
    TI (instantiateClosure (σ := σ) callRecurse c args) :=
  P.Inv.bind ns_allocInst fun inst =>
    ns_instantiateComponent (fun _ _ => P.Inv.callItems _) c args inst

/-- **Root instantiation never writes the host state.** -/
theorem nsProg_instantiateProg (c : Syntax.Component E.Module) (args : Exports E) :
    TI (instantiateProg (σ := σ) c args) :=
  P.Inv.bind (P.Inv.modifyStore (tf_insts')) fun _ =>
    P.Inv.bind (P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.bind P.Inv.getStore fun _ =>
      P.Inv.bind (ns_checkImport _) fun _ => P.Inv.bind ns_allocInst fun inst =>
        P.Inv.bind (ns_instantiateComponent (fun _ _ => P.Inv.callItems _) _ args inst)
          fun _ => P.Inv.pure _) fun _ =>
      P.Inv.bind (P.Inv.modifyStore (tf_insts')) fun _ =>
        P.Inv.bind (P.Inv.emit _) fun _ => P.Inv.pure _

end Instantiation


/-! ## The arms of the dispatcher that run host programs -/

variable {Ext : σ → σ → Prop} {host : HostImpl E σ}

theorem hs_calloutBody (hh : HostImplSafe Ext host) (lim : Silmaril.Wasm.Component.Limits)
    (q : Quirks) (hr : HostReady σ) (s : CStore E) (th : Option ThreadId) (h : CanonHost E)
    (args : List FlatValue) : HostSafe Ext none (calloutBody lim q hr host s th h args) := by
  unfold calloutBody
  cases h with
  | lowered callee ft opts inst =>
    exact HostSafe.of_invW (P.Inv.bind (P.Inv.canonLower lowerPres_tab lim q callee ft opts inst
      args) fun _ => P.Inv.pure _) none
  | builtin b _ =>
    exact HostSafe.of_invW (P.Inv.bind (ns_builtinProg lim q hr b args) fun _ => P.Inv.pure _)
      none
  | embedder name ft =>
    dsimp only
    split
    · exact (hh.embedder name ft args).bind fun _ => .pure _ _
    · exact (hh.embedder name ft args).confine.bind fun _ => .pure _ _

theorem hs_hostCalloutProg (hh : HostImplSafe Ext host) (lim : Silmaril.Wasm.Component.Limits)
    (q : Quirks) (hr : HostReady σ) (h : CanonHost E) (args : List FlatValue) :
    HostSafe Ext none (hostCalloutProg lim q hr host h args) := by
  rw [hostCalloutProg_eq]
  unfold withCalloutEntry
  refine (HostSafe.of_invW (P.Inv.currentThread (I := TT) (W := fun _ : σ => False)) none).bind
    fun th => (HostSafe.of_invW (P.Inv.getStore (I := TT) (W := fun _ : σ => False)) none).bind
      fun s => ?_
  split
  · exact HostSafe.of_invW (P.Inv.trap (I := TT) _) none
  · exact hs_calloutBody hh lim q hr s th h args

theorem hs_funcInstProg (hh : HostImplSafe Ext host) (lim : Silmaril.Wasm.Component.Limits)
    (q : Quirks) (f : FuncId) (caller : CallerId) :
    HostSafe Ext none (funcInstProg lim q host f caller) := by
  unfold funcInstProg
  refine (HostSafe.of_invW (P.Inv.getObj (I := TT) (W := fun _ : σ => False) _ _) none).bind
    fun fi => ?_
  cases fi with
  | lifted core ft opts inst =>
    exact HostSafe.of_invW (P.Inv.canonLift liftHyps_tab lim q core ft opts inst caller) none
  | host _ fn => exact hh.funcs fn caller

theorem ns_callerOnStart (lim : Silmaril.Wasm.Component.Limits) (q : Quirks) (c : CallerId) :
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

theorem ns_callerOnResolve (lim : Silmaril.Wasm.Component.Limits) (q : Quirks) (c : CallerId)
    (r : Option (List Silmaril.Wasm.Component.Value.Val)) :
    TI (callerOnResolve (σ := σ) lim q c r) := by
  unfold callerOnResolve
  refine P.Inv.bind (P.Inv.getObj _ _) fun cr => ?_
  split
  · dsimp only
    split
    · exact P.Inv.bind (P.Inv.emit _) fun _ => P.Inv.pure _
    · exact P.Inv.pure _
  · exact P.Inv.bind (P.Inv.lowerOnResolve lowerPres_tab lim q c r) fun _ => P.Inv.pure _
  · exact P.Inv.bind (P.Inv.modifyObj _ _ _ tf_insts') fun _ => P.Inv.pure _
  · exact P.Inv.onResolveProg liftHyps_tab c r

theorem hs_onCancelProg (hh : HostImplSafe Ext host) (hr : HostReady σ) (r : CancelRef) :
    HostSafe Ext none (onCancelProg hr host r) := by
  cases r with
  | task t =>
    exact HostSafe.of_invW (P.Inv.bind (Task.requestCancellation_inv hr t invHyps_tab) fun _ =>
      P.Inv.pure _) none
  | host n => exact (hh.cancel n).bind fun _ => .pure _ _
  | none => exact .pure _ _

theorem hs_threadBodyProg (hh : HostImplSafe Ext host) (lim : Silmaril.Wasm.Component.Limits)
    (q : Quirks) (b : ThreadBody E) : HostSafe Ext none (threadBodyProg lim q host b) := by
  cases b with
  | liftImplicit task callee =>
    exact HostSafe.of_invW (P.Inv.liftThreadBody liftHyps_tab lim q task callee) none
  | newIndirect task f c =>
    exact HostSafe.of_invW (P.Inv.bind (P.Inv.callCore _ _) fun _ =>
      P.Inv.bind P.Inv.currentThreadId fun t =>
        P.Inv.bind (Task.unregisterThread_inv task t (tf_unregisterThread task t)) fun _ =>
          P.Inv.pure _) none
  | host fn task => exact hh.threadBody fn task
  | liftNoop task => exact HostSafe.of_invW (P.Inv.liftNoopThreadBody liftHyps_tab lim q task) none

theorem ns_loopProg (lim : Silmaril.Wasm.Component.Limits) (hr : HostReady σ) (l : LoopPoint E) :
    TI (loopProg lim hr l) := by
  cases l with
  | syncLiftLoop task => exact P.Inv.syncLiftLoopBody liftHyps_tab hr task
  | callbackLoop task thread code si =>
    exact P.Inv.callbackLoopBody liftHyps_tab lim task thread code si

theorem ns_hostInvokeProg (f : FuncId) (args : List Silmaril.Wasm.Component.Value.Val) :
    TI (hostInvokeProg (E := E) (σ := σ) f args) :=
  P.Inv.bind (P.Inv.allocObj _ _ tf_insts') fun _ =>
    P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ =>
      P.Inv.bind (P.Inv.callCancel _) fun _ =>
        P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ =>
          P.Inv.bind (P.Inv.getObj _ _) fun _ => P.Inv.pure _

theorem ns_hostCancelProg (r : CancelRef) : TI (hostCancelProg (E := E) (σ := σ) r) :=
  P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ =>
    P.Inv.bind (P.Inv.callUnit _) fun _ =>
      P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ => P.Inv.pure _

/-! ## The dispatcher -/

/-- **Every program of the reference dispatcher is host-safe**, for a host-safe host: canon lift
and lower, the loops and thread bodies, every canon built-in, caller records, nested invokes and
cancellations and nested instantiation never write the host state; the host's own programs are
host-safe by hypothesis. -/
theorem hostSafe_dispatch [∀ a b, Decidable (E.ExternSub a b)] (hh : HostImplSafe Ext host)
    (lim : Silmaril.Wasm.Component.Limits) (q : Quirks) (hr : HostReady σ) :
    DispatchSafe Ext (dispatch lim q hr host) := by
  intro c
  cases c with
  | reallocate cx old oldLen align newLen =>
    exact HostSafe.of_invW (P.Inv.reallocProg liftHyps_tab lim q cx old oldLen align newLen) none
  | funcInst f caller => exact hs_funcInstProg hh lim q f caller
  | onStart c => exact HostSafe.of_invW (ns_callerOnStart lim q c) none
  | onResolve c r => exact HostSafe.of_invW (ns_callerOnResolve lim q c r) none
  | onCancel r => exact hs_onCancelProg hh hr r
  | hostCallout h args => exact hs_hostCalloutProg hh lim q hr h args
  | threadBody b => exact hs_threadBodyProg hh lim q b
  | loop l => exact HostSafe.of_invW (ns_loopProg lim hr l) none
  | hostFunc fn caller => exact hh.funcs fn caller
  | hostBuffer op => exact hh.buffer op
  | hostInvoke f args => exact HostSafe.of_invW (ns_hostInvokeProg f args) none
  | hostCancel r => exact HostSafe.of_invW (ns_hostCancelProg r) none
  | instantiate c args =>
    exact HostSafe.of_invW (P.Inv.bind (ns_instantiateClosure c args) fun _ => P.Inv.pure _) none

/-! ## Hosts -/

/-- A host given by host function programs is host-safe when they are. -/
theorem hostImplSafe_ofFns {fns : HostFuncId → CallerId → P E σ (Ret E)}
    (h : ∀ fn c, HostSafe Ext none (fns fn c)) : HostImplSafe Ext (HostImpl.ofFns fns) where
  funcs := h
  embedder _ _ _ := HostSafe.of_invW (P.Inv.trap (I := TT) _) none
  threadBody _ _ := HostSafe.of_invW (P.Inv.internal (I := TT) _) none
  buffer _ := HostSafe.of_invW (P.Inv.internal (I := TT) _) none
  cancel _ := .pure _ _

/-- **The stateful answering host is host-safe** for every relation that holds between the state
it reads and the state its answering function returns. -/
theorem hostImplSafe_answerImplS
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ))
    (hg : ∀ s fn args rs s', g s fn args = some (rs, s') → Ext s s') :
    HostImplSafe Ext (Silmaril.Wasm.Component.Reference.answerImplS g : HostImpl E σ) := by
  refine hostImplSafe_ofFns fun fn c =>
    (HostSafe.of_invW (P.Inv.callVals (I := TT) (W := fun _ : σ => False) _) none).bind
      fun args => .get none fun s => ?_
  change HostSafe Ext (some s) (match g s fn args with
    | some (rs, s') => Prog.bind (hostSet s') fun _ =>
        Prog.bind (callUnit (Call.onResolve c (some rs))) fun _ =>
          (pure (Ret.cancel CancelRef.none) : P E σ (Ret E))
    | none => (trap (TrapReason.hostTrap "answerImpl: no answer") : P E σ (Ret E)))
  rcases hgs : g s fn args with _ | ⟨rs, s'⟩
  · exact HostSafe.of_invW (P.Inv.trap (I := TT) _) _
  · exact .set (hg s fn args rs s' hgs) (HostSafe.of_invW (P.Inv.bind (P.Inv.callUnit
      (I := TT) (W := fun _ : σ => False) _) fun _ => P.Inv.pure _) none)

/-- **The logging host is host-safe for `logExt`**: every answered host call appends one event to
the log. -/
theorem hostImplSafe_answerLog {σ₀ : Type}
    (g : σ₀ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ₀)) :
    HostImplSafe (E := E) Silmaril.Wasm.Component.Reference.logExt
      (Silmaril.Wasm.Component.Reference.answerImplS
        (Silmaril.Wasm.Component.Reference.HLinked2.logG g)) := by
  refine hostImplSafe_answerImplS _ fun s fn args rs s' h => ?_
  simp only [Silmaril.Wasm.Component.Reference.HLinked2.logG, Option.map_eq_some_iff,
    Prod.mk.injEq] at h
  obtain ⟨⟨rs', t⟩, -, rfl, rfl⟩ := h
  exact ⟨List.prefix_append _ _, by simp⟩

end Silmaril.Proofs.Wasm.Component.Reference.HostWrite
