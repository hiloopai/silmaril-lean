module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Stream.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.StreamOps.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Load.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Store.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.StreamOps.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Builtins.Stream`: laws of the component reference

Theorems of the component reference copy `Canon.Builtins.Stream`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Builtins.Stream`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Async
variable {E : CoreEngine} {σ : Type}

namespace Inv

variable {I : CStore E → Prop}

theorem endMayLeave (inst : InstId) : P.Inv I (Builtins.endMayLeave inst : P E σ Unit) :=
  P.Inv.bind (P.Inv.getInst inst) fun _ => P.Inv.trapIf _ _

theorem expectEnd (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (ent : HandleEntry) :
    P.Inv I (Builtins.expectEnd kind t ent : P E σ (EndId × End E)) := by
  unfold Builtins.expectEnd
  split
  · exact P.Inv.bind (P.Inv.getObj _ _) fun _ => P.Inv.bind (P.Inv.trapIf _ _) fun _ =>
      P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.pure _
  · exact P.Inv.trap _

theorem checkCopyIdle (kind : EndKind) (st : EndState) :
    P.Inv I (Builtins.checkCopyIdle kind st : P E σ Unit) := by
  cases st <;> first | exact P.Inv.pure _ | exact P.Inv.trap _

theorem copyResultFlat (kind : EndKind) (cx : LiftLowerContext E) (payload : Nat) :
    P.Inv I (Builtins.copyResultFlat kind cx payload : P E σ (List FlatValue)) := by
  unfold Builtins.copyResultFlat
  exact P.Inv.ite (P.Inv.bind (P.Inv.ptrType _) fun _ => P.Inv.pure _) (P.Inv.pure _)

theorem awaitEndEvent (h : AwaitPres I) (site : WaitSite) (async_ : Bool) (e : EndId)
    {res : Nat → P E σ (List FlatValue)} (hr : ∀ p, P.Inv I (res p)) :
    P.Inv I (Builtins.awaitEndEvent site async_ e res) := by
  unfold Builtins.awaitEndEvent
  refine P.Inv.bind (Waitable.hasPendingEvent_inv _) fun _ => ?_
  have hg : P.Inv I (do
      let ev ← Waitable.getPendingEvent (E := E) (σ := σ) (.end_ e)
      res ev.payload) :=
    P.Inv.bind (Waitable.getPendingEvent_inv (h.takeEvent _)) fun _ => hr _
  exact P.Inv.ite hg (P.Inv.ite (hr _) (P.Inv.bind (Waitable.waitForPendingEvent_inv site
      (h.syncWaiter _) (h.startWaiting · _)) fun _ => hg))

theorem newBuiltin (hA : P.Inv.AddHandlePres I)
    (hN : ∀ k t o s, I s → I (newEndsSt (E := E) k t o s))
    (hI : ∀ e i s, I s → I (HandleSt.setEndIndex (E := E) e i s)) (lim : Limits)
    (k : EndKind) (t : Option (WIT.ClosedType RtId)) :
    P.Inv I (Builtins.newBuiltin lim k t : P E σ (List FlatValue)) :=
  P.Inv.bind P.Inv.currentInst fun _ => P.Inv.bind (endMayLeave _) fun _ =>
    P.Inv.bind P.Inv.getStore fun _ => P.Inv.bind (P.Inv.modifyStore (hN _ _ _)) fun _ =>
    P.Inv.bind (P.Inv.handlesAdd _ _ fun s hs => hA s _ ⟨_, NotSubtaskEntry.end_ _⟩ hs) fun _ =>
    P.Inv.bind (P.Inv.modifyStore (hI _ _)) fun _ =>
    P.Inv.bind (P.Inv.handlesAdd _ _ fun s hs => hA s _ ⟨_, NotSubtaskEntry.end_ _⟩ hs) fun _ =>
    P.Inv.bind (P.Inv.modifyStore (hI _ _)) fun _ => P.Inv.pure _

theorem cancelCopy (h : AwaitPres I) (hc : ∀ e b s, I s → I (cancel (E := E) e b s))
    (lim : Limits) (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (async_ : Bool)
    (i : Nat) :
    P.Inv I (Builtins.cancelCopy lim kind t async_ i : P E σ (List FlatValue)) :=
  P.Inv.bind P.Inv.currentInst fun _ => P.Inv.bind (endMayLeave _) fun _ =>
    P.Inv.bind (P.Inv.handlesGet _ _) fun _ => P.Inv.bind (expectEnd _ _ _) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.bind (P.Inv.trapIf _ _) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.bind (endCancel_inv (hc _)) fun _ =>
    awaitEndEvent h _ _ _ fun _ => P.Inv.pure _

theorem dropEnd (hR : P.Inv.RemoveHandlePres I)
    (hd : ∀ e s, I s → I (Runtime.dropEnd (E := E) e s))
    (lim : Limits) (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (i : Nat) :
    P.Inv I (Builtins.dropEnd lim kind t i : P E σ (List FlatValue)) :=
  P.Inv.bind P.Inv.currentInst fun _ => P.Inv.bind (endMayLeave _) fun _ =>
    P.Inv.bind (P.Inv.handlesRemove _ _ fun s hs => hR s _ _ hs) fun _ =>
    P.Inv.bind (expectEnd _ _ _) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.bind (P.Inv.trapIf _ _) fun _ =>
    P.Inv.bind (endDrop_inv (hd _)) fun _ => P.Inv.pure _

theorem expectForwardEnd (kind : EndKind) (t : Option (WIT.ClosedType RtId))
    (ent : HandleEntry) : P.Inv I (Builtins.expectForwardEnd kind t ent : P E σ EndId) :=
  P.Inv.bind (expectEnd _ _ _) fun _ => P.Inv.bind (P.Inv.trapIf _ _) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.pure _

end Inv

end Silmaril.Wasm.Component.Canon.Builtins

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Async
variable {E : CoreEngine} {σ : Type}

namespace Inv

variable {I : CStore E → Prop}

theorem copyBuiltin (hl : P.Inv.LoadPres I) (hs : P.Inv.StorePres I) (h : AwaitPres I)
    (hc : ∀ e buf isRead s, I s → I (copySt (E := E) e buf isRead s)) (lim : Limits)
    (q : Quirks) (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (opts : CanonOpts E)
    (i ptr length : Nat) :
    P.Inv I (Builtins.copyBuiltin lim q kind t opts i ptr length : P E σ (List FlatValue)) :=
  P.Inv.bind P.Inv.currentInst fun _ => P.Inv.bind (endMayLeave _) fun _ =>
    P.Inv.bind (P.Inv.handlesGet _ _) fun _ => P.Inv.bind (expectEnd _ _ _) fun _ =>
    P.Inv.bind (checkCopyIdle _ _) fun _ => P.Inv.bind (P.Inv.trapIf _ _) fun _ =>
    P.Inv.bind (mkGuestBuffer_inv _ _ _ _ _) fun _ =>
    P.Inv.bind (endCopy_inv hl hs lim q (hc _ _ _)) fun _ =>
    awaitEndEvent h _ _ _ fun _ => copyResultFlat _ _ _

theorem forwardBuiltin (hl : P.Inv.LoadPres I) (hs : P.Inv.StorePres I)
    (hR : P.Inv.RemoveHandlePres I)
    (hf : ∀ src dst s, I s → I (forwardSt (E := E) src dst s)) (lim : Limits) (q : Quirks)
    (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (ri wi : Nat) :
    P.Inv I (Builtins.forwardBuiltin lim q kind t ri wi : P E σ (List FlatValue)) :=
  P.Inv.bind P.Inv.currentInst fun _ => P.Inv.bind (endMayLeave _) fun _ =>
    P.Inv.bind (P.Inv.handlesRemove _ _ fun s hs => hR s _ _ hs) fun _ =>
    P.Inv.bind (expectForwardEnd _ _ _) fun _ =>
    P.Inv.bind (P.Inv.handlesRemove _ _ fun s hs => hR s _ _ hs) fun _ =>
    P.Inv.bind (expectForwardEnd _ _ _) fun _ =>
    P.Inv.bind (endForward_inv hl hs lim q (hf _ _)) fun _ => P.Inv.pure _

end Inv

end Silmaril.Wasm.Component.Canon.Builtins
