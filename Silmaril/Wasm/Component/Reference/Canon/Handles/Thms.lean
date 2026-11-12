module

public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Handles`: laws of the component reference

Theorems of the component reference copy `Canon.Handles`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Handles`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.AsyncRef
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem expectResource (e : HandleEntry) : P.Inv I (Canon.expectResource e : P E σ _) := by
  cases e <;> first | exact pure _ | exact trap _

theorem getResHandle (h : HandleObjId) : P.Inv I (Canon.getResHandle h : P E σ _) :=
  getObj _ _

theorem getResourceType (rt : RtId) : P.Inv I (Canon.getResourceType rt : P E σ _) :=
  getObj _ _

theorem addResHandle (hA : AllocResHandlePres I) (hH : AddHandlePres I) (inst : InstId)
    (h : ResourceHandle) : P.Inv I (Canon.addResHandle inst h : P E σ Nat) :=
  bind (allocObj _ _ fun s hs => hA s h hs) fun _ =>
    handlesAdd _ _ fun s hs => hH s inst ⟨_, NotSubtaskEntry.resource _⟩ hs

theorem liftOwn (hR : RemoveHandlePres I) (lim : Limits) (cx : LiftLowerContext E) (rt : RtId)
    (i : Nat) : P.Inv I (Canon.liftOwn lim cx rt i : P E σ Nat) :=
  bind (handlesRemove _ _ fun s hs => hR s _ _ hs) fun _ =>
    bind (expectResource _) fun _ => bind (getResHandle _) fun _ =>
      bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ => pure _

theorem liftBorrow (hL : ∀ s st h, I st → I (HandleSt.addLender (E := E) s h st))
    (lim : Limits) (cx : LiftLowerContext E) (rt : RtId) (i : Nat) :
    P.Inv I (Canon.liftBorrow lim cx rt i : P E σ Nat) := by
  unfold Canon.liftBorrow
  split
  · exact bind (handlesGet _ _) fun _ => bind (expectResource _) fun _ =>
      bind (getResHandle _) fun _ => bind (trapIf _ _) fun _ =>
        bind (modifyStore (hL _ · _)) fun _ => pure _
  · exact internal _

theorem lowerOwn (hA : AllocResHandlePres I) (hH : AddHandlePres I) (lim : Limits)
    (cx : LiftLowerContext E) (rt : RtId) (rep : Nat) :
    P.Inv I (Canon.lowerOwn lim cx rt rep : P E σ Nat) := addResHandle hA hH _ _

theorem lowerBorrow (hA : AllocResHandlePres I) (hH : AddHandlePres I)
    (hB : ∀ t st, I st → I (HandleSt.incBorrows (E := E) t st)) (lim : Limits)
    (cx : LiftLowerContext E) (rt : RtId) (rep : Nat) :
    P.Inv I (Canon.lowerBorrow lim cx rt rep : P E σ Nat) := by
  unfold Canon.lowerBorrow
  split
  · refine bind (getResourceType _) fun rty => ite (pure _) ?_
    exact bind (allocObj _ _ fun s hs => hA s _ hs) fun _ =>
      bind (modifyStore (hB _ · )) fun _ =>
        handlesAdd _ _ fun s hs => hH s _ ⟨_, NotSubtaskEntry.resource _⟩ hs
  · exact internal _

theorem liftErrorContext (lim : Limits) (cx : LiftLowerContext E) (i : Nat) :
    P.Inv I (Canon.liftErrorContext lim cx i : P E σ ErrCtxId) :=
  bind (handlesGet _ _) fun e => by cases e <;> first | exact pure _ | exact trap _

theorem lowerErrorContext (hH : AddHandlePres I) (lim : Limits) (cx : LiftLowerContext E)
    (x : ErrCtxId) : P.Inv I (Canon.lowerErrorContext lim cx x : P E σ Nat) :=
  handlesAdd _ _ fun s hs => hH s _ ⟨_, NotSubtaskEntry.errCtx _⟩ hs

theorem checkLiftEnd (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (ent : HandleEntry) :
    P.Inv I (Canon.checkLiftEnd kind t ent : P E σ EndId) := by
  unfold Canon.checkLiftEnd
  split
  · exact bind (getObj _ _) fun _ => bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ =>
      bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ => pure _
  · exact trap _

theorem liftAsyncValue (hR : RemoveHandlePres I)
    (hE : ∀ e st, I st → I (HandleSt.releaseEnd (E := E) e st)) (lim : Limits)
    (kind : EndKind) (cx : LiftLowerContext E) (t : Option (WIT.ClosedType RtId)) (i : Nat) :
    P.Inv I (Canon.liftAsyncValue lim kind cx t i : P E σ EndId) :=
  bind (handlesRemove _ _ fun s hs => hR s _ _ hs) fun _ =>
    bind (checkLiftEnd _ _ _) fun _ => bind (modifyStore (hE _ ·)) fun _ => pure _

theorem lowerAsyncValue (hH : AddHandlePres I)
    (hO : ∀ e inst st, I st → I (HandleSt.setEndOwner (E := E) e inst st))
    (hI : ∀ e i st, I st → I (HandleSt.setEndIndex (E := E) e i st)) (lim : Limits)
    (kind : EndKind) (cx : LiftLowerContext E) (e : EndId) :
    P.Inv I (Canon.lowerAsyncValue lim kind cx e : P E σ Nat) :=
  bind (modifyStore (hO _ _ ·)) fun _ =>
    bind (handlesAdd _ _ fun s hs => hH s _ ⟨_, NotSubtaskEntry.end_ _⟩ hs) fun _ =>
    bind (modifyStore (hI _ _ ·)) fun _ => pure _

theorem resourceNewCore (hA : AllocResHandlePres I) (hH : AddHandlePres I) (lim : Limits)
    (inst : InstId) (rt : RtId) (rep : Nat) :
    P.Inv I (Canon.resourceNewCore lim inst rt rep : P E σ Nat) := addResHandle hA hH _ _

theorem resourceRepCore (lim : Limits) (inst : InstId) (rt : RtId) (i : Nat) :
    P.Inv I (Canon.resourceRepCore lim inst rt i : P E σ Nat) :=
  bind (handlesGet _ _) fun _ => bind (expectResource _) fun _ =>
    bind (getResHandle _) fun _ => bind (trapIf _ _) fun _ => pure _

theorem dropHandleTail (hB : ∀ t st, I st → I (HandleSt.decBorrows (E := E) t st)) (rt : RtId)
    (h : ResourceHandle) : P.Inv I (Canon.dropHandleTail rt h : P E σ _) := by
  unfold Canon.dropHandleTail
  split
  · exact bind (getResourceType _) fun _ => pure _
  · split
    · exact bind (modifyStore (hB _ ·)) fun _ => pure _
    · exact internal _

theorem resourceDropCore (hR : RemoveHandlePres I)
    (hB : ∀ t st, I st → I (HandleSt.decBorrows (E := E) t st)) (lim : Limits) (inst : InstId)
    (rt : RtId) (i : Nat) : P.Inv I (Canon.resourceDropCore lim inst rt i : P E σ _) :=
  bind (handlesRemove _ _ fun s hs => hR s _ _ hs) fun _ =>
    bind (expectResource _) fun _ => bind (getResHandle _) fun _ =>
      bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ => dropHandleTail hB _ _

end P.Inv

end Silmaril.Wasm.Component.Canon
