module

public import Silmaril.Wasm.Component.Reference.Runtime.StreamOps.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Stream.Properties.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Load.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Store.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Load.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Store.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Runtime.StreamOps`: laws of the component reference

Theorems of the component reference copy `Runtime.StreamOps`, refined out of
`Silmaril.Raw.Wasm.Component.Runtime.StreamOps`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine AsyncRef Canon Value
variable {E : CoreEngine} {σ : Type}

section Inv

variable {I : CStore E → Prop}

theorem checkGuestBuffer_inv (lim : Limits) (cx : LiftLowerContext E)
    (t : Option (WIT.ClosedType RtId)) (ptr length : Nat) :
    P.Inv I (checkGuestBuffer lim cx t ptr length : P E σ Unit) := by
  unfold checkGuestBuffer
  refine P.Inv.bind (P.Inv.trapIf _ _) fun _ => ?_
  split
  · exact P.Inv.ite (P.Inv.bind (P.Inv.ptrType _) fun _ =>
      P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.checkInBounds _ _ _) (P.Inv.pure _)
  · exact P.Inv.pure _

theorem mkGuestBuffer_inv (lim : Limits) (cx : LiftLowerContext E)
    (t : Option (WIT.ClosedType RtId)) (ptr length : Nat) :
    P.Inv I (mkGuestBuffer lim cx t ptr length : P E σ (BufferDesc E)) :=
  P.Inv.bind (checkGuestBuffer_inv lim cx t ptr length) fun _ => P.Inv.pure _

theorem readBuffer_inv (h : P.Inv.LoadPres I) (lim : Limits) (q : Quirks) (b : BufferDesc E)
    (n : Nat) : P.Inv I (readBuffer lim q b n : P E σ (List Val)) := by
  match b with
  | .guest cx (some u) ptr _ progress =>
    exact P.Inv.bind (P.Inv.ptrType _) fun _ => P.Inv.loadListFromValidRange h _ _ _ _ _ _
  | .guest _ none _ _ _ => exact P.Inv.pure _
  | .host _ _ _ =>
    exact P.Inv.bind (P.Inv.callVals _) fun _ => P.Inv.ite (P.Inv.pure _) (P.Inv.internal _)

theorem endCancel_inv {e : EndId} (hc : ∀ b s, I s → I (cancel e b s)) :
    P.Inv I (endCancel e : P E σ Unit) :=
  P.Inv.bind P.Inv.getStore fun _ =>
    P.Inv.bind (P.Inv.ite (P.Inv.choose _) (P.Inv.pure _)) fun b => P.Inv.modifyStore (hc b)

theorem endDrop_inv {e : EndId} (hd : ∀ s, I s → I (dropEnd e s)) :
    P.Inv I (endDrop e : P E σ Unit) := P.Inv.modifyStore hd

end Inv

end Silmaril.Wasm.Component.Runtime

namespace Silmaril.Wasm.Component.Runtime

open Engine AsyncRef Canon Value
variable {E : CoreEngine} {σ : Type}

section Inv

variable {I : CStore E → Prop}

theorem writeBuffer_inv (h : P.Inv.StorePres I) (lim : Limits) (q : Quirks) (b : BufferDesc E)
    (vs : List Val) : P.Inv I (writeBuffer lim q b vs : P E σ Unit) := by
  match b with
  | .guest cx (some u) ptr _ progress =>
    exact P.Inv.bind (P.Inv.ptrType _) fun _ => P.Inv.storeListIntoValidRange h _ _ _ _ _ _
  | .guest _ none _ _ _ => exact P.Inv.pure _
  | .host _ _ _ => exact P.Inv.callUnit _

theorem performCopy_inv (hl : P.Inv.LoadPres I) (hs : P.Inv.StorePres I) (lim : Limits) (q : Quirks)
    (a : CopyAction E) : P.Inv I (performCopy lim q a : P E σ Unit) := by
  cases a with
  | none => exact P.Inv.pure _
  | transfer _ _ n wb rb =>
    exact P.Inv.bind (readBuffer_inv hl lim q wb n) fun vs => writeBuffer_inv hs lim q rb vs

theorem endCopy_inv (hl : P.Inv.LoadPres I) (hs : P.Inv.StorePres I) (lim : Limits) (q : Quirks)
    {e : EndId} {buf : BufferDesc E} {isRead : Bool}
    (hc : ∀ s, I s → I (copySt e buf isRead s)) :
    P.Inv I (endCopy lim q e buf isRead : P E σ Unit) := by
  unfold endCopy
  refine P.Inv.bind P.Inv.getStore fun _ => ?_
  split
  · exact P.Inv.trap _
  · exact P.Inv.bind (P.Inv.modifyStore hc) fun _ => performCopy_inv hl hs lim q _

theorem endForward_inv (hl : P.Inv.LoadPres I) (hs : P.Inv.StorePres I) (lim : Limits) (q : Quirks)
    {src dst : EndId} (hf : ∀ s, I s → I (forwardSt src dst s)) :
    P.Inv I (endForward lim q src dst : P E σ Unit) := by
  unfold endForward
  refine P.Inv.bind P.Inv.getStore fun _ => ?_
  split
  · exact P.Inv.trap _
  · exact P.Inv.bind (P.Inv.modifyStore hf) fun _ => performCopy_inv hl hs lim q _

end Inv

end Silmaril.Wasm.Component.Runtime
