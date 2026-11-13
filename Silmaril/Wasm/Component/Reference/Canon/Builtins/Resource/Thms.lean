module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Resource.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
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
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Builtins.Resource`: laws of the component reference

Theorems of the component reference copy `Canon.Builtins.Resource`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Builtins.Resource`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value
variable {E : CoreEngine} {σ : Type}

namespace Inv

variable {I : CStore E → Prop}

theorem resourceEnter : P.Inv I (Builtins.resourceEnter : P E σ InstId) :=
  P.Inv.bind P.Inv.currentInst fun _ => P.Inv.bind (P.Inv.getInst _) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.pure _

theorem resourceNew (hA : P.Inv.AllocResHandlePres I) (hH : P.Inv.AddHandlePres I)
    (lim : Limits) (rt : RtId) (rep : Nat) :
    P.Inv I (Builtins.resourceNew lim rt rep : P E σ (List FlatValue)) :=
  P.Inv.bind resourceEnter fun _ =>
    P.Inv.bind (P.Inv.resourceNewCore hA hH _ _ _ _) fun _ => P.Inv.pure _

theorem resourceDrop (hR : P.Inv.RemoveHandlePres I)
    (hB : ∀ t st, I st → I (HandleSt.decBorrows (E := E) t st)) (lim : Limits) (q : Quirks)
    {dtorCall : InstId → DtorRequest E → P E σ Unit}
    (hD : ∀ inst req, P.Inv I (dtorCall inst req)) (rt : RtId) (i : Nat) :
    P.Inv I (Builtins.resourceDrop lim q dtorCall rt i : P E σ (List FlatValue)) := by
  unfold Builtins.resourceDrop
  refine P.Inv.bind resourceEnter fun inst =>
    P.Inv.bind (P.Inv.resourceDropCore hR hB _ _ _ _) fun r => ?_
  cases r
  · exact P.Inv.bind (P.Inv.pure _) fun _ => P.Inv.pure _
  · exact P.Inv.bind (hD _ _) fun _ => P.Inv.pure _

theorem resourceRep (lim : Limits) (rt : RtId) (i : Nat) :
    P.Inv I (Builtins.resourceRep lim rt i : P E σ (List FlatValue)) :=
  P.Inv.bind P.Inv.currentInst fun _ =>
    P.Inv.bind (P.Inv.resourceRepCore _ _ _ _) fun _ =>
      P.Inv.bind (P.Inv.getResourceType _) fun _ => P.Inv.pure _

end Inv

end Silmaril.Wasm.Component.Canon.Builtins
