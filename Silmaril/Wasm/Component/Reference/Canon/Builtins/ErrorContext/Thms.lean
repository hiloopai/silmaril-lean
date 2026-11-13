module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.ErrorContext.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Defs
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
# `Canon.Builtins.ErrorContext`: laws of the component reference

Theorems of the component reference copy `Canon.Builtins.ErrorContext`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Builtins.ErrorContext`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem expectErrCtx (e : HandleEntry) :
    P.Inv I (Builtins.expectErrCtx e : P E σ ErrCtxId) := by
  cases e <;> first | exact Canon.P.Inv.pure _ | exact Canon.P.Inv.trap _

/-- `error-context.new` preserves `I` when allocating an error context and adding a handle
to an instance do. -/
theorem errorContextNew (lim : Limits) (q : Quirks) (opts : CanonOpts E) (ptr units : Nat)
    (halloc : ∀ ec s, I s → I (ArenaOps.allocSt ArenaField.errCtxs ec s))
    (hadd : ∀ inst x s, I s →
      I (ArenaField.insts.modify s inst (InstState.addHandle (.errCtx x)))) :
    P.Inv I (Builtins.errorContextNew lim q opts ptr units : P E σ _) := by
  unfold Builtins.errorContextNew
  refine Canon.P.Inv.bind Canon.P.Inv.currentInst fun inst => ?_
  refine Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ => ?_
  refine Canon.P.Inv.bind (Canon.P.Inv.choose _) fun keep => ?_
  refine Canon.P.Inv.bind ?_ fun msg => ?_
  · cases keep
    · exact Canon.P.Inv.pure _
    · exact Canon.P.Inv.bind (Canon.P.Inv.loadStringFromRange _ _ _ _ _) fun _ =>
        Canon.P.Inv.choose _
  · exact Canon.P.Inv.bind (Canon.P.Inv.allocObj _ _ (halloc _)) fun x =>
      Canon.P.Inv.bind (Canon.P.Inv.handlesAdd _ _ (hadd _ _)) fun _ => Canon.P.Inv.pure _

/-- `error-context.debug-message` preserves `I` when memory writes do. -/
theorem errorContextDebugMessage (lim : Limits) (q : Quirks) (opts : CanonOpts E) (i ptr : Nat)
    (hw : ∀ m p bs s, I s → I (writeMemSt m p bs s)) :
    P.Inv I (Builtins.errorContextDebugMessage lim q opts i ptr : P E σ _) := by
  unfold Builtins.errorContextDebugMessage
  refine Canon.P.Inv.bind Canon.P.Inv.currentInst fun inst => ?_
  refine Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ => ?_
  refine Canon.P.Inv.bind (Canon.P.Inv.handlesGet _ _) fun e =>
    Canon.P.Inv.bind (expectErrCtx e) fun x => ?_
  refine Canon.P.Inv.bind (Canon.P.Inv.getObj _ _) fun ec => ?_
  refine Canon.P.Inv.bind (Canon.P.Inv.ptrSize _) fun sz => ?_
  refine Canon.P.Inv.bind (Canon.P.Inv.checkAligned _ _) fun _ => ?_
  refine Canon.P.Inv.bind (Canon.P.Inv.checkInBounds _ _ _) fun _ => ?_
  exact Canon.P.Inv.bind (Canon.P.Inv.storeString _ _ _ _ _ hw) fun _ => Canon.P.Inv.pure _

/-- `error-context.drop` preserves `I` when removing a handle from an instance does. -/
theorem errorContextDrop (i : Nat)
    (hrm : ∀ inst s, I s → I (ArenaField.insts.modify s inst (InstState.removeHandle i))) :
    P.Inv I (Builtins.errorContextDrop i : P E σ _) := by
  unfold Builtins.errorContextDrop
  refine Canon.P.Inv.bind Canon.P.Inv.currentInst fun inst => ?_
  refine Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ => ?_
  exact Canon.P.Inv.bind (Canon.P.Inv.handlesRemove _ _ (hrm _)) fun e =>
    Canon.P.Inv.bind (expectErrCtx e) fun _ => Canon.P.Inv.pure _

end P.Inv

end Silmaril.Wasm.Component.Canon.Builtins
