module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Task.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs
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
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Builtins.Task`: laws of the component reference

Theorems of the component reference copy `Canon.Builtins.Task`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Builtins.Task`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem contextGet (t : AddrType) (i : Nat) :
    P.Inv I (Builtins.contextGet t i : P E σ (List FlatValue)) :=
  Canon.P.Inv.bind Canon.P.Inv.currentThreadId fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.getThread _) fun _ =>
      Canon.P.Inv.bind (Canon.P.Inv.orTrap _ _) fun _ => Canon.P.Inv.pure _

theorem contextSet (t : AddrType) (i v : Nat) (h : ∀ th s, I s → I (setContextSt th i v s)) :
    P.Inv I (Builtins.contextSet t i v : P E σ (List FlatValue)) :=
  Canon.P.Inv.bind Canon.P.Inv.currentThreadId fun th =>
    Canon.P.Inv.bind (Canon.P.Inv.getThread _) fun _ =>
      Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
        Canon.P.Inv.bind (Canon.P.Inv.modifyStore (h th)) fun _ => Canon.P.Inv.pure _

theorem backpressureInc
    (h : ∀ inst s, I s → I (ArenaField.insts.modify s inst incBackpressureSt)) :
    P.Inv I (Builtins.backpressureInc : P E σ (List FlatValue)) :=
  Canon.P.Inv.bind Canon.P.Inv.currentInst fun inst =>
    Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
      Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
        Canon.P.Inv.bind (Canon.P.Inv.modifyInst inst (h inst)) fun _ => Canon.P.Inv.pure _

theorem backpressureDec
    (h : ∀ inst s, I s → I (ArenaField.insts.modify s inst decBackpressureSt)) :
    P.Inv I (Builtins.backpressureDec : P E σ (List FlatValue)) :=
  Canon.P.Inv.bind Canon.P.Inv.currentInst fun inst =>
    Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
      Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
        Canon.P.Inv.bind (Canon.P.Inv.modifyInst inst (h inst)) fun _ => Canon.P.Inv.pure _

/-- `task.return` preserves `I` when lifting does (`LoadPres I`) and setting a task state to
`resolved` does. -/
theorem taskReturn (hl : Canon.P.Inv.LoadPres I)
    (hs : ∀ task s, I s → I (s.setTaskState task .resolved)) (lim : Limits) (q : Quirks)
    (result : Option (WIT.ClosedType RtId)) (opts : CanonOpts E) (flatArgs : List FlatValue) :
    P.Inv I (Builtins.taskReturn lim q result opts flatArgs : P E σ (List FlatValue)) :=
  Canon.P.Inv.bind Canon.P.Inv.currentTask fun task =>
    Canon.P.Inv.bind (Canon.P.Inv.getTask _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.liftFlatValues hl lim q _ _ _ _) fun _ =>
    Canon.P.Inv.bind (Runtime.Task.return_inv task _ (hs task)) fun _ => Canon.P.Inv.pure _

/-- `task.cancel` preserves `I` when setting a task state to `resolved` does. -/
theorem taskCancel (hs : ∀ task s, I s → I (s.setTaskState task .resolved)) :
    P.Inv I (Builtins.taskCancel : P E σ (List FlatValue)) :=
  Canon.P.Inv.bind Canon.P.Inv.currentTask fun task =>
    Canon.P.Inv.bind (Canon.P.Inv.getTask _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
    Canon.P.Inv.bind (Runtime.Task.cancel_inv task (hs task)) fun _ => Canon.P.Inv.pure _

end P.Inv

end Silmaril.Wasm.Component.Canon.Builtins
