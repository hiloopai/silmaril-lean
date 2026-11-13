module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Thread.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs
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
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Builtins.Thread`: laws of the component reference

Theorems of the component reference copy `Canon.Builtins.Thread`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Builtins.Thread`: those that other topics use through
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

theorem enterThreadBuiltin : P.Inv I (Builtins.enterThreadBuiltin : P E σ _) :=
  Canon.P.Inv.bind Canon.P.Inv.currentThreadId fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.getThread _) fun _ =>
      Canon.P.Inv.bind (Canon.P.Inv.getTask _) fun _ =>
        Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
          Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ => Canon.P.Inv.pure _

theorem trapUnlessSuspended (o : ThreadId) :
    P.Inv I (Builtins.trapUnlessSuspended o : P E σ Unit) :=
  Canon.P.Inv.bind Canon.P.Inv.getStore fun _ => Canon.P.Inv.trapIf _ _

theorem threadIndex : P.Inv I (Builtins.threadIndex : P E σ _) :=
  Canon.P.Inv.bind enterThreadBuiltin fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.orTrap _ _) fun _ => Canon.P.Inv.pure _

/-- `thread.new-indirect` preserves `I` when thread registration does. -/
theorem threadNewIndirect (tbl : E.TableAddr) (ft : V1.FuncType) (fi : Nat) (c : FlatValue)
    (h : ∀ task t s, I s → I (s.registerThreadSt task t)) :
    P.Inv I (Builtins.threadNewIndirect tbl ft fi c : P E σ _) :=
  Canon.P.Inv.bind Canon.P.Inv.currentTask fun task =>
    Canon.P.Inv.bind (Canon.P.Inv.getTask _) fun _ =>
      Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
        Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
          Canon.P.Inv.bind Canon.P.Inv.getStore fun _ =>
            Canon.P.Inv.bind (Canon.P.Inv.orTrap _ _) fun _ =>
              Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
                Canon.P.Inv.bind (Canon.P.Inv.newThread _) fun nt =>
                  Canon.P.Inv.bind (Runtime.Task.registerThread_inv task nt (h task nt))
                    fun _ => Canon.P.Inv.pure _

/-- `thread.resume-later` preserves `I` when starting to wait on `.always` does. -/
theorem threadResumeLater (i : Nat) (h : ∀ t s, I s → I (s.startWaitingSt t .always)) :
    P.Inv I (Builtins.threadResumeLater i : P E σ _) :=
  Canon.P.Inv.bind Canon.P.Inv.currentInst fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.getInst _) fun _ =>
      Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
        Canon.P.Inv.bind (Canon.P.Inv.threadsGet _ _) fun o =>
          Canon.P.Inv.bind (trapUnlessSuspended o) fun _ =>
            Canon.P.Inv.bind (Runtime.Thread.resumeLater_inv (h o)) fun _ =>
              Canon.P.Inv.pure _

theorem threadSuspend : P.Inv I (Builtins.threadSuspend : P E σ _) :=
  Canon.P.Inv.bind enterThreadBuiltin fun _ =>
    Canon.P.Inv.bind Runtime.Thread.suspend_inv fun _ => Canon.P.Inv.pure _

/-- `thread.yield` preserves `I` when starting to wait on `.always` does. -/
theorem threadYield (h : ∀ t s, I s → I (s.startWaitingSt t .always)) :
    P.Inv I (Builtins.threadYield : P E σ _) :=
  Canon.P.Inv.bind enterThreadBuiltin fun _ =>
    Canon.P.Inv.bind (Runtime.Thread.waitUntil_inv _ _ _ h) fun _ => Canon.P.Inv.pure _

theorem threadSuspendThenResume (i : Nat) :
    P.Inv I (Builtins.threadSuspendThenResume i : P E σ _) :=
  Canon.P.Inv.bind enterThreadBuiltin fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.threadsGet _ _) fun o =>
      Canon.P.Inv.bind (trapUnlessSuspended o) fun _ =>
        Canon.P.Inv.bind (Runtime.Thread.suspendThenResume_inv o) fun _ => Canon.P.Inv.pure _

/-- `thread.yield-then-resume` preserves `I` when starting to wait on `.always` does. -/
theorem threadYieldThenResume (i : Nat) (h : ∀ t s, I s → I (s.startWaitingSt t .always)) :
    P.Inv I (Builtins.threadYieldThenResume i : P E σ _) :=
  Canon.P.Inv.bind enterThreadBuiltin fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.threadsGet _ _) fun o =>
      Canon.P.Inv.bind (trapUnlessSuspended o) fun _ =>
        Canon.P.Inv.bind (Runtime.Thread.yieldThenResume_inv o h) fun _ => Canon.P.Inv.pure _

/-- `thread.suspend-then-promote` preserves `I` when stopping to wait does. -/
theorem threadSuspendThenPromote (hr : HostReady σ) (q : Quirks) (i : Nat)
    (hstop : ∀ t s, I s → I (s.stopWaitingSt t)) :
    P.Inv I (Builtins.threadSuspendThenPromote hr q i : P E σ _) :=
  Canon.P.Inv.bind enterThreadBuiltin fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
      Canon.P.Inv.bind (Canon.P.Inv.threadsGet _ _) fun o =>
        Canon.P.Inv.bind (Runtime.Thread.suspendThenPromote_inv hr q o (hstop o)) fun _ =>
          Canon.P.Inv.pure _

/-- `thread.yield-then-promote` preserves `I` when starting to wait on `.always` and stopping
to wait do. -/
theorem threadYieldThenPromote (hr : HostReady σ) (q : Quirks) (i : Nat)
    (hstart : ∀ t s, I s → I (s.startWaitingSt t .always))
    (hstop : ∀ t s, I s → I (s.stopWaitingSt t)) :
    P.Inv I (Builtins.threadYieldThenPromote hr q i : P E σ _) :=
  Canon.P.Inv.bind enterThreadBuiltin fun _ =>
    Canon.P.Inv.bind (Canon.P.Inv.trapIf _ _) fun _ =>
      Canon.P.Inv.bind (Canon.P.Inv.threadsGet _ _) fun o =>
        Canon.P.Inv.bind (Runtime.Thread.yieldThenPromote_inv hr q o hstart (hstop o))
          fun _ => Canon.P.Inv.pure _

end P.Inv

end Silmaril.Wasm.Component.Canon.Builtins
