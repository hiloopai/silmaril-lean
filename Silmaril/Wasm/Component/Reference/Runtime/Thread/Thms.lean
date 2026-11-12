module

public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Runtime.Thread`: laws of the component reference

Theorems of the component reference copy `Runtime.Thread`, refined out of
`Silmaril.Raw.Wasm.Component.Runtime.Thread`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine Async Canon

namespace Thread

variable {E : CoreEngine} {σ : Type}

section Inv

variable {I : CStore E → Prop}

theorem readyNow_inv (hr : HostReady σ) (rc : ReadyCond) :
    P.Inv I (readyNow hr rc : P E σ Bool) := by
  cases rc <;>
    first
    | exact P.Inv.bind P.Inv.hostGet fun _ => P.Inv.pure _
    | exact P.Inv.bind P.Inv.getStore fun _ => P.Inv.pure _

theorem isReady_inv (hr : HostReady σ) (t : ThreadId) :
    P.Inv I (isReady hr t : P E σ Bool) :=
  P.Inv.bind P.Inv.getStore fun _ => P.Inv.bind P.Inv.hostGet fun _ => P.Inv.pure _

theorem isPromotable_inv (hr : HostReady σ) (q : Quirks) (o : ThreadId) :
    P.Inv I (isPromotable hr q o : P E σ Bool) := by
  unfold isPromotable
  split
  · exact P.Inv.bind P.Inv.getStore fun _ => P.Inv.pure _
  · exact isReady_inv hr o

theorem startWaiting_inv {t : ThreadId} {rc : ReadyCond}
    (h : ∀ s, I s → I (s.startWaitingSt t rc)) : P.Inv I (startWaiting t rc : P E σ Unit) :=
  P.Inv.modifyStore h

theorem stopWaiting_inv {t : ThreadId} (h : ∀ s, I s → I (s.stopWaitingSt t)) :
    P.Inv I (stopWaiting t : P E σ Unit) :=
  P.Inv.modifyStore h

theorem resumeLater_inv {t : ThreadId} (h : ∀ s, I s → I (s.startWaitingSt t .always)) :
    P.Inv I (resumeLater t : P E σ Unit) :=
  startWaiting_inv h

theorem suspend_inv : P.Inv I (suspend : P E σ Unit) := P.Inv.block _

theorem suspendThenResume_inv (o : ThreadId) : P.Inv I (suspendThenResume o : P E σ Unit) :=
  P.Inv.block _

theorem yieldThenResume_inv (o : ThreadId) (h : ∀ t s, I s → I (s.startWaitingSt t .always)) :
    P.Inv I (yieldThenResume o : P E σ Unit) :=
  P.Inv.bind P.Inv.currentThreadId fun t =>
    P.Inv.bind (startWaiting_inv (h t)) fun _ => P.Inv.block _

/-- `waitUntil hr site rc` preserves `I` if every `startWaitingSt _ rc` does. -/
theorem waitUntil_inv (hr : HostReady σ) (site : WaitSite) (rc : ReadyCond)
    (h : ∀ t s, I s → I (s.startWaitingSt t rc)) :
    P.Inv I (waitUntil hr site rc : P E σ Unit) := by
  unfold waitUntil
  refine P.Inv.bind P.Inv.currentThreadId fun t => ?_
  refine P.Inv.bind (readyNow_inv hr rc) fun now => ?_
  refine P.Inv.bind ?_ fun early => ?_
  · cases now
    · exact P.Inv.pure _
    · exact P.Inv.choose _
  · cases early
    · exact P.Inv.bind (startWaiting_inv (h t)) fun _ => P.Inv.block _
    · exact P.Inv.pure _

theorem resume_inv (t : ThreadId) (h : ∀ s, I s → I (s.stopWaitingSt t)) :
    P.Inv I (resume t : P E σ Unit) := by
  unfold resume
  refine P.Inv.bind P.Inv.getStore fun s => ?_
  refine P.Inv.bind ?_ fun _ => P.Inv.resumeThread t
  split
  · exact stopWaiting_inv h
  · exact P.Inv.pure _

theorem yieldThenPromote_inv (hr : HostReady σ) (q : Quirks) (o : ThreadId)
    (hstart : ∀ t s, I s → I (s.startWaitingSt t .always))
    (hstop : ∀ s, I s → I (s.stopWaitingSt o)) :
    P.Inv I (yieldThenPromote hr q o : P E σ Unit) := by
  unfold yieldThenPromote yield_ waitUntilGuest
  refine P.Inv.bind (isPromotable_inv hr q o) fun b => ?_
  cases b
  · exact waitUntil_inv _ _ _ hstart
  · exact P.Inv.bind (stopWaiting_inv hstop) fun _ => yieldThenResume_inv o hstart

theorem suspendThenPromote_inv (hr : HostReady σ) (q : Quirks) (o : ThreadId)
    (hstop : ∀ s, I s → I (s.stopWaitingSt o)) :
    P.Inv I (suspendThenPromote hr q o : P E σ Unit) := by
  unfold suspendThenPromote suspendThenResume suspend
  refine P.Inv.bind (isPromotable_inv hr q o) fun b => ?_
  cases b
  · exact P.Inv.block _
  · exact P.Inv.bind (stopWaiting_inv hstop) fun _ => P.Inv.block _

end Inv

end Thread

end Silmaril.Wasm.Component.Runtime
