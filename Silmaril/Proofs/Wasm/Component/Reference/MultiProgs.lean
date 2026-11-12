module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiBase
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Canon programs of an export call over leftover arenas

Big-step runs (`RunsQ`) of the programs of a `canon lift` call whose task, thread and caller
record are the last entries of arenas with arbitrary earlier entries (left by earlier calls):
`Task.enterImplicitThread`, `Task.start`, `Task.return_`, `Task.exitImplicitThread` and the
synchronous loop body. Lookups at the last index are `List.getElem?_concat_length`, updates
`modify_concat_length`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {σ : Type} {impl : HostImpl (E3 P) σ}

/-! ## Small programs -/

theorem RunsQ.of_tr {α : Type} {th : Option ThreadId} {p : Canon.P (E3 P) σ α}
    {m m' : Machine.Config (E3 P) σ} {a : α} {tr tr' : List (Label (E3 P) σ)}
    (h : RunsQ (DI P impl) th p m tr a m') (e : tr = tr') : RunsQ (DI P impl) th p m tr' a m' :=
  e ▸ h


theorem runs_currentThreadId {th : ThreadId} (m : Machine.Config (E3 P) σ) :
    RunsQ (DI P impl) (some th) currentThreadId m [.tau] th m :=
  .currentThread (.pure _ _)

theorem runs_modifyStore {th : Option ThreadId} (f : CStore (E3 P) → CStore (E3 P))
    (m : Machine.Config (E3 P) σ) (hl : (f m.store).lockdown = m.store.lockdown) :
    RunsQ (DI P impl) th (modifyStore f) m [.tau] () { m with store := f m.store } :=
  .modify hl (.pure _ _)

theorem runs_ite_false {th : Option ThreadId} {b : Bool} (hb : b = false)
    (X : Canon.P (E3 P) σ Unit) (m : Machine.Config (E3 P) σ) :
    RunsQ (DI P impl) th (if b = true then X else pure ()) m [] () m := by
  subst hb
  exact .pure _ _

theorem runs_ite_pure {α : Type} {th : Option ThreadId} {b : Bool} (hb : b = false)
    (X : Canon.P (E3 P) σ α) (a : α) (m : Machine.Config (E3 P) σ) :
    RunsQ (DI P impl) th (if b = true then X else pure a) m [] a m := by
  subst hb
  exact .pure _ _

/-! ## `enter_implicit_thread` -/

theorem runs_enter {m : Machine.Config (E3 P) σ} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {t : ThreadId} {ι ι' : InstState}
    (htasks : m.store.tasks = Gt ++ [y]) (hasync : y.ft.async_ = false) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hadd : ι.addThread? t = some (1, ι')) :
    RunsQ (DI P impl) (some t) (Task.enterImplicitThread Quirks.none ⟨Gt.length⟩) m
      [.tau, .tau, .tau, .tau, .tau, .tau] true
      { m with store := (CStore.registerThreadSt ⟨Gt.length⟩ t
        (CStore.setImplicitThread ⟨Gt.length⟩ t m.store)) } := by
  have h₁ : (CStore.setImplicitThread ⟨Gt.length⟩ t m.store).tasks =
      Gt ++ [{ y with implicitThread := some t }] := tasks_modify_last htasks _
  have hi : ArenaField.insts.get? (CStore.setImplicitThread ⟨Gt.length⟩ t m.store) y.inst =
      some ι := by
    rw [hinst]
    exact insts_get_zero hinsts
  unfold Task.enterImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_currentThreadId m)
  apply RunsQ.bind (runs_modifyStore _ m rfl)
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last h₁))
  apply RunsQ.bind (runs_ite_pure hasync _ true _)
  show RunsQ _ _ (Task.registerThread ⟨Gt.length⟩ t >>= fun _ => pure true) _ _ _ _
  apply RunsQ.bind (f := fun _ => pure true) (a := 1) ?_ (.pure _ _)
  rotate_left
  unfold Task.registerThread
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last h₁))
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ (by exact hi))
  rw [hadd]
  exact RunsQ.bind (runs_modifyStore _ _
    (CStore.registerThreadSt_frame (E := E3 P) _ _ _).2.2.2.2.2.2.1) (.pure _ _)
  rfl

/-! ## Caller records of top-level calls -/

theorem runs_onStart {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gc : List (Caller (E3 P))} {c : CallId} {args : List Val}
    (hc : m.store.callers = Gc ++ [.host c args 0]) :
    RunsQ (DI P impl) th (DI P impl (.onStart ⟨Gc.length⟩)) m [.tau, .obs (.started c)] (.vals args) m := by
  show RunsQ _ _ (callerOnStart Limits.spec Quirks.none ⟨Gc.length⟩) _ _ _ _
  unfold callerOnStart
  exact RunsQ.bind (runs_getObj ArenaField.callers _ _ (callers_get_last hc))
    (RunsQ.bind (tr₁ := [.obs (.started c)]) (.emit (.pure _ _)) (.pure _ _))

theorem runs_onResolve {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gc : List (Caller (E3 P))} {c : CallId} {args : List Val} (r : Option (List Val))
    (hc : m.store.callers = Gc ++ [.host c args 0]) :
    RunsQ (DI P impl) th (DI P impl (.onResolve ⟨Gc.length⟩ r)) m [.tau, .obs (.resolved c r)] .unit
      (m.resolve c r) := by
  show RunsQ _ _ (callerOnResolve Limits.spec Quirks.none ⟨Gc.length⟩ r) _ _ _ _
  unfold callerOnResolve
  exact RunsQ.bind (runs_getObj ArenaField.callers _ _ (callers_get_last hc))
    (RunsQ.bind (tr₁ := [.obs (.resolved c r)]) (.emit (.pure _ _)) (.pure _ _))

/-! ## `Task.start` and `Task.return_` -/

theorem runs_start {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gc : List (Caller (E3 P))}
    {c : CallId} {args : List Val} (ht : m.store.tasks = Gt ++ [y])
    (hy : y.caller = ⟨Gc.length⟩) (hc : m.store.callers = Gc ++ [.host c args 0]) :
    RunsQ (DI P impl) th (Task.start ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .obs (.started c), .tau] args
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } := by
  unfold Task.start
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_modifyStore _ _ rfl)
  rw [hy]
  unfold callVals callRet perform Prog.lift
  exact RunsQ.call (runs_onStart hc) (.pure _ _)
  rfl

theorem runs_trapIf {th : Option ThreadId} {b : Bool} (hb : b = false) (r : TrapReason)
    (m : Machine.Config (E3 P) σ) : RunsQ (DI P impl) th (trapIf b r) m [] () m := by
  subst hb
  exact .pure _ _

theorem runs_return {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gc : List (Caller (E3 P))}
    {c : CallId} {args : List Val} (vs : List Val) (ht : m.store.tasks = Gt ++ [y])
    (hy : y.caller = ⟨Gc.length⟩) (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : m.store.callers = Gc ++ [.host c args 0]) :
    RunsQ (DI P impl) th (Task.return_ ⟨Gt.length⟩ vs) m
      [.tau, .tau, .tau, .obs (.resolved c (some vs)), .tau, .tau] ()
      { m.resolve c (some vs) with
        store := CStore.setTaskState ⟨Gt.length⟩ .resolved m.store } := by
  unfold Task.return_
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hb]; rfl) _ _)
  rw [hy]
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call (runs_onResolve (some vs) hc) (.pure _ _))
  exact runs_modifyStore _ _ rfl
  rfl

/-! ## `exit_implicit_thread` and the synchronous loop -/

theorem runs_unregister {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gth : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved)
    (hthr : m.store.threads = Gth ++ [z]) (hidx : z.index = some i) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.unregisterThread ⟨Gt.length⟩ ⟨Gth.length⟩) m [.tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  have hi : ArenaField.insts.get? m.store y.inst = some ι := by
    rw [hinst]
    exact insts_get_zero hinsts
  unfold Task.unregisterThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; simp) _ _)
  apply RunsQ.bind (runs_getObj ArenaField.threads _ _ (threads_get_last hthr))
  rw [hidx]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ hi)
  rw [hrem]
  exact runs_modifyStore _ _ (CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.2.1
  rfl

theorem runs_exit {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gth : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y]) (himp : y.implicitThread = some ⟨Gth.length⟩)
    (hst : y.state = .resolved) (hasync : y.ft.async_ = false)
    (hthr : m.store.threads = Gth ++ [z]) (hidx : z.index = some i) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.exitImplicitThread ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  have hu := runs_unregister (impl := impl) (th := th) ht hst hthr hidx hinst hinsts hrem
  unfold Task.exitImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  rw [himp]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind hu
  exact runs_ite_false (by rw [hasync]; rfl) _ _
  rfl

theorem runs_loop {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved) :
    RunsQ (DI P impl) th (DI P impl (.loop (.syncLiftLoop ⟨Gt.length⟩))) m [.tau] .unit m := by
  show RunsQ _ _ (syncLiftLoopBody (fun _ _ => false) ⟨Gt.length⟩) _ _ _ _
  unfold syncLiftLoopBody
  apply RunsQ.bind (tr₂ := []) (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  rw [hst]
  exact .pure _ _

theorem runs_callUnit_loop {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved) :
    RunsQ (DI P impl) th (callUnit (.loop (.syncLiftLoop ⟨Gt.length⟩))) m [.tau, .tau, .tau] () m := by
  unfold callUnit callRet perform Prog.lift
  exact RunsQ.call (runs_loop ht hst) (.pure _ _)

end Silmaril.Proofs.Wasm.Component.Reference
