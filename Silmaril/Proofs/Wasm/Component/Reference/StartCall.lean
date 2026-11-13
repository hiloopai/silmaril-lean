module

public import Silmaril.Proofs.Wasm.Component.Reference.StartBase

/-!
# The start function's call during instantiation

`Instantiate.runStart ⟨0⟩ a` lifts the core function `a` at `func()` (the lifted function type of
the pseudo-export `startEx`, no parameters and no results), allocates a `Caller.sub .start`
record and calls the lifted function. The call is the path of a top-level call
(`call_at_k`) with the start caller (`on_start` returns no arguments, `on_resolve` does nothing)
and without the host frame: a deterministic run to the core activation of `a` on no arguments
(`start_at`), and from its return, a deterministic run back to the instantiation program
(`StartAt.ret`), the store holding one more function, one finished task, one exited thread and
the start caller record (`sStore₅`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {impl : HostImpl (E3 P) Unit}

/-- `mstep` at a store whose lockdown flag is a hypothesis. -/
macro "mstepL" : tactic => `(tactic| apply LRun.prog rfl (fun _ _ e => by cases e) (by assumption)
  (by first
    | exact Step.get rfl | exact Step.modify rfl | exact Step.call rfl | exact Step.popProg rfl
    | exact Step.currentThread rfl | exact Step.hostGet rfl | exact Step.hostSet rfl
    | exact Step.emit rfl
    | exact Step.resumeThread rfl rfl | exact Step.newThread rfl rfl | exact Step.threadExit rfl
    | exact Step.hostDone rfl | exact Step.callCore rfl))

/-- The start function as a pseudo-export: no parameters, no results. -/
def startEx : SimpleExport := ⟨"", ⟨[], []⟩, 0⟩

theorem liftedFt_startEx : liftedFt startEx = Instantiate.startType := rfl

/-! ## The start caller -/

theorem runs_onStartS {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gc : List (Caller (E3 P))} (hc : m.store.callers = Gc ++ [.sub .start]) :
    RunsQ (DI P impl) th (DI P impl (.onStart ⟨Gc.length⟩)) m [.tau, .tau] (.vals []) m := by
  show RunsQ _ _ (callerOnStart Limits.spec Quirks.none ⟨Gc.length⟩) _ _ _ _
  unfold callerOnStart
  refine RunsQ.bind (tr₁ := [.tau]) (runs_getObj ArenaField.callers _ _ (callers_get_last hc)) ?_
  unfold onStartProg
  exact RunsQ.bind (tr₂ := []) (runs_getObj ArenaField.callers _ _ (callers_get_last hc)) (.pure _ _)

theorem runs_onResolveS {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gc : List (Caller (E3 P))} (r : Option (List Silmaril.Wasm.Component.Reference.Val))
    (hc : m.store.callers = Gc ++ [.sub .start]) :
    RunsQ (DI P impl) th (DI P impl (.onResolve ⟨Gc.length⟩ r)) m [.tau, .tau] .unit m := by
  show RunsQ _ _ (callerOnResolve Limits.spec Quirks.none ⟨Gc.length⟩ r) _ _ _ _
  unfold callerOnResolve
  refine RunsQ.bind (tr₁ := [.tau]) (runs_getObj ArenaField.callers _ _ (callers_get_last hc)) ?_
  unfold onResolveProg
  exact RunsQ.bind (tr₂ := []) (runs_getObj ArenaField.callers _ _ (callers_get_last hc)) (.pure _ _)

theorem runs_startS {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gc : List (Caller (E3 P))}
    (ht : m.store.tasks = Gt ++ [y]) (hy : y.caller = ⟨Gc.length⟩)
    (hc : m.store.callers = Gc ++ [.sub .start]) :
    RunsQ (DI P impl) th (Task.start ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .tau, .tau] []
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } := by
  unfold Task.start
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_modifyStore _ _ rfl)
  rw [hy]
  unfold callVals callRet perform Prog.lift
  exact RunsQ.call (runs_onStartS hc) (.pure _ _)
  rfl

theorem runs_returnS {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gc : List (Caller (E3 P))}
    (vs : List Silmaril.Wasm.Component.Reference.Val) (ht : m.store.tasks = Gt ++ [y])
    (hy : y.caller = ⟨Gc.length⟩) (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : m.store.callers = Gc ++ [.sub .start]) :
    RunsQ (DI P impl) th (Task.return_ ⟨Gt.length⟩ vs) m
      [.tau, .tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .resolved m.store } := by
  unfold Task.return_
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hb]; rfl) _ _)
  rw [hy]
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call (runs_onResolveS (some vs) hc) (.pure _ _))
  exact runs_modifyStore _ _ rfl
  rfl

/-! ## The stores of the start call -/

/-- The start function, lifted. -/
def startFn (a : Nat) : CFuncInst (core3P P) := .lifted a (liftedFt startEx) {} ⟨0⟩

/-- The store when the start thread starts running. -/
def sStore₁ (S : CStore (E3 P)) (a : Nat) : CStore (E3 P) :=
  { S with
    funcs := S.funcs ++ [startFn a]
    callers := S.callers ++ [.sub .start]
    tasks := S.tasks ++ [task₀ startEx S.callers]
    threads := S.threads ++ [thread₁ S.tasks] }

/-- The store once the start thread entered its task. -/
def sStore₂ (S : CStore (E3 P)) (a : Nat) (ι' : InstState) : CStore (E3 P) :=
  { sStore₁ S a with
    tasks := S.tasks ++ [task₁ startEx S.callers ⟨S.threads.length⟩]
    insts := [ι']
    threads := S.threads ++ [(thread₁ S.tasks).withIndex 1] }

/-- The store when the core activation of the start function begins. -/
def sStore₃ (S : CStore (E3 P)) (a : Nat) (ι' : InstState) : CStore (E3 P) :=
  { sStore₂ S a ι' with
    tasks := S.tasks ++ [(task₁ startEx S.callers ⟨S.threads.length⟩).withState .started] }

/-- The store when the start task resolved (core store `cs'`). -/
def sStore₄ (S : CStore (E3 P)) (a : Nat) (ι' : InstState)
    (cs' : (core3P P).Store (CanonHost (core3P P))) : CStore (E3 P) :=
  { sStore₃ S a ι' with
    core := cs'
    tasks := S.tasks ++ [((task₁ startEx S.callers ⟨S.threads.length⟩).withState .started).withState
      .resolved] }

/-- **The store after the start function** (core store `cs'`). -/
def sStore₅ (S : CStore (E3 P)) (a : Nat) (ι' : InstState)
    (cs' : (core3P P).Store (CanonHost (core3P P))) : CStore (E3 P) :=
  { sStore₄ S a ι' cs' with
    tasks := S.tasks ++ [task₂ startEx S.callers ⟨S.threads.length⟩]
    insts := [InstState.removeThread 1 ι']
    threads := S.threads ++ [{ (thread₁ S.tasks).withIndex 1 with status := .exited }] }

/-- **The configuration after the start function**, back in the instantiation program. -/
def startedCfg (M : Machine.Config (E3 P) Unit) (a : Nat) (ι' : InstState)
    (cs' : (core3P P).Store (CanonHost (core3P P))) : Machine.Config (E3 P) Unit :=
  { M with
    store := sStore₅ M.store a ι' cs'
    conts := Config.setSlot (Config.setSlot M.conts M.store.threads.length
      (some (threadAct (D P) ⟨M.store.threads.length⟩
        (.liftImplicit ⟨M.store.tasks.length⟩ a)))) M.store.threads.length none }

/-- The configuration `M₀` runs the core activation of the start function `a`; when it returns
no values, the run goes back to the instantiation program `K ()` at `startedCfg`. -/
structure StartAt (prof : ProfileKind) (M : Machine.Config (E3 P) Unit) (a : Nat)
    (ι' : InstState) (th : Option ThreadId) (K : Unit → Canon.P (E3 P) Unit (Ret (E3 P)))
    (segs : List (Seg (E3 P) Unit)) (rest : List (Activation (E3 P) Unit))
    (M₀ : Machine.Config (E3 P) Unit) (thc : Option ThreadId)
    (Kc : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segsc : List (Seg (E3 P) Unit))
    (restc : List (Activation (E3 P) Unit)) : Prop where
  ctl : M₀.ctl = ⟨thc, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) Kc, segsc⟩ ::
    restc
  core : M₀.store.core = M.store.core
  lock : M₀.store.lockdown = false
  ret : ∀ y : CoreSt (E3 P), ∃ tr, LRun prof (refHost P).hr (D P) (retCfg M₀ thc Kc segsc restc y [])
    tr { startedCfg M a ι' y.1 with ctl := ⟨th, .prog (K ()), segs⟩ :: rest } ∧ traceObs tr = []

/-- **The start call**: from the instantiation program at `runStart ⟨0⟩ a`, a deterministic run
without observations to the core activation of the start function. -/
theorem start_at (prof : ProfileKind) (M : Machine.Config (E3 P) Unit) (a : Nat)
    (ι ι' : InstState) {th : Option ThreadId} {K : Unit → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hc : M.ctl = ⟨th, .prog (Instantiate.runStart ⟨0⟩ a >>= K), segs⟩ :: rest)
    (hl : M.store.lockdown = false) (hi : M.store.insts = [ι])
    (hadd : ι.addThread? ⟨M.store.threads.length⟩ = some (1, ι'))
    (hrem : ι'.removeThread? 1 = some (⟨M.store.threads.length⟩, InstState.removeThread 1 ι')) :
    ∃ M₀ thc Kc segsc restc tr₁, LRun prof (refHost P).hr (D P) M tr₁ M₀ ∧ traceObs tr₁ = [] ∧
      StartAt prof M a ι' th K segs rest M₀ thc Kc segsc restc := by
  obtain ⟨S, h₀, ctl₀, conts, pending, results, cancels⟩ := M
  dsimp only at hc hl hi hadd hrem ⊢
  subst hc
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (refHost P).hr (D P) _ _ _
    apply RunsQ.chunk2 rfl (runs_allocObj ArenaField.funcs (startFn a) _ rfl) hl
    apply RunsQ.chunk2 rfl (runs_allocObj ArenaField.callers (.sub .start) _ rfl) hl
    apply LRun.prog rfl (fun _ _ e => by cases e) hl (.call rfl)
    have hget : ArenaField.funcs.get? (sStore₁ S a) (⟨S.funcs.length⟩ : FuncId) =
        some (startFn a) := by
      show (S.funcs ++ [startFn a])[S.funcs.length]? = _
      rw [List.getElem?_concat_length]
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ hget) hl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) hl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) hl
    apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) hl
    apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) hl
    apply LRun.prog rfl (fun _ _ e => by cases e) hl
      (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
    have e₁ : ∀ S' : CStore (E3 P), S'.threads = S.threads ++ [{ task := ⟨S.tasks.length⟩ }] →
        threadStatusSt ⟨S.threads.length⟩ .running S' =
          { S' with threads := S.threads ++ [thread₁ S.tasks] } :=
      fun S' h => threadStatus_last h _
    apply LRun.store_congr (S' := sStore₁ S a) ((e₁ _ rfl).trans rfl)
    have hS₁ : (sStore₁ S a).insts = [ι] := hi
    apply RunsQ.chunk (th := some ⟨S.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨S.tasks.length⟩) (a := true) rfl
      (runs_enter (Gt := S.tasks) (y := task₀ startEx S.callers) rfl rfl rfl hS₁ hadd) hl
    have e₂ : CStore.registerThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩
        (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩ (sStore₁ S a)) =
          sStore₂ S a ι' :=
      enter_eq rfl rfl hS₁ hadd rfl
    apply LRun.store_congr (S' := sStore₂ S a ι') (by exact e₂)
    have hS₂ : (sStore₂ S a ι').tasks = S.tasks ++ [task₁ startEx S.callers ⟨S.threads.length⟩] :=
      rfl
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last (Gt := S.tasks) hS₂))
      hl
    apply RunsQ.chunk rfl (runs_startS (Gt := S.tasks) (Gc := S.callers) hS₂ rfl rfl) hl
    apply RunsQ.chunk rfl (runs_lower startEx [] _ rfl rfl (Nat.zero_le _) _) hl
    apply LRun.store_congr (S' := sStore₃ S a ι') (by
      exact setTaskState_last (Gt := S.tasks) (y := task₁ startEx S.callers ⟨S.threads.length⟩)
        rfl _)
    mstepL
    exact .refl _
  apply And.intro
  · simp [traceObs, Label.obs?]
  · show StartAt prof _ a ι' th K segs rest _ _ _ _ _
    apply StartAt.mk
    · rfl
    · rfl
    · exact hl
    · show ∀ y : CoreSt (E3 P), ∃ tr, LRun prof (refHost P).hr (D P) (retCfg _ _ _ _ _ y []) tr _ ∧
        traceObs tr = []
      intro y
      apply Exists.intro
      refine ⟨?_, ?_⟩
      · show LRun prof (refHost P).hr (D P) (retCfg _ _ _ _ _ y []) _ _
        apply LRun.store_congr (S' := sStore₃ { S with core := y.1 } a ι') rfl
        have hS₃ : (sStore₃ { S with core := y.1 } a ι').tasks =
            S.tasks ++ [(task₁ startEx S.callers ⟨S.threads.length⟩).withState .started] := rfl
        unfold retCfg
        apply RunsQ.chunk2 rfl (runs_lift_some (P := P) startEx (Nat.zero_le _) (Nat.zero_le _) rfl
          (ys := []) rfl (ws := []) rfl _ _).choose_spec hl
        apply RunsQ.chunk2 rfl
          (runs_returnS (Gt := S.tasks) (Gc := S.callers) _ hS₃ rfl rfl rfl rfl) hl
        apply LRun.store_congr (S' := sStore₄ S a ι' y.1)
          (by refine setTaskState_last (Gt := S.tasks) ?_ _; rfl)
        apply RunsQ.chunk rfl
          (runs_exit (Gt := S.tasks) (Gth := S.threads)
            (y := ((task₁ startEx S.callers ⟨S.threads.length⟩).withState .started).withState
              .resolved)
            (z := (thread₁ S.tasks).withIndex 1) (ι := ι') rfl rfl rfl rfl rfl rfl rfl rfl hrem) hl
        have e₄ : CStore.unregisterThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩ 1
            (sStore₄ S a ι' y.1) =
              { sStore₄ S a ι' y.1 with
                tasks := S.tasks ++ [task₂ startEx S.callers ⟨S.threads.length⟩]
                insts := [InstState.removeThread 1 ι'] } :=
          unregisterThreadSt_eq _ _ rfl rfl rfl
        apply LRun.store_congr (S' := { sStore₄ S a ι' y.1 with
            tasks := S.tasks ++ [task₂ startEx S.callers ⟨S.threads.length⟩]
            insts := [InstState.removeThread 1 ι'] }) e₄
        mstepL
        have e₅ : threadStatusSt ⟨S.threads.length⟩ .exited
            { sStore₄ S a ι' y.1 with
              tasks := S.tasks ++ [task₂ startEx S.callers ⟨S.threads.length⟩]
              insts := [InstState.removeThread 1 ι'] } = sStore₅ S a ι' y.1 :=
          threadStatus_last (z := (thread₁ S.tasks).withIndex 1) rfl _
        apply LRun.store_congr (S' := sStore₅ S a ι' y.1) e₅
        apply RunsQ.chunk rfl (runs_callUnit_loop (Gt := S.tasks) rfl rfl) hl
        repeat mstepL
        exact .refl _
      · simp [traceObs, Label.obs?]

end Silmaril.Proofs.Wasm.Component.Reference
