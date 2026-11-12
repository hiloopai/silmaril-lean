module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiPath
public import Silmaril.Proofs.Wasm.Component.Reference.CallI

/-!
# The deterministic parts of an export call with imports between other calls

`call_at_kA`: `call_atA` (the host `answerHostS P g` (a stateful host; `answerHost P g` is its stateless instance)) from the configuration between calls
`readyCfgI` (`readyCfg` with the subtasks left by earlier callouts), as top-level call `k`,
following `call_at_k`. The core activation may make callouts, which append subtask and caller
records (`extSC`); a resolved call ends at the next configuration between calls, whose caller
records and subtasks keep them.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Val → Option (List Val × σ)}

/-! ## Configurations between calls with callout records -/

/-- The store between calls, with the subtasks `ST` of earlier callouts. -/
def readyStoreI (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) : CStore (E3 P) :=
  { readyStore cs ι fs G with subtasks := ST }

/-- The configuration between calls, with the subtasks `ST` of earlier callouts, in host state
`h`. -/
def readyCfgI (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h : σ) :
    Machine.Config (E3 P) σ :=
  { readyCfgH cs ι fs G h with store := readyStoreI cs ι fs G ST }

/-- The configuration after the host invoked function `j` on `args` as call `k`. -/
def invokedAtI (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h : σ) (k j : Nat)
    (args : List Val) : Machine.Config (E3 P) σ :=
  { readyCfgI cs ι fs G ST h with
    pending := G.pending ++ [(⟨k⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨k⟩ ⟨j⟩ args)] }

/-- A store of call `k` with the subtasks `SS`. -/
def storeS (S : CStore (E3 P)) (SS : List Subtask) : CStore (E3 P) :=
  { S with subtasks := SS }

/-- A store of call `k` with the subtasks `SS` and the caller records `CL` of callouts after its
host caller record. -/
def storeSC (S : CStore (E3 P)) (SS : List Subtask) (Gc CL : List (Caller (E3 P))) (k : Nat)
    (args : List Val) : CStore (E3 P) :=
  { S with subtasks := SS, callers := Gc ++ [.host ⟨k⟩ args 0] ++ CL }

/-- The leftovers after call `k` of function `j` on `args` with results `rs`, whose callouts
appended the caller records `CL`. -/
def nextGarbA (P : Profile) (g : σ → HostFuncId → List Val → Option (List Val × σ)) (G : Garb P σ)
    (x : SimpleExport) (k j : Nat) (a : (E3 P).FuncAddr) (args rs : List Val)
    (CL : List (Caller (E3 P))) : Garb P σ :=
  { tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
    threads := G.threads ++ [{ (thread₁ G.tasks).withIndex 1 with status := .exited }]
    pending := G.pending ++ [(⟨k⟩, ⟨j⟩, args)]
    results := G.results ++ [(⟨k⟩, some rs)]
    cancels := (⟨k⟩, .task ⟨G.tasks.length⟩) :: G.cancels.filter (·.1 != ⟨k⟩)
    callers := G.callers ++ [.host ⟨k⟩ args 0] ++ CL
    conts := Config.setSlot (Config.setSlot G.conts G.threads.length
      (some (threadAct (DA P g) ⟨G.threads.length⟩ (.liftImplicit ⟨G.tasks.length⟩ a))))
      G.threads.length none }

/-- From `mS` the call resolves at the configuration `mE`, under `answerHostS P g`. -/
def ResolvesAtA (prof : ProfileKind) (P : Profile) (g : σ → HostFuncId → List Val → Option (List Val × σ))
    (mS mE : Machine.Config (E3 P) σ) : Prop :=
  ∃ tr mE', LRun prof (answerHostS P g).hr (DA P g) mS tr mE' ∧ mE' = mE

/-! ## Caller records with callout records after them -/

theorem callers_get_mid {s : CStore (E3 P)} {Gc CL : List (Caller (E3 P))} {y : Caller (E3 P)}
    (h : s.callers = Gc ++ [y] ++ CL) :
    ArenaField.callers.get? s (⟨Gc.length⟩ : CallerId) = some y := by
  show (s.callers)[Gc.length]? = some y
  rw [h, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

variable {impl : HostImpl (E3 P) σ}

theorem runs_onResolveSC {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gc CL : List (Caller (E3 P))} {c : CallId} {args : List Val} (r : Option (List Val))
    (hc : m.store.callers = Gc ++ [.host c args 0] ++ CL) :
    RunsQ (DI P impl) th (DI P impl (.onResolve ⟨Gc.length⟩ r)) m [.tau, .obs (.resolved c r)]
      .unit (m.resolve c r) := by
  show RunsQ _ _ (callerOnResolve Limits.spec Quirks.none ⟨Gc.length⟩ r) _ _ _ _
  unfold callerOnResolve
  exact RunsQ.bind (runs_getObj ArenaField.callers _ _ (callers_get_mid hc))
    (RunsQ.bind (tr₁ := [.obs (.resolved c r)]) (.emit (.pure _ _)) (.pure _ _))

/-- `Task.return_` with callout records after the host caller record. -/
theorem runs_returnSC {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gc CL : List (Caller (E3 P))}
    {c : CallId} {args : List Val} (vs : List Val) (ht : m.store.tasks = Gt ++ [y])
    (hy : y.caller = ⟨Gc.length⟩) (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : m.store.callers = Gc ++ [.host c args 0] ++ CL) :
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
  apply RunsQ.bind (RunsQ.call (runs_onResolveSC (some vs) hc) (.pure _ _))
  exact runs_modifyStore _ _ rfl
  rfl

/-! ## Call `k` -/

/-- The configuration `M₀` of call `k` runs the core activation of export `x` (address `a`) on
the lowered values of `vs`; when it returns flat values of the result types, after callouts that
appended subtask and caller records, the call resolves at the next configuration between calls,
or traps, as the IR lift prescribes. -/
structure CallAtKA (prof : ProfileKind) (P : Profile)
    (g : σ → HostFuncId → List Val → Option (List Val × σ)) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι' : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST₀ : List Subtask)
    (k j : Nat) (x : SimpleExport) (a : (E3 P).FuncAddr) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a
    (lowerArgs x.ty.params vs)) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  funcs : M₀.store.funcs = fs
  entry : ∀ f ft opts, calloutEntry M₀.store th (.lowered f ft opts ⟨0⟩) = none
  inst : ArenaField.insts.get? M₀.store ⟨0⟩ = some ι'
  ret : ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P))) (y : CoreSt (E3 P))
    (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ResolvesAtA prof P g (retCfg (extSC (withH M₀ s) ST CL) th K segs rest y ys)
      (readyCfgI y.1 (InstState.removeThread 1 ι') fs
        (nextGarbA P g G x k j a (vs.map toRefVal) (ws.map toRefVal) CL) (ST₀ ++ ST) s)
  trap : ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P))) (y : CoreSt (E3 P))
    (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextA prof P g (retCfg (extSC (withH M₀ s) ST CL) th K segs rest y ys)

/-- The entry check of a callout of instance `0` from the thread of call `k`. -/
theorem calloutEntry_k {S : CStore (E3 P)} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    (ht : S.tasks = Gt ++ [y]) (hth : S.threads = Gth ++ [z]) (hz : z.task = ⟨Gt.length⟩)
    (hy : y.inst = ⟨0⟩) (f : FuncId) (ft : WIT.FuncType Empty RtId) (opts : CanonOpts (E3 P)) :
    calloutEntry S (some ⟨Gth.length⟩) (.lowered f ft opts ⟨0⟩) = none := by
  have h₁ : ArenaField.threads.get? S (⟨Gth.length⟩ : ThreadId) = some z := threads_get_last hth
  have h₂ : ArenaField.tasks.get? S z.task = some y := by
    rw [hz]
    exact tasks_get_last ht
  have h₃ : instOfThread? S (some ⟨Gth.length⟩) = some ⟨0⟩ := by
    simp only [instOfThread?, h₁, h₂, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp only [calloutEntry, h₃, ↓reduceIte]

/-- **The deterministic parts of call `k` with imports** from a configuration between calls. -/
theorem call_at_kA (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι ι' : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST₀ : List Subtask)
    (h₀ : σ) (k j : Nat) (a : (E3 P).FuncAddr) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hadd : ι.addThread? ⟨G.threads.length⟩ = some (1, ι'))
    (hrem : ι'.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι'))
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (answerHostS P g).hr (DA P g)
      (invokedAtI cs ι fs G ST₀ h₀ k j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtKA prof P g cs ι' fs G ST₀ k j x a vs M₀ th K segs rest ∧ M₀.host = h₀ := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (answerHostS P g).hr (DA P g)
      (invokedAtI cs ι fs G ST₀ h₀ k j (vs.map toRefVal)) _ _
    unfold invokedAtI
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (.host ⟨k⟩ (vs.map toRefVal) 0) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) :=
      funcs_get? hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (runs_ite_false (impl := answerImplS g) (by exact threadIs_last rfl) _ _)
      rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl
      (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
    have e₁ : ∀ S : CStore (E3 P), S.threads = G.threads ++ [{ task := ⟨G.tasks.length⟩ }] →
        threadStatusSt ⟨G.threads.length⟩ .running S =
          { S with threads := G.threads ++ [thread₁ G.tasks] } :=
      fun S h => threadStatus_last h _
    apply LRun.store_congr
      (S' := storeS (store₁ cs ι fs G x k (vs.map toRefVal)) ST₀)
      ((e₁ _ rfl).trans rfl)
    have hS₁ : (storeS (store₁ cs ι fs G x k (vs.map toRefVal)) ST₀).insts = [ι] := rfl
    apply RunsQ.chunk (th := some ⟨G.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨G.tasks.length⟩) (a := true) rfl
      (runs_enter (Gt := G.tasks) (y := task₀ x G.callers) rfl rfl rfl hS₁ hadd) rfl
    have e₂ : CStore.registerThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩
        (CStore.setImplicitThread ⟨G.tasks.length⟩ ⟨G.threads.length⟩
          (storeS (store₁ cs ι fs G x k (vs.map toRefVal)) ST₀)) =
        storeS (store₂ cs ι ι' fs G x k (vs.map toRefVal)) ST₀ :=
      enter_eq rfl rfl rfl hadd rfl
    apply LRun.store_congr (by exact e₂)
    have hS₂ : (storeS (store₂ cs ι ι' fs G x k (vs.map toRefVal)) ST₀).tasks = G.tasks ++ [task₁ x G.callers ⟨G.threads.length⟩] := rfl
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last hS₂)) rfl
    apply RunsQ.chunk rfl (runs_start (impl := answerImplS g) (Gt := G.tasks) (Gc := G.callers)
      hS₂ rfl rfl) rfl
    have hlow : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ),
        RunsQ (DA P g) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatParams (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau]
          (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lowerA x vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    apply LRun.store_congr
      (S' := storeS (store₃ cs ι ι' fs G x k (vs.map toRefVal)) ST₀)
      (setTaskState_last (Gt := G.tasks) rfl _)
    mstep
    exact .refl _
  refine ⟨?_, rfl⟩
  apply CallAtKA.mk
  · rfl
  · rfl
  · rfl
  · rfl
  · exact calloutEntry_k (Gt := G.tasks) (Gth := G.threads) rfl rfl rfl rfl
  · rfl
  · show ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P))) (y : CoreSt (E3 P))
      (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
      ResolvesAtA prof P g (retCfg (extSC (withH _ s) ST CL) _ _ _ _ y ys) (readyCfgI y.1
        (InstState.removeThread 1 ι') fs
        (nextGarbA P g G x k j a (vs.map toRefVal) (ws.map toRefVal) CL) (ST₀ ++ ST) s)
    intro s ST CL y ys ws hys hws
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · show LRun prof (answerHostS P g).hr (DA P g) (retCfg _ _ _ _ _ y ys) _ _
      apply LRun.store_congr
        (S' := storeSC (store₃ y.1 ι ι' fs G x k (vs.map toRefVal)) (ST₀ ++ ST) G.callers CL k
          (vs.map toRefVal)) rfl
      have hS₃ : (storeSC (store₃ y.1 ι ι' fs G x k (vs.map toRefVal)) (ST₀ ++ ST) G.callers CL k
          (vs.map toRefVal)).tasks =
          G.tasks ++ [(task₁ x G.callers ⟨G.threads.length⟩).withState .started] := rfl
      unfold retCfg
      apply RunsQ.chunk2 rfl (runs_lift_someA (g := g) x hres hmaxr hffr hys hws _ _).choose_spec
        rfl
      apply RunsQ.chunk2 rfl
        (runs_returnSC (Gt := G.tasks) (Gc := G.callers) (CL := CL) _ hS₃ rfl rfl rfl rfl) rfl
      apply LRun.store_congr
        (S' := storeSC (store₄ y.1 ι ι' fs G x k (vs.map toRefVal)) (ST₀ ++ ST) G.callers CL k
          (vs.map toRefVal))
        (by refine setTaskState_last (Gt := G.tasks) ?_ _; rfl)
      apply RunsQ.chunk rfl
        (runs_exit (impl := answerImplS g) (Gt := G.tasks) (Gth := G.threads)
          (y := ((task₁ x G.callers ⟨G.threads.length⟩).withState .started).withState .resolved)
          (z := (thread₁ G.tasks).withIndex 1) (ι := ι') rfl rfl rfl rfl rfl rfl rfl rfl hrem) rfl
      have e₄ : CStore.unregisterThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩ 1
          (storeSC (store₄ y.1 ι ι' fs G x k (vs.map toRefVal)) (ST₀ ++ ST) G.callers CL k
            (vs.map toRefVal)) =
            { storeSC (store₄ y.1 ι ι' fs G x k (vs.map toRefVal)) (ST₀ ++ ST) G.callers CL k
                (vs.map toRefVal) with
              tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
              insts := [InstState.removeThread 1 ι'] } :=
        unregisterThreadSt_eq _ _ rfl rfl rfl
      apply LRun.store_congr e₄
      mstep
      have e₅ : threadStatusSt ⟨G.threads.length⟩ .exited
          { storeSC (store₄ y.1 ι ι' fs G x k (vs.map toRefVal)) (ST₀ ++ ST) G.callers CL k
              (vs.map toRefVal) with
            tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
            insts := [InstState.removeThread 1 ι'] } =
          storeSC (store₅ y.1 ι ι' fs G x k (vs.map toRefVal)) (ST₀ ++ ST) G.callers CL k
            (vs.map toRefVal) :=
        threadStatus_last (z := (thread₁ G.tasks).withIndex 1) rfl _
      apply LRun.store_congr e₅
      apply RunsQ.chunk rfl (runs_callUnit_loop (impl := answerImplS g) (Gt := G.tasks) rfl rfl) rfl
      mstep
      mstep
      mstep
      exact .refl _
    · rw [hostFinish_cancel _ G.pending ⟨k⟩ ⟨j⟩ (vs.map toRefVal) _ rfl]
      rfl
  · intro s ST CL y ys hys hn
    exact lrun_lift_trapA prof x hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Reference
