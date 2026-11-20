module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Ready

/-!
# A top-level call of the importer from any configuration between calls

`call_atLKTS` of `LinkedSessionFwd` runs the host's invocation of the importer's export from
the configuration `readyCfgL` of `Linked2`, whose instances are exactly `[{}, ιe, ιi]`. For an
abstract exporter the importer sits after all of the exporter's instances, and the store
between calls is whatever the exporter's runs left. Here the same program is run from **any**
configuration `m` ready for the host (`HostReadyCfg`), the importer's instance at an index `ii`
and its export a `canon lift` at function id `j`:

* `call_atG`: the invocation runs (a live run) to the importer's core activation on the lowered
  arguments, at the store `storeG₃ m.store …` (the host caller, the call's task and thread
  appended, the importer's instance entered, the nesting depth one more);
* `CallAtG.ret`: from **any** later store keeping the call's records at their indices (the
  arenas `Gt ++ [y] ++ R`), with any continuation slots, a return of flat results that lift
  resolves the call at an explicit configuration: control empty, the task resolved, the thread
  exited, the importer's thread table reset, the nesting depth one less, the resolution and the
  call's `on_cancel` recorded;
* `CallAtG.trap`: a return whose results do not lift is a specification trap at the returned
  core store.

The records are those of `call_atLKTS` with the importer's instance `ii` in place of `2`
(`taskG₀`, `taskG₁`, `taskG₂`); `enter_eqG` and `unregisterThreadSt_midG` are `enter_eq3` and
`unregisterThreadSt_mid` at an instance found at any index.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## The records of the call -/

/-- The configuration after the host invoked function `j` on `args` as call `k`. -/
def invokedG (m : Machine.Config (E3 P) σ) (k j : Nat) (args : List RVal) :
    Machine.Config (E3 P) σ :=
  { m with
    pending := m.pending ++ [(⟨k⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨k⟩ ⟨j⟩ args)] }

/-- The importer's task of the call (instance `ii`). -/
def taskG₀ (x : SimpleExport) (ii : Nat) (Gc : List (Caller (E3 P))) : Runtime.Task (E3 P) :=
  { ft := liftedFt x, opts := {}, inst := ⟨ii⟩, caller := ⟨Gc.length⟩ }

/-- The importer's task once its implicit thread `t` is registered. -/
def taskG₁ (x : SimpleExport) (ii : Nat) (Gc : List (Caller (E3 P))) (t : ThreadId) :
    Runtime.Task (E3 P) :=
  ({ taskG₀ x ii Gc with implicitThread := some t } : Runtime.Task (E3 P)).addThread t

/-- The importer's task once the call finished. -/
def taskG₂ (x : SimpleExport) (ii : Nat) (Gc : List (Caller (E3 P))) (t : ThreadId) :
    Runtime.Task (E3 P) :=
  { ((taskG₁ x ii Gc t).withState .started).withState .resolved with
    threads := (((taskG₁ x ii Gc t).withState .started).withState .resolved).threads.erase t }

/-- The store when the importer's thread of call `k` starts running. -/
def storeG₁ (S : CStore (E3 P)) (x : SimpleExport) (ii k : Nat) (args : List RVal) :
    CStore (E3 P) :=
  { S with
    tasks := S.tasks ++ [taskG₀ x ii S.callers]
    threads := S.threads ++ [thread₁ S.tasks]
    callers := S.callers ++ [.host ⟨k⟩ args 0]
    nestingDepth := S.nestingDepth + 1 }

/-- The store once the thread entered its task (instance state `ιi'`). -/
def storeG₂ (S : CStore (E3 P)) (x : SimpleExport) (ii : Nat) (ιi' : InstState) (k : Nat)
    (args : List RVal) : CStore (E3 P) :=
  { storeG₁ S x ii k args with
    tasks := S.tasks ++ [taskG₁ x ii S.callers ⟨S.threads.length⟩]
    insts := S.insts.set ii ιi'
    threads := S.threads ++ [(thread₁ S.tasks).withIndex 1] }

/-- The store when the importer's core activation starts. -/
def storeG₃ (S : CStore (E3 P)) (x : SimpleExport) (ii : Nat) (ιi' : InstState) (k : Nat)
    (args : List RVal) : CStore (E3 P) :=
  { storeG₂ S x ii ιi' k args with
    tasks := S.tasks ++ [(taskG₁ x ii S.callers ⟨S.threads.length⟩).withState .started] }

theorem enter_eqG (S : CStore (E3 P)) (x : SimpleExport) (ii k : Nat) (args : List RVal)
    {ιi ιi' : InstState} (hi : S.insts[ii]? = some ιi)
    (hadd : ιi.addThread? ⟨S.threads.length⟩ = some (1, ιi')) :
    CStore.registerThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩
        (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩ (storeG₁ S x ii k args)) =
      storeG₂ S x ii ιi' k args := by
  have h₁ : (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩
      (storeG₁ S x ii k args)).task? ⟨S.tasks.length⟩ =
      some { taskG₀ x ii S.callers with implicitThread := some ⟨S.threads.length⟩ } :=
    tasks_get_last (tasks_modify_last rfl _)
  have h₂ : (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩
      (storeG₁ S x ii k args)).inst? ⟨ii⟩ = some ιi := hi
  unfold CStore.registerThreadSt
  rw [h₁]
  dsimp only
  rw [show ({ taskG₀ x ii S.callers with implicitThread := some ⟨S.threads.length⟩ } :
    Runtime.Task (E3 P)).inst = ⟨ii⟩ from rfl, h₂, Option.bind_some, hadd]
  dsimp only
  simp [storeG₁, storeG₂, CStore.setImplicitThread, ArenaField.modify, ArenaField.set,
    ArenaField.tasks, ArenaField.insts, ArenaField.threads, Arena.modify, Arena.set,
    modify_concat_length, taskG₁, taskG₀, Runtime.Task.addThread, Runtime.Thread.withIndex,
    thread₁]

theorem unregisterThreadSt_midG {s : CStore (E3 P)} {Gt R : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {ii : Nat} {ι : InstState} (t : ThreadId) (i : Nat)
    (ht : s.tasks = Gt ++ [y] ++ R) (hinst : y.inst = ⟨ii⟩) (hi : s.insts[ii]? = some ι) :
    CStore.unregisterThreadSt ⟨Gt.length⟩ t i s =
      { s with
        tasks := Gt ++ [{ y with threads := y.threads.erase t }] ++ R
        insts := s.insts.set ii (InstState.removeThread i ι) } := by
  have h₁ : s.task? ⟨Gt.length⟩ = some y := tasks_get_mid ht
  unfold CStore.unregisterThreadSt
  rw [h₁]
  simp only [ArenaField.modify, ArenaField.tasks, ArenaField.insts, Arena.modify,
    show y.inst.idx = ii by rw [hinst]]
  rw [ht, modify_mid]
  erw [modify_eq_set_of hi]
  rfl

/-! ## The call -/

/-- **Call `k` of the importer's export from a configuration ready for the host**: the start
of its core activation and its return from any later store keeping the call's records. -/
structure CallAtG (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (m : Machine.Config (E3 P) σ) (k j ii : Nat) (x : SimpleExport) (a : Nat) (vs : List IVal)
    (ιi' : InstState) (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a
    (lowerArgs x.ty.params vs)) K, segs⟩ :: rest
  store : M₀.store = storeG₃ m.store x ii ιi' k (vs.map toRefVal)
  core : M₀.core = m.core
  host : M₀.host = m.host
  pending : M₀.pending = m.pending ++ [(⟨k⟩, ⟨j⟩, vs.map toRefVal)]
  results : M₀.results = m.results
  cancels : M₀.cancels = m.cancels
  thread : th = some ⟨m.store.threads.length⟩
  ret : ∀ (S' : CStore (E3 P)) (C' : List (Option (Activation (E3 P) σ)))
    (RT : List (Runtime.Task (E3 P))) (RH : List Runtime.Thread) (CL : List (Caller (E3 P)))
    (y : CoreSt (E3 P)) (zs : List Flat) (ws : List IVal),
    S'.tasks = m.store.tasks ++
      [(taskG₁ x ii m.store.callers ⟨m.store.threads.length⟩).withState .started] ++ RT →
    S'.threads = m.store.threads ++ [(thread₁ m.store.tasks).withIndex 1] ++ RH →
    S'.callers = m.store.callers ++ [.host ⟨k⟩ (vs.map toRefVal) 0] ++ CL →
    S'.insts[ii]? = some ιi' → S'.lockdown = false →
    zs.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results zs = some ws →
    ∃ (tr : List (Label (E3 P) σ)) (mE : Machine.Config (E3 P) σ),
      LRun prof (fun _ _ => false) (DI P impl)
        (retCfg { M₀ with store := S', conts := C' } th K segs rest y zs) tr mE ∧
      mE = { M₀ with
        store := { S' with
          tasks := m.store.tasks ++ [taskG₂ x ii m.store.callers ⟨m.store.threads.length⟩] ++ RT
          threads := m.store.threads ++
            [{ (thread₁ m.store.tasks).withIndex 1 with status := .exited }] ++ RH
          insts := S'.insts.set ii (InstState.removeThread 1 ιi')
          nestingDepth := S'.nestingDepth - 1 }
        core := y.1
        conts := C'
        ctl := []
        results := M₀.results ++ [(⟨k⟩, some (ws.map toRefVal))]
        cancels := (⟨k⟩, .task ⟨m.store.tasks.length⟩) :: M₀.cancels.filter (·.1 != ⟨k⟩) }
  trap : ∀ (S' : CStore (E3 P)) (C' : List (Option (Activation (E3 P) σ))) (y : CoreSt (E3 P))
    (zs : List Flat), S'.lockdown = false →
    zs.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results zs = none →
    TrapsAtS prof P impl (retCfg { M₀ with store := S', conts := C' } th K segs rest y zs) y.1

/-- **The host's call `k` of the importer's export `j`** (a `canon lift` of the core address
`a` at instance `ii`) from a configuration whose store is not locked down. -/
theorem call_atG (prof : ProfileKind) (m : Machine.Config (E3 P) σ)
    (hl : m.store.lockdown = false) (k j a ii : Nat) (x : SimpleExport) (vs : List IVal)
    (hff : floatFreeList x.ty.params = true) (hck : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16) (hres : x.ty.results.length ≤ 1)
    (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true) {ιi : InstState}
    (hii : m.store.insts[ii]? = some ιi) (hth : ThreadsOk ιi)
    (hf : m.store.funcs[j]? = some (.lifted a (liftedFt x) {} ⟨ii⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (fun _ _ => false) (DI P impl)
      (invokedG m k j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtG prof P impl m k j ii x a vs (enterInst ιi ⟨m.store.threads.length⟩) M₀ th K segs
        rest := by
  have hadd : ιi.addThread? ⟨m.store.threads.length⟩ =
      some (1, enterInst ιi ⟨m.store.threads.length⟩) := addThread?_ok hth _
  have hrem : (enterInst ιi ⟨m.store.threads.length⟩).removeThread? 1 =
      some (⟨m.store.threads.length⟩,
        InstState.removeThread 1 (enterInst ιi ⟨m.store.threads.length⟩)) :=
    removeThread?_enter ιi _
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (fun _ _ => false) (DI P impl) (invokedG m k j (vs.map toRefVal)) _ _
    unfold invokedG
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (.host ⟨k⟩ (vs.map toRefVal) 0) _ rfl) (by exact hl)
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) (by exact hl)
    apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl) (.call rfl)
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (by exact hf)) (by exact hl)
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) (by exact hl)
    show LRun prof (fun _ _ => false) (DI P impl) _ _ _
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) (by exact hl)
    apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) (by exact hl)
    apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) (by exact hl)
    apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl)
      (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
    have e₁ : ∀ S : CStore (E3 P),
        S.threads = m.store.threads ++ [{ task := ⟨m.store.tasks.length⟩ }] →
        threadStatusSt ⟨m.store.threads.length⟩ .running S =
          { S with threads := m.store.threads ++ [thread₁ m.store.tasks] } :=
      fun S h => threadStatus_last h _
    apply LRun.store_congr (S' := storeG₁ m.store x ii k (vs.map toRefVal))
      ((e₁ _ rfl).trans rfl)
    apply RunsQ.chunk (th := some ⟨m.store.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨m.store.tasks.length⟩) (a := true) rfl
      (runs_enterG (impl := impl) (Gt := m.store.tasks) (y := taskG₀ x ii m.store.callers) rfl
        rfl (by exact hii) hadd) (by exact hl)
    apply LRun.store_congr (by exact enter_eqG m.store x ii k (vs.map toRefVal) hii hadd)
    have hS₂ : (storeG₂ m.store x ii (enterInst ιi ⟨m.store.threads.length⟩) k
        (vs.map toRefVal)).tasks =
        m.store.tasks ++ [taskG₁ x ii m.store.callers ⟨m.store.threads.length⟩] := rfl
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last hS₂)) (by exact hl)
    apply RunsQ.chunk rfl (runs_start (Gt := m.store.tasks) (Gc := m.store.callers) hS₂ rfl rfl)
      (by exact hl)
    have hlow : ∀ (cx : LiftLowerContext (E3 P)) (m' : Machine.Config (E3 P) σ),
        RunsQ (DI P impl) (some ⟨m.store.threads.length⟩)
          (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams (vs.map toRefVal)
            (paramTypes (liftedFt x)) none) m' [.tau] (lowerArgs x.ty.params vs) m' :=
      fun cx m' => runs_lowerP x.ty vs cx hff hck hmax m'
    apply RunsQ.chunk rfl (hlow _ _) (by exact hl)
    apply LRun.store_congr
      (S' := storeG₃ m.store x ii (enterInst ιi ⟨m.store.threads.length⟩) k (vs.map toRefVal))
      (setTaskState_last (Gt := m.store.tasks) rfl _)
    lstep hl
    exact .refl _
  apply CallAtG.mk
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro S' C' RT RH CL y zs ws hT hTh hC hI hl' hys hws
    have hlift : ∀ (cx : LiftLowerContext (E3 P)) (m' : Machine.Config (E3 P) σ), ∃ c,
        RunsQ (DI P impl) (some ⟨m.store.threads.length⟩) (liftFlatValues Limits.spec
          Quirks.none cx ABI.maxFlatResults (.ofList zs) (resultTypes (witFt x.ty))) m' [.tau]
          (ws.map toRefVal, c) m' :=
      runs_lift_someP x.ty hres hmaxr hffr hys hws
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · show LRun prof (fun _ _ => false) (DI P impl) (retCfg _ _ _ _ _ y zs) _ _
      unfold retCfg
      apply RunsQ.chunk2 rfl (hlift _ _).choose_spec (by exact hl')
      apply RunsQ.chunk2 rfl (runs_returnM (Gt := m.store.tasks) (R := RT)
        (Gc := m.store.callers) (CL := CL) _ (by exact hT) rfl rfl rfl (by exact hC))
        (by exact hl')
      apply LRun.store_congr (setTaskState_mid (Gt := m.store.tasks) (by exact hT) _)
      apply RunsQ.chunk rfl (runs_exitM (Gt := m.store.tasks) (R := RT)
        (Gth := m.store.threads) (R' := RH) rfl rfl rfl rfl (by exact hTh) rfl (by exact hI)
        hrem) (by exact hl')
      apply LRun.store_congr (unregisterThreadSt_midG _ _ rfl rfl (by exact hI))
      show LRun prof (fun _ _ => false) (DI P impl) _ _ _
      lstep hl'
      apply LRun.store_congr (threadStatus_mid (Gth := m.store.threads) (by exact hTh) _)
      apply RunsQ.chunk rfl (runs_callUnit_loopM (Gt := m.store.tasks) (R := RT) rfl rfl)
        (by exact hl')
      lstep hl'
      lstep hl'
      lstep hl'
      exact .refl _
    · rw [hostFinish_cancel _ m.pending ⟨k⟩ ⟨j⟩ (vs.map toRefVal) _ rfl]
      rfl
  · intro S' C' y zs hl' hys hn
    exact lrun_lift_trapAtS x.ty hres hmaxr hffr hys hn rfl (by exact hl')

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
