module

public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Reference.MultiPath

/-!
# Sequences of calls over `core3R P V IR`: the path of call `k`

A copy of `Silmaril.Proofs.Wasm.Component.Reference.MultiPath` with `core3P P` replaced by
`core3R P V IR` (provenance: copy; proofs unchanged).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

variable {P : Profile} {σ : Type}

/-- The task of the call. -/
def task₀ (x : SimpleExport) (Gc : List (Caller (E3 P V IR))) : Runtime.Task (E3 P V IR) :=
  { ft := liftedFt x, opts := {}, inst := ⟨0⟩, caller := ⟨Gc.length⟩ }

/-- The task once its implicit thread `t` is registered. -/
def task₁ (x : SimpleExport) (Gc : List (Caller (E3 P V IR))) (t : ThreadId) : Runtime.Task (E3 P V IR) :=
  ({ task₀ x Gc with implicitThread := some t } : Runtime.Task (E3 P V IR)).addThreadR t

/-- The thread of the call, running. -/
def thread₁ (Gt : List (Runtime.Task (E3 P V IR))) : Runtime.Thread :=
  { status := .running, task := ⟨Gt.length⟩ }

/-- The store when the thread of call `k` starts running. -/
def store₁ (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (x : SimpleExport) (k : Nat)
    (args : List Val) : CStore (E3 P V IR) :=
  { readyStore cs ι fs G with
    tasks := G.tasks ++ [task₀ x G.callers]
    threads := G.threads ++ [thread₁ G.tasks]
    callers := G.callers ++ [.host ⟨k⟩ args 0]
    nestingDepth := 1 }

/-- The store once the thread entered its task. -/
def store₂ (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι ι' : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (x : SimpleExport) (k : Nat)
    (args : List Val) : CStore (E3 P V IR) :=
  { store₁ cs ι fs G x k args with
    tasks := G.tasks ++ [task₁ x G.callers ⟨G.threads.length⟩]
    insts := [ι']
    threads := G.threads ++ [(thread₁ G.tasks).withIndex 1] }

/-- The store when the core activation starts. -/
def store₃ (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι ι' : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (x : SimpleExport) (k : Nat)
    (args : List Val) : CStore (E3 P V IR) :=
  { store₂ cs ι ι' fs G x k args with
    tasks := G.tasks ++ [(task₁ x G.callers ⟨G.threads.length⟩).withState .started] }

/-- The store when the call resolved (core store `cs'`). -/
def store₄ (cs' : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι ι' : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (x : SimpleExport) (k : Nat)
    (args : List Val) : CStore (E3 P V IR) :=
  { store₃ cs' ι ι' fs G x k args with
    tasks := G.tasks ++ [((task₁ x G.callers ⟨G.threads.length⟩).withState .started).withState
      .resolved] }

/-- The task of call `k` once finished. -/
def task₂ (x : SimpleExport) (Gc : List (Caller (E3 P V IR))) (t : ThreadId) : Runtime.Task (E3 P V IR) :=
  { ((task₁ x Gc t).withState .started).withState .resolved with
    threads := (((task₁ x Gc t).withState .started).withState .resolved).threads.erase t }

/-- The store when the thread of call `k` exited. -/
def store₅ (cs' : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι ι' : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (x : SimpleExport) (k : Nat)
    (args : List Val) : CStore (E3 P V IR) :=
  { store₄ cs' ι ι' fs G x k args with
    tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
    insts := [InstState.removeThread 1 ι']
    threads := G.threads ++ [{ (thread₁ G.tasks).withIndex 1 with status := .exited }] }

/-- The leftovers after call `k` of function `j` on `args` with results `rs`. -/
def nextGarb (G : Garb P V IR) (x : SimpleExport) (k j : Nat) (a : (E3 P V IR).FuncAddr)
    (args rs : List Val) : Garb P V IR where
  tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
  threads := G.threads ++ [{ (thread₁ G.tasks).withIndex 1 with status := .exited }]
  callers := G.callers ++ [.host ⟨k⟩ args 0]
  conts := Config.setSlot (Config.setSlot G.conts G.threads.length
    (some (threadAct (D P V IR) ⟨G.threads.length⟩ (.liftImplicit ⟨G.tasks.length⟩ a))))
    G.threads.length none
  pending := G.pending ++ [(⟨k⟩, ⟨j⟩, args)]
  results := G.results ++ [(⟨k⟩, some rs)]
  cancels := (⟨k⟩, .task ⟨G.tasks.length⟩) :: G.cancels.filter (·.1 != ⟨k⟩)

/-- From `mS` the call resolves at the configuration `mE`. -/
def ResolvesAt (prof : ProfileKind) (P : Profile) (mS mE : Machine.Config (E3 P V IR) Unit) : Prop :=
  ∃ tr mE', LRun prof (refHostR P V IR).hr (D P V IR) mS tr mE' ∧ mE' = mE

/-- The configuration `M₀` of call `k` runs the core activation of export `x` (address `a`)
on the lowered values of `vs`; when it returns flat values of the result types, the call
resolves at the next configuration between calls, or traps, as the IR lift prescribes. -/
structure CallAtK (prof : ProfileKind) (P : Profile) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (ι' : InstState) (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR) (k j : Nat)
    (x : SimpleExport) (a : (E3 P V IR).FuncAddr) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P V IR) Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P V IR) Unit (Ret (E3 P V IR))) (segs : List (Seg (E3 P V IR) Unit))
    (rest : List (Activation (E3 P V IR) Unit)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a
    (lowerArgs x.ty.params vs)) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  ret : ∀ (y : CoreSt (E3 P V IR)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ResolvesAt prof P (retCfg M₀ th K segs rest y ys)
      (readyCfg y.1 (InstState.removeThread 1 ι') fs
        (nextGarb G x k j a (vs.map toRefVal) (ws.map toRefVal)))
  trap : ∀ (y : CoreSt (E3 P V IR)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNext prof P (retCfg M₀ th K segs rest y ys)

/-- **The deterministic parts of call `k`** from a configuration between calls. -/
theorem call_at_k (prof : ProfileKind) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (ι ι' : InstState) (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR) (k j : Nat)
    (a : (E3 P V IR).FuncAddr) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hadd : ι.addThread? ⟨G.threads.length⟩ = some (1, ι'))
    (hrem : ι'.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι'))
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (refHostR P V IR).hr (D P V IR)
      (invokedAt cs ι fs G k j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtK prof P cs ι' fs G k j x a vs M₀ th K segs rest := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (refHostR P V IR).hr (D P V IR) (invokedAt cs ι fs G k j (vs.map toRefVal)) _ _
    unfold invokedAt
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (.host ⟨k⟩ (vs.map toRefVal) 0) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P V IR), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) :=
      funcs_get? hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl
      (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
    have e₁ : ∀ S : CStore (E3 P V IR), S.threads = G.threads ++ [{ task := ⟨G.tasks.length⟩ }] →
        threadStatusSt ⟨G.threads.length⟩ .running S =
          { S with threads := G.threads ++ [thread₁ G.tasks] } :=
      fun S h => threadStatus_last h _
    apply LRun.store_congr (S' := store₁ cs ι fs G x k (vs.map toRefVal)) ((e₁ _ rfl).trans rfl)
    have hS₁ : (store₁ cs ι fs G x k (vs.map toRefVal)).insts = [ι] := rfl
    apply RunsQ.chunk (th := some ⟨G.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨G.tasks.length⟩) (a := true) rfl
      (runs_enter (Gt := G.tasks) (y := task₀ x G.callers) rfl rfl rfl hS₁ hadd) rfl
    have e₂ : CStore.registerThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩
        (CStore.setImplicitThread ⟨G.tasks.length⟩ ⟨G.threads.length⟩
          (store₁ cs ι fs G x k (vs.map toRefVal))) = store₂ cs ι ι' fs G x k (vs.map toRefVal) :=
      enter_eq rfl rfl rfl hadd rfl
    apply LRun.store_congr (S' := store₂ cs ι ι' fs G x k (vs.map toRefVal)) (by exact e₂)
    have hS₂ : (store₂ cs ι ι' fs G x k (vs.map toRefVal)).tasks =
        G.tasks ++ [task₁ x G.callers ⟨G.threads.length⟩] := rfl
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last (Gt := G.tasks) hS₂))
      rfl
    apply RunsQ.chunk rfl (runs_start (Gt := G.tasks) (Gc := G.callers) hS₂ rfl rfl) rfl
    have hlow : ∀ (cx : LiftLowerContext (E3 P V IR)) (m : Machine.Config (E3 P V IR) Unit),
        RunsQ (D P V IR) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatParams (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau]
          (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lower x vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    apply LRun.store_congr (S' := store₃ cs ι ι' fs G x k (vs.map toRefVal))
      (setTaskState_last (Gt := G.tasks) rfl _)
    mstep
    exact .refl _

  apply CallAtK.mk
  · rfl
  · rfl
  · rfl
  · show ∀ (y : CoreSt (E3 P V IR)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
      ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
      ResolvesAt prof P _ (readyCfg y.1 (InstState.removeThread 1 ι') fs
        (nextGarb G x k j a (vs.map toRefVal) (ws.map toRefVal)))
    intro y ys ws hys hws
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · show LRun prof (refHostR P V IR).hr (D P V IR) (retCfg _ _ _ _ _ y ys) _ _
      apply LRun.store_congr (S' := store₃ y.1 ι ι' fs G x k (vs.map toRefVal)) rfl
      have hS₃ : (store₃ y.1 ι ι' fs G x k (vs.map toRefVal)).tasks =
          G.tasks ++ [(task₁ x G.callers ⟨G.threads.length⟩).withState .started] := rfl
      unfold retCfg
      apply RunsQ.chunk2 rfl (runs_lift_some x hres hmaxr hffr hys hws _ _).choose_spec rfl
      apply RunsQ.chunk2 rfl
        (runs_return (Gt := G.tasks) (Gc := G.callers) _ hS₃ rfl rfl rfl rfl) rfl
      apply LRun.store_congr (S' := store₄ y.1 ι ι' fs G x k (vs.map toRefVal))
        (by refine setTaskState_last (Gt := G.tasks) ?_ _; rfl)
      apply RunsQ.chunk rfl
        (runs_exit (Gt := G.tasks) (Gth := G.threads)
          (y := ((task₁ x G.callers ⟨G.threads.length⟩).withState .started).withState .resolved)
          (z := (thread₁ G.tasks).withIndex 1) (ι := ι') rfl rfl rfl rfl rfl rfl rfl rfl hrem) rfl
      have e₄ : CStore.unregisterThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩ 1
          (store₄ y.1 ι ι' fs G x k (vs.map toRefVal)) =
            { store₄ y.1 ι ι' fs G x k (vs.map toRefVal) with
              tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
              insts := [InstState.removeThread 1 ι'] } :=
        unregisterThreadSt_eq _ _ rfl rfl rfl
      apply LRun.store_congr (S' := { store₄ y.1 ι ι' fs G x k (vs.map toRefVal) with
          tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
          insts := [InstState.removeThread 1 ι'] }) e₄
      mstep
      have e₅ : threadStatusSt ⟨G.threads.length⟩ .exited
          { store₄ y.1 ι ι' fs G x k (vs.map toRefVal) with
            tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
            insts := [InstState.removeThread 1 ι'] } = store₅ y.1 ι ι' fs G x k (vs.map toRefVal) :=
        threadStatus_last (z := (thread₁ G.tasks).withIndex 1) rfl _
      apply LRun.store_congr (S' := store₅ y.1 ι ι' fs G x k (vs.map toRefVal)) e₅
      apply RunsQ.chunk rfl (runs_callUnit_loop (Gt := G.tasks) rfl rfl) rfl
      mstep
      mstep
      mstep
      exact .refl _
    · rw [hostFinish_cancel _ G.pending ⟨k⟩ ⟨j⟩ (vs.map toRefVal) _ rfl]
      rfl
  · intro y ys hys hn
    exact lrun_lift_trap prof x hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Param.Core3R
