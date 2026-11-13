module

public import Silmaril.Proofs.Wasm.Component.Reference.CallKI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.CallKI` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.CallKI` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)}

/-! ## Configurations between calls with callout records -/

/-- The store between calls, with the subtasks `ST` of earlier callouts. -/
def readyStoreI (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (ST : List Subtask) : CStore (E3 P V IR) :=
  { readyStore cs ι fs G with subtasks := ST }

/-- The configuration between calls, with the subtasks `ST` of earlier callouts, in host state
`h`. -/
def readyCfgI (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (ST : List Subtask) (h : σ) :
    Machine.Config (E3 P V IR) σ :=
  { readyCfgH cs ι fs G h with store := readyStoreI cs ι fs G ST }

/-- The leftovers after call `k` of function `j` on `args` with results `rs`, whose callouts
appended the caller records `CL`. -/
def nextGarbA (P : Profile) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (G : Garb P V IR σ)
    (x : SimpleExport) (k j : Nat) (a : (E3 P V IR).FuncAddr) (args rs : List Silmaril.Wasm.Component.Reference.Val)
    (CL : List (Caller (E3 P V IR))) : Garb P V IR σ :=
  { tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
    threads := G.threads ++ [{ (thread₁ G.tasks).withIndex 1 with status := .exited }]
    pending := G.pending ++ [(⟨k⟩, ⟨j⟩, args)]
    results := G.results ++ [(⟨k⟩, some rs)]
    cancels := (⟨k⟩, .task ⟨G.tasks.length⟩) :: G.cancels.filter (·.1 != ⟨k⟩)
    callers := G.callers ++ [.host ⟨k⟩ args 0] ++ CL
    conts := Config.setSlot (Config.setSlot G.conts G.threads.length
      (some (threadAct (DA P g) ⟨G.threads.length⟩ (.liftImplicit ⟨G.tasks.length⟩ a))))
      G.threads.length none }

/-- From `mS` the call resolves at the configuration `mE`, under `answerHostS P V IR g`. -/
def ResolvesAtA (prof : ProfileKind) (P : Profile) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (mS mE : Machine.Config (E3 P V IR) σ) : Prop :=
  ∃ tr mE', LRun prof (answerHostS P V IR g).hr (DA P g) mS tr mE' ∧ mE' = mE

/-! ## Caller records with callout records after them -/

theorem callers_get_mid {s : CStore (E3 P V IR)} {Gc CL : List (Caller (E3 P V IR))} {y : Caller (E3 P V IR)}
    (h : s.callers = Gc ++ [y] ++ CL) :
    ArenaField.callers.get? s (⟨Gc.length⟩ : CallerId) = some y := by
  show (s.callers)[Gc.length]? = some y
  rw [h, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

variable {impl : HostImpl (E3 P V IR) σ}

theorem runs_onResolveSC {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {Gc CL : List (Caller (E3 P V IR))} {c : CallId} {args : List Silmaril.Wasm.Component.Reference.Val} (r : Option (List Silmaril.Wasm.Component.Reference.Val))
    (hc : m.store.callers = Gc ++ [.host c args 0] ++ CL) :
    RunsQ (DI P impl) th (DI P impl (.onResolve ⟨Gc.length⟩ r)) m [.tau, .obs (.resolved c r)]
      .unit (m.resolve c r) := by
  show RunsQ _ _ (callerOnResolve Limits.spec Quirks.none ⟨Gc.length⟩ r) _ _ _ _
  unfold callerOnResolve
  exact RunsQ.bind (runs_getObj ArenaField.callers _ _ (callers_get_mid hc))
    (RunsQ.bind (tr₁ := [.obs (.resolved c r)]) (.emit (.pure _ _)) (.pure _ _))

/-! ## Call `k` -/

/-- The configuration `M₀` of call `k` runs the core activation of export `x` (address `a`) on
the lowered values of `vs`; when it returns flat values of the result types, after callouts that
appended subtask and caller records, the call resolves at the next configuration between calls,
or traps, as the IR lift prescribes. -/
structure CallAtKA (prof : ProfileKind) (P : Profile)
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (ι' : InstState) (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (ST₀ : List Subtask)
    (k j : Nat) (x : SimpleExport) (a : (E3 P V IR).FuncAddr) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P V IR) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P V IR) σ (Ret (E3 P V IR))) (segs : List (Seg (E3 P V IR) σ))
    (rest : List (Activation (E3 P V IR) σ)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a
    (lowerArgs x.ty.params vs)) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  funcs : M₀.store.funcs = fs
  entry : ∀ f ft opts, calloutEntry M₀.store th (.lowered f ft opts ⟨0⟩) = none
  inst : ArenaField.insts.get? M₀.store ⟨0⟩ = some ι'
  ret : ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P V IR))) (y : CoreSt (E3 P V IR))
    (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ResolvesAtA prof P g (retCfg (extSC (withH M₀ s) ST CL) th K segs rest y ys)
      (readyCfgI y.1 (InstState.removeThread 1 ι') fs
        (nextGarbA P g G x k j a (vs.map toRefVal) (ws.map toRefVal) CL) (ST₀ ++ ST) s)
  trap : ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P V IR))) (y : CoreSt (E3 P V IR))
    (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextA prof P g (retCfg (extSC (withH M₀ s) ST CL) th K segs rest y ys)

end Silmaril.Proofs.Wasm.Component.Param.Core3R
