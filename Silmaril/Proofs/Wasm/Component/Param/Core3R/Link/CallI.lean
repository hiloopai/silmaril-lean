module

public import Silmaril.Proofs.Wasm.Component.Reference.CallI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.CallI` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.CallI` that the
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

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)} {prof : ProfileKind}

/-- From `mS`, the call resolves with `rs` under `answerHostS P V IR g` (a stateful host; `answerHost P g` is its stateless instance). -/
def ResolvesA (prof : ProfileKind) (P : Profile) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (mS : Machine.Config (E3 P V IR) σ) (rs : List Silmaril.Wasm.Component.Reference.Val) : Prop :=
  ∃ tr mE, LRun prof (answerHostS P V IR g).hr (DA P g) mS tr mE ∧ mE.ctl = [] ∧
    mE.store.lockdown = false ∧ mE.result? ⟨0⟩ = some (some rs) ∧
    ∀ m₁, Step prof (answerHostS P V IR g).hr (DA P g) mE (.host .tick) m₁ →
      ∃ trT, LRun prof (answerHostS P V IR g).hr (DA P g) m₁ trT mE

/-- From `mS`, the call traps after one live step under `answerHostS P V IR g` (a stateful host; `answerHost P g` is its stateless instance). -/
def TrapsNextA (prof : ProfileKind) (P : Profile) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (mS : Machine.Config (E3 P V IR) σ) : Prop :=
  ∃ mT r, LRun prof (answerHostS P V IR g).hr (DA P g) mS [.tau] mT ∧ Live mT ∧
    UniqueStep prof (answerHostS P V IR g).hr (DA P g) mT (.trap r) (trapCfg mT)

/-- The configuration `M₀` runs the core activation of export `x` (address `a`) on the
lowered values of `vs`; whenever it returns flat values of the result types, after callouts
that appended subtask and caller records, the call resolves or traps as the IR lift
prescribes. -/
structure CallAtA (prof : ProfileKind) (P : Profile) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (fs : List (CFuncInst (core3R P V IR)))
    (x : SimpleExport) (a : Nat)
    (vs : List Silmaril.Wasm.Component.Val) (M₀ : Machine.Config (E3 P V IR) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P V IR) σ (Ret (E3 P V IR))) (segs : List (Seg (E3 P V IR) σ))
    (rest : List (Activation (E3 P V IR) σ)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a
    (lowerArgs x.ty.params vs)) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  funcs : M₀.store.funcs = fs
  entry : ∀ f ft opts, calloutEntry M₀.store th (.lowered f ft opts ⟨0⟩) = none
  inst : ∃ st, ArenaField.insts.get? M₀.store ⟨0⟩ = some st ∧ st.mayLeave = true
  ret : ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P V IR))) (y : CoreSt (E3 P V IR))
    (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ResolvesA prof P g (retCfg (extSC (withH M₀ s) ST CL) th K segs rest y ys) (ws.map toRefVal)
  trap : ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P V IR))) (y : CoreSt (E3 P V IR))
    (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextA prof P g (retCfg (extSC (withH M₀ s) ST CL) th K segs rest y ys)

end Silmaril.Proofs.Wasm.Component.Param.Core3R
