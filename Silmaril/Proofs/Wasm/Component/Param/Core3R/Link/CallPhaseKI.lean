module

public import Silmaril.Proofs.Wasm.Component.Reference.CallPhaseKI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallKI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallPhaseI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.FloatPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqCall
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Seq
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Sound
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.CallPhaseKI` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.CallPhaseKI` that the
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

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Val → Option (List Val × σ)}
  {prof : ProfileKind} {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ## Configurations between calls -/

/-- **The invariant between calls with imports.** -/
structure ReadyAtI (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState) (G : Garb P V IR σ) (k : Nat) :
    Prop where
  wf : I.WellFormed (Store.mapH trampIdx cs)
  tramp : TrampOk c cs
  threads : ThreadsOk ι
  leave : ι.mayLeave = true
  fresh : G.Fresh k

/-! ## Plays at a later store -/

/-- The static facts of call `k` of export `j` with imports at the core store `cs`. -/
structure CallCtxKI (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (f : I.F.Op) (a : Nat) : Prop where
  start : CallStartAt c I (Store.mapH trampIdx cs) cs f a (lowerArgs c.exports[j].ty.params vs)
  typed : ValTy.checkList c.exports[j].ty.params vs = true
  core : f.1.val = c.exports[j].core
  ty : I.exports.get f.1 = fnOf c.exports[j].ty.flat

theorem CallCtxKI.lowered {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))}
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} {f : I.F.Op} {a : Nat}
    (C : CallCtxKI P V IR c I cs j vs f a) :
    checkLower c.exports[j].ty.params vs = some (lowerArgs c.exports[j].ty.params vs) := by
  simp only [checkLower, C.typed, ↓reduceIte]

/-! ## Call `k` -/

variable {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))} {ι : InstState}
  {fs : List (CFuncInst (core3R P V IR))} {G : Garb P V IR σ} {ST₀ : List Subtask} {k : Nat}
  {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} {f : I.F.Op}

end Silmaril.Proofs.Wasm.Component.Param.Core3R
