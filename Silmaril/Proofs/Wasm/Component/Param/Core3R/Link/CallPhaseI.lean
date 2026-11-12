module

public import Silmaril.Proofs.Wasm.Component.Reference.CallPhaseI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
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
# `Silmaril.Proofs.Wasm.Component.Reference.CallPhaseI` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.CallPhaseI` that the
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
  {prof : ProfileKind}
  {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ## Rounds to component import calls -/

theorem ASeg.chain {Q : LowerSite P → Prop} {B : CStore (E3 P V IR)} {th : Option ThreadId}
    {s s' : σ} {x z : CoreSt (E3 P V IR)} {calls : List (σ × CallRec × σ)}
    (h : ASeg g Q B th s x calls s' z) : Chain s calls s' := by
  induction h with
  | done => rfl
  | call _ _ _ _ _ _ _ ih => exact ⟨rfl, ih⟩

/-! ## The callouts of the core activation -/

/-- The facts about the frame of the core activation that the callouts use. -/
structure FrameOk (c : SimpleI) (B : CStore (E3 P V IR)) (th : Option ThreadId) : Prop where
  funcs : B.funcs = afterFuncs P (fun k => I.addrs.getD k 0) c
  entry : ∀ f ft opts, calloutEntry B th (.lowered f ft opts ⟨0⟩) = none
  inst : ∃ st, ArenaField.insts.get? B ⟨0⟩ = some st ∧ st.mayLeave = true

/-! ## Assembly -/

/-- The static facts of an export call of `c` from the configuration after instantiation. -/
structure CallCtxI (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (f : I.F.Op) (a : Nat) : Prop where
  start : CallStart c I cs f a (lowerArgs c.exports[j].ty.params vs)
  typed : ValTy.checkList c.exports[j].ty.params vs = true
  core : f.1.val = c.exports[j].core
  ty : I.exports.get f.1 = fnOf c.exports[j].ty.flat

theorem CallCtxI.lowered {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {f : I.F.Op} {a : Nat} (C : CallCtxI P V IR c I cs j vs f a) :
    checkLower c.exports[j].ty.params vs = some (lowerArgs c.exports[j].ty.params vs) := by
  simp only [checkLower, C.typed, ↓reduceIte]

/-! ## Stateless hosts -/

end Silmaril.Proofs.Wasm.Component.Param.Core3R
