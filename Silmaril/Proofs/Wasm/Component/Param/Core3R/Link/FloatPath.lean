module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.FloatPath` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.FloatPath` that the
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

variable {P : Profile}

/-- `CallAt` on the flat arguments `xs`, with canonicalised results. -/
structure CallAtF (prof : ProfileKind) (P : Profile)
    (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (x : SimpleExport) (a : Nat) (xs : List Flat)
    (M₀ : Machine.Config (E3 P V IR) Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P V IR) Unit (Ret (E3 P V IR))) (segs : List (Seg (E3 P V IR) Unit))
    (rest : List (Activation (E3 P V IR) Unit)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  ret : ∀ (y : CoreSt (E3 P V IR)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    Resolves prof P (retCfg M₀ th K segs rest y ys)
      ((canonAtList x.ty.results ws).map toRefVal)
  trap : ∀ (y : CoreSt (E3 P V IR)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNext prof P (retCfg M₀ th K segs rest y ys)

end Silmaril.Proofs.Wasm.Component.Param.Core3R
