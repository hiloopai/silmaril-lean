module

public import Silmaril.Proofs.Wasm.Component.Reference.InstImpCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.InstImpCore` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.InstImpCore` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-! ## The trampoline store -/

section Tramp

open Silmaril.Wasm.Component.Runtime

variable {P : Profile}

/-- The trampoline of import `k` (of type `p.2`). -/
noncomputable def trampFI (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (k : Nat) (p : String × FuncTy) :
    FuncInst (CanonHost (core3R P V IR)) :=
  ⟨SingleThreaded.ofFlatType (flatV1 p.2), {}, .host (.lowered ⟨k⟩ (witFt p.2) {} ⟨0⟩)⟩

/-- The core store holding the trampolines of the imports `ims`. -/
noncomputable def trampStore (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (ims : Iface) : Store (CanonHost (core3R P V IR)) :=
  { funcs := ims.mapIdx (trampFI P V IR) }

end Tramp

/-! ## The core facts of `SimpleI.Inst` -/

section Facts

open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Instantiate

variable {Pf : Profile}

/-- The core facts of a `SimpleI.Inst` component, over `core3R Pf V IR`: the instance, its store up
to `trampIdx` and with trampoline host code only, the core instantiation in the trampoline
store, its import vector, and the core exports found by name. -/
structure CoreFactsI (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (ci : (core3R Pf V IR).Inst) : Prop where
  isInst : c.mod.IsInst I
  store : Store.mapH trampIdx cs = I.store
  tramp : TrampOk c cs
  prepare : (core3R Pf V IR).prepare? (trampStore Pf V IR c.imports) c.mod.mod
    ((List.range c.imports.length).map ExternAddr.func) = some (cs, ci, none)
  imports : ∀ f : Frame (core3R Pf V IR), f.coreInstance? 0 = some (envExports c.mod.imports) →
    coreImportsFor? (trampStore Pf V IR c.imports) c.mod.mod [("env", 0)] f =
      some ((List.range c.imports.length).map ExternAddr.func)
  lookup : ∀ x ∈ c.exports, lookupExport? ((core3R Pf V IR).exports ci) (coreNameI c x) =
    some (.func (I.addrs.getD x.core 0))

end Facts

end Silmaril.Proofs.Wasm.Component.Param.Core3R
