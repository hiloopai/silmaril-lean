module

public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Component.Reference.LinkSound.Defs

/-!
# Hosts and component functions over `core3R P V IR`

Provenance: copies of the `core3P`-specific definitions of
`Silmaril.Wasm.Component.Reference.Sound.Defs` (`answerHostS`, `SimpleI.afterFuncs`,
`SimpleI.TrampOk`) and `Silmaril.Wasm.Component.Reference.LinkSound.Defs` (`linkHost`), with
`core3P P` replaced by `core3R P V IR`. The `SimpleI` definitions are copied as
`afterFuncs` and `TrampOk` in this namespace (dot notation on `SimpleI` would find the
originals). Over `core3R P V IR`, `linkHost` is `Param.linkHostE`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Numerics (Profile)

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}
  {σ : Type}

/-- The reference host answering the imports by the stateful `g` (`Reference.answerHostS`). -/
def answerHostS (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) :
    Host (core3R P V IR) σ :=
  { hr := fun _ _ => false, impl := answerImplS g }

/-- A reference host without ready host waitables and with the host functions `impl`
(`Reference.linkHost`). -/
def linkHost {P : Profile} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3R P V IR) σ) :
    Host (core3R P V IR) σ :=
  { hr := fun _ _ => false, impl := impl }

theorem linkHost_eq {P : Profile}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3R P V IR) σ) :
    linkHost impl = Silmaril.Wasm.Component.Param.linkHostE impl := rfl

/-- The component functions after instantiating `c.toRef` (`Reference.SimpleI.afterFuncs`). -/
def afterFuncs (P : Profile) (addr : Nat → Nat) (c : SimpleI) :
    List (CFuncInst (core3R P V IR)) :=
  c.imports.mapIdx (fun k p => .host (witFt p.2) ⟨k⟩) ++
    c.exports.map fun x => .lifted (addr x.core) (witFt x.ty) {} ⟨0⟩

/-- The host functions of `cs` are the `canon lower` trampolines of the imports of `c`
(`Reference.SimpleI.TrampOk`). -/
def TrampOk {P : Profile} (c : SimpleI) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) :
    Prop :=
  ∀ (a : Nat) (fi : Silmaril.Wasm.Execution.Core.FuncInst (CanonHost (core3R P V IR)))
    (h : CanonHost (core3R P V IR)),
    (cs : Silmaril.Wasm.Execution.Core.Store (CanonHost (core3R P V IR))).funcs[a]? = some fi →
    fi.code = .host h → ∃ (k : Nat) (hk : k < c.imports.length),
      h = .lowered ⟨k⟩ (witFt c.imports[k].2) {} ⟨0⟩

end Silmaril.Proofs.Wasm.Component.Param.Core3R
