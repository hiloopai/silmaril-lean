module

public import Silmaril.Wasm.Component.Param.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.Instance.Defs
import Silmaril.Proofs.Wasm.Component.Core3G.Lawful

/-!
# The Core 3.0 engine at every profile as a game engine

* `core3P_lawful P : (core3P P).Lawful`: **the Core 3.0 engine at an arbitrary profile `P`
  satisfies the engine laws** of `CoreEngine.Lawful` (`docs/projects/spectec/README.md` §3.3, item
  `(core3P P).Lawful`). The laws that mention neither the internal step nor the status are those
  of `core3` (`core3_lawful`); the others are proved for every profile in
  `Silmaril.Proofs.Wasm.Component.Core3G.Lawful`: internal steps grow the store (`Step.grows`
  holds at every profile), callout statuses of `statusP P` persist under growth, parked
  threads take no internal step, and an allocated host function is a callout;
* `core3G P : GameEngine`: **the Core 3.0 game engine** at profile `P`, running the IR's numeric
  modules `NumModule` through `NumModule.mod`, with the ABI law from the engine laws.

Its game semantics is `(core3G P).sem = engineSem (core3P P) NumModule NumModule.mod`. The
bridge to the existing `modSem P` (instance strategies of `Silmaril.Wasm.Game` between the flat
boundary handlers) is proved in `Silmaril.Wasm.Component.Core3G.Thms` (`engineSem_eq_modSem`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Param

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Core3G
open Silmaril.Wasm.Component.Engine.Core3 (prepareE?_grows allocHost_grows memWrite?_grows)
open Silmaril.Wasm.Numerics (Profile)

/-- The laws of `core3` (with the unused grow oracle `neverFail`). -/
abbrev L₀ : (Silmaril.Wasm.Component.Engine.core3 Silmaril.Wasm.SingleThreaded.neverFail).Lawful :=
  Silmaril.Wasm.Component.Engine.core3_lawful _

/-- **The Core 3.0 engine at every profile is lawful.** -/
instance core3P_lawful (P : Profile) : (core3P P).Lawful where
  flatType?_ofFlatType := (L₀).flatType?_ofFlatType
  returned_no_step h := flat_no_step (Or.inr (Or.inl ⟨_, h⟩))
  callout_no_step h := flat_no_step (Or.inr (Or.inr ⟨_, _, h⟩))
  stuck_no_step h := flat_no_step (Or.inl h)
  externSub_refl := (L₀).externSub_refl
  externSub_trans := (L₀).externSub_trans
  asFunc?_ofFunc _ := rfl
  internal_extends h := Grows.extendsP (internalP_grows h)
  prepare_extends h := Grows.extendsP (prepareE?_grows h)
  allocHost_extends h := Grows.extendsP (allocHost_grows h)
  allocHost_fresh := (L₀).allocHost_fresh
  allocHost_frame := (L₀).allocHost_frame
  allocHost_funcType := (L₀).allocHost_funcType
  allocHost_callout := statusP_allocHost_callout
  memWrite_extends h := Grows.extendsP (memWrite?_grows h)
  memWrite_memSize := (L₀).memWrite_memSize
  memWrite_memAddrType := (L₀).memWrite_memAddrType
  memWrite_read := (L₀).memWrite_read
  memWrite_read_other := (L₀).memWrite_read_other
  memRead_isSome_iff := (L₀).memRead_isSome_iff
  memRead_size := (L₀).memRead_size
  memWrite_isSome_iff := (L₀).memWrite_isSome_iff
  memAddrType_isSome_iff := (L₀).memAddrType_isSome_iff

/-- **The Core 3.0 game engine** at profile `P`: the IR's numeric modules run on `core3P P`. -/
noncomputable def core3G (P : Profile) : GameEngine where
  E := core3P P
  lawful := core3P_lawful P
  abi := AbiLawful.ofLawful _
  M := NumModule
  core := inferInstance
  emb := NumModule.mod

theorem core3G_sem (P : Profile) :
    (core3G P).sem = engineSem (core3P P) NumModule NumModule.mod :=
  rfl

end Silmaril.Wasm.Component.Param
