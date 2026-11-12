module

public import Silmaril.Wasm.Det.Component.Litmus.Defs
public import Silmaril.Wasm.Det.Component.Thms
public import Silmaril.Wasm.Component.Reference.Litmus.Thms
public import Silmaril.Proofs.Wasm.Det.Component.Litmus

/-!
# Litmus components for determinism and statelessness across calls: theorems

Every statement holds at every silmaril-lean profile `P`.

* **The adder.** `adder_stateless` and `adder_det` hold for the session (the tactics
  `abi_stateless` and `abi_det`). On the reference machine (`core3P P`, every component choice
  profile), `adder_exportDet` says the export call `add` on any well-typed arguments is
  deterministic modulo traps. It uses `export_det` and `exportDet_of_coreDet`, which goes through
  `refToSpec_of_arity`.
* **The stateful component** `litX`. `one_stateless` and `one_det` hold for the export `one`,
  while `get_not_stateless` and `not_sStateless` show that the export `get`, and so the component
  as a whole, are **not** stateless: `get` returns `0`, then `5` after `set`. This is the
  per-export litmus: the export `one` is stateless and deterministic although the component is
  not stateless, because `one` reads no state.
* **The scratch buffer** `bufX`. `len_stateless` and `len_det` hold for `len(bs: list<u8>)`.
  Every call writes `bs` into linear memory at the scratch address returned by `realloc`, so the
  core store changes from call to call; the outputs do not depend on it. The proof is the
  unwinding theorem with the observable state "the function instances", the `realloc` VC (the
  scratch pointer is a leaf constant) and the core VC (the core function is a leaf).

Proofs: `Silmaril.Proofs.Wasm.Det.Component.Litmus` (`get_not_stateless`); the rest by the tactics
here. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Component.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Det.Core.Litmus (litStore)
open Silmaril.Wasm.Component.Reference (refHost toRefVal)
open Silmaril.Wasm.Component.Reference.Litmus (adderS binStore adderS_good adderS_inst adderS_arity)

/-! ## The adder -/

/-- The adder export is stateless across calls. -/
theorem adder_stateless (P : Profile) : SStatelessAt (abiSem P adderX) (binStore .add) () := by
  abi_stateless

/-- The adder export is deterministic modulo traps and imports. -/
theorem adder_det (P : Profile) : SDetAt (abiSem P adderX) (binStore .add) () := by
  abi_det

/-- The lifted core function of the reference adder `adderS` is deterministic. -/
theorem adderS_coreDet (P : Profile) :
    CoreDet P adderS ⟨"add", ⟨[.u32, .u32], [.u32]⟩, 0⟩ := by
  export_det

/-- **On the reference machine**, the export call `add` is deterministic modulo traps, at
every profile, component choice profile and well-typed argument list. -/
theorem adder_exportDet (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (vs : List Silmaril.Wasm.Component.Val)
    (hvs : Silmaril.Wasm.Component.ValTy.checkList [.u32, .u32] vs = true) :
    ExportDet prof (refHost P) () adderS.toRef [] "add" (vs.map toRefVal) :=
  exportDet_of_coreDet P prof adderS adderS_good
    (by intro x hx; simp only [adderS, List.mem_singleton] at hx; subst hx; exact ⟨rfl, rfl⟩)
    adderS_inst adderS_arity (x := ⟨"add", ⟨[.u32, .u32], [.u32]⟩, 0⟩) List.mem_cons_self
    (adderS_coreDet P) hvs

/-! ## A stateful component -/

/-- **`one` is stateless** across calls. -/
theorem one_stateless (P : Profile) : SStatelessAt (abiSem P litX) litStore .one := by
  abi_stateless

/-- **`one` is deterministic**. -/
theorem one_det (P : Profile) : SDetAt (abiSem P litX) litStore .one := by
  abi_det

/-- **`get` is not stateless**: it returns `0`, then `5` after `set`. -/
theorem get_not_stateless (P : Profile) : ¬ SStatelessAt (abiSem P litX) litStore .get :=
  Silmaril.Proofs.Wasm.Det.Component.Litmus.get_not_stateless P

/-- **The component is not stateless.** -/
theorem not_sStateless (P : Profile) : ¬ SStateless (abiSem P litX) litStore :=
  fun h => get_not_stateless P (h .get)

/-! ## A `list<u8>` export over a scratch buffer -/

/-- **`len` is stateless** across calls, although each call writes its argument into memory. -/
theorem len_stateless (P : Profile) : SStatelessAt (abiSem P bufX) bufStore () := by
  abi_stateless

/-- **`len` is deterministic**. -/
theorem len_det (P : Profile) : SDetAt (abiSem P bufX) bufStore () := by
  abi_det

end Silmaril.Wasm.Det.Component.Litmus
