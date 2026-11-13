module

public import Silmaril.Wasm.Det.Component.Litmus.Defs
public import Silmaril.Wasm.Det.Component.Thms
public import Silmaril.Wasm.Det.Core.Litmus.Thms

/-!
# Litmus components: proofs

`get_not_stateless`: in the session of `litX`, `get` returns `0` from the initial state and `5`
after a call of `set`. The canonical-ABI calls are built from the Core runs `set_run` and
`get_run` of `Silmaril.Proofs.Wasm.Det.Core.Litmus`, which are reached through the public imports of
the header `Silmaril.Wasm.Det.Core.Litmus.Thms`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Component.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Component Silmaril.Wasm.Det.Component.Litmus
open Silmaril.Wasm.Det.Core.Litmus (litStore)

/-- `set` from the initial state returns, writing the global. -/
theorem set_call (P : Profile) :
    AbiCall P (litX .set) litStore (.flat []) [] (litStore.setGlobal 1 (Val.i32 5))
      (some (.flat [])) :=
  AbiCall.ret (ws := []) (ok := true) (Lower.flat (xs := []) rfl)
    (.stop (Silmaril.Proofs.Wasm.Det.Core.Litmus.set_run P)) rfl (PostRet.none rfl)

/-- `get` returns `0` from the initial state. -/
theorem get_call₀ (P : Profile) :
    AbiCall P (litX .get) litStore (.flat []) [] litStore (some (.flat [0])) :=
  AbiCall.ret (ws := [Val.i32 0]) (ok := true) (Lower.flat (xs := []) rfl)
    (.stop (Silmaril.Proofs.Wasm.Det.Core.Litmus.get_run P).1) rfl (PostRet.none rfl)

/-- `get` returns `5` after `set`. -/
theorem get_call₁ (P : Profile) :
    AbiCall P (litX .get) (litStore.setGlobal 1 (Val.i32 5)) (.flat []) []
      (litStore.setGlobal 1 (Val.i32 5)) (some (.flat [5])) :=
  AbiCall.ret (ws := [Val.i32 5]) (ok := true) (Lower.flat (xs := []) rfl)
    (.stop (Silmaril.Proofs.Wasm.Det.Core.Litmus.get_run P).2) rfl (PostRet.none rfl)

/-- **`get` is not stateless**, at every profile. -/
theorem get_not_stateless (P : Profile) : ¬ SStatelessAt (abiSem P litX) litStore .get := by
  intro hS
  have hr : SReach (abiSem P litX) litStore (litStore.setGlobal 1 (Val.i32 5)) :=
    SReach.call (i := .set) .init (set_call P)
  have h : AVal.flat [0] = AVal.flat [5] :=
    hS litStore _ .init hr (.flat []) [] _ _ _ _ (get_call₀ P) (get_call₁ P)
  exact absurd h (by decide)

end Silmaril.Proofs.Wasm.Det.Component.Litmus
