module

public import Silmaril.Wasm.Interp.Example.Defs
public import Silmaril.Wasm.Interp.Thms
public import Silmaril.Proofs.Wasm.Interp.Example

/-!
# A closed module for native adequacy: theorems

Non-vacuity of `Silmaril.Wasm.Interp.native_adequacy` on `exMod`, a validated module whose only
function uses `select` and `br_table` inside a block:

* `ex_instantiate`: silmaril-lean's executable instantiation `prepare?` of `exMod` into the empty
  store is its Core 3.0 instantiation `Instantiate`, at every profile and host (no imports,
  segments or start function), with store `exStore`;
* `ex_storeOk`, `ex_nativeFuncsOk`, `ex_storeChk`, `ex_invokeOk`: every hypothesis of
  `native_adequacy` holds — typing from `Instantiate.ok`, the native profile and the arity
  check by kernel evaluation of `nativeFuncsB` and `storeChkB`;
* `ex_adequacy`: `native_adequacy` instantiated on export `0` with two `i32` arguments;
* `ex_behaviours_07`, `ex_behaviours_37`: the Core 3.0 behaviours of two invocations at
  **every** profile, computed by kernel evaluation of the native interpreter: `f(0, 7)`
  returns `7` and `f(3, 7)` returns `3`, and nothing else (no trap, no divergence).

Proofs: `Silmaril.Proofs.Wasm.Interp.Example`. New.
-/

public section

namespace Silmaril.Wasm.Interp.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

/-- **`exMod` instantiates to the allocation `exPrep.1`**, every profile and host. -/
theorem ex_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) exMod [] exPrep.1 :=
  Silmaril.Proofs.Wasm.Interp.Example.ex_instantiate P host

/-- The body of function `0` uses `select` and `br_table`. -/
theorem exMod_body : exMod.funcs.map (·.body) = [[.block (.value i32)
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .localGet ⟨0⟩, .select none, .localGet ⟨1⟩,
      .brTable [⟨0⟩] ⟨0⟩]]] := rfl

theorem ex_storeOk : StoreOk exStore := Silmaril.Proofs.Wasm.Interp.Example.exStore_ok

theorem ex_nativeFuncsOk : Binaryen.NativeFuncsOk exStore.funcs :=
  nativeFuncsOk_of_nativeFuncsB Silmaril.Proofs.Wasm.Interp.Example.exStore_native

theorem ex_storeChk : StoreChk exStore.funcs :=
  storeChk_of_storeChkB Silmaril.Proofs.Wasm.Interp.Example.exStore_chk

theorem ex_invokeOk (x y : BitVec 32) : InvokeOk exStore 0 [Val.i32 x, Val.i32 y] :=
  Silmaril.Proofs.Wasm.Interp.Example.ex_invokeOk x y

/-- **`native_adequacy` on `exMod`**: the Core behaviours of `f(x, y)` at every profile are the
native interpreter's. -/
theorem ex_adequacy (P : Numerics.Profile) (x y : BitVec 32) :
    behaviours P Binaryen.closedHost exStore 0 [Val.i32 x, Val.i32 y] =
      Binaryen.nbeh exStore 0 [Val.i32 x, Val.i32 y] :=
  native_adequacy ex_storeOk ex_nativeFuncsOk ex_storeChk (ex_invokeOk x y)

/-- **`f(0, 7)` returns `7`, and does nothing else**, at every profile. -/
theorem ex_behaviours_07 (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost exStore 0 [Val.i32 0, Val.i32 7] = {.returns [Val.i32 7]} := by
  rw [ex_adequacy]
  exact Silmaril.Proofs.Wasm.Interp.Example.nbeh_eq_singleton
    Silmaril.Proofs.Wasm.Interp.Example.exRun_07

/-- **`f(3, 7)` returns `3`, and does nothing else**, at every profile. -/
theorem ex_behaviours_37 (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost exStore 0 [Val.i32 3, Val.i32 7] = {.returns [Val.i32 3]} := by
  rw [ex_adequacy]
  exact Silmaril.Proofs.Wasm.Interp.Example.nbeh_eq_singleton
    Silmaril.Proofs.Wasm.Interp.Example.exRun_37

end Silmaril.Wasm.Interp.Example
