module

public import Silmaril.Wasm.Resource.CompTable.Defs

/-!
# The borrow discipline of `cont` handles, from the reference machine's programs: definitions

The ownership and borrowing protocol `obProto` (`Silmaril.Wasm.Resource.Handle`) rejects a
transfer or drop of a borrowed handle and ends every borrow with the call that lent it.
`Silmaril.Wasm.Component.FXRes.Example` checked those rejections on event lists by `decide`. Here
they are derived from successful runs of the **programs of the reference component machine** that
implement the Canonical ABI's handle discipline (`Silmaril.Wasm.Component.Canon`, transcribed from
REF `definitions.py`): `liftBorrow` (lending a handle to a callee: `num_lends += 1`),
`lowerBorrow` (the callee's borrowed handle: `own = false`, `num_borrows += 1`), `liftOwn`
(transferring ownership away), `resourceDropCore` (`resource.drop`) and `Task.return_` (the end
of an export call). These programs are generic in the core engine, so the results hold for the
`cont` resource type of components over the WasmFX engine with a continuation table `fxCE P`
(`Silmaril.Wasm.Component.FXRes.ContEngine`), where a `cont` handle's representation is the index
of its continuation in the engine's table.

Runs are `SRun` (`Silmaril.Wasm.Resource.CompTable`: `get` and `modify` answered as the machine's
`Step.get`/`Step.modify` do, no other operation succeeds), and for `Task.return_`, whose
`on_resolve` is a late-bound call, `StoreCallH`: the same, with every late-bound call answered
in any way.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Borrow

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-- The store-only handler with late-bound calls answered arbitrarily (any response, any
store). -/
def StoreCallH : (o : (Eff E σ).Op) → CStore E → (Eff E σ).Resp o → CStore E → Prop :=
  fun o => match (o : Op E σ) with
  | .get => fun s r s' => r = s ∧ s' = s
  | .modify f => fun s _ s' => s' = f s
  | .call _ => fun _ _ _ => True
  | _ => fun _ _ _ => False

/-- A run of a program whose late-bound calls are answered arbitrarily. -/
abbrev CRunP {α : Type} (p : P E σ α) (s : CStore E) (a : α) (s' : CStore E) : Prop :=
  Prog.Eval (S := Eff E σ) StoreCallH p s a s'

/-- The resource handle object of entry `i` of instance `j`'s table. -/
def HandleAt (s : CStore E) (j : InstId) (i : ℕ) (h : ResourceHandle) : Prop :=
  ∃ st hid, s.inst? j = some st ∧ st.handles.get? i = some (.resource hid) ∧
    ArenaField.resHandles.get? s hid = some h

end Silmaril.Wasm.Component.FXRes.Borrow
