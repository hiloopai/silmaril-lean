module

public import Silmaril.Wasm.Jco.Async.Defs

/-!
# A closed form of the async specification

`Silmaril.Wasm.Jco.Async.aspec` runs the C convention over `M.withStore`. Between the runtime's
creation of the task and the caller reading back the results, the `task.return` built-in runs
on the async store. This module states what that comes to.

The **frame lemma** (`Silmaril.Wasm.Jco.Async.Frame.Thms`, `specCall_withStore`) is that the C
convention over `M.withStore` is `RM.liftFst` of the C convention over `M`: `M`'s calls, its
allocator and its memory never touch the store. Then

* `RM.alongside m f` runs `m` on the first component. On a value `a` it updates the second
  component by `f a`, and traps when `f a` is `none`;
* `asyncStore st ws` is the store after the runtime started a fresh task in `st` and that task's
  `task.return` stored `ws`. It is a total function: the task is fresh, so `task.return` cannot
  fail on it;
* `aspecClosed md name vs` is the closed form of `aspec`. A synchronous function is
  `RM.liftFst` of the C convention. An async function is the C convention alongside the
  update `asyncStore` by the values of its result. A string or list result is outside the async
  fragment, so `resVals` is `none` and the call traps once `M` has returned.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

/-- Run `m` on the first component; on a value `a`, update the second component by `f a`
(a trap when `f a` is `none`). -/
def RM.alongside {σ τ α : Type} (m : RM σ α) (f : α → τ → Option τ) : RM (σ × τ) α :=
  fun s o =>
    match o with
    | .ok a s' => m s.1 (.ok a s'.1) ∧ f a s.2 = some s'.2
    | .trap => m s.1 .trap ∨ ∃ a s₁, m s.1 (.ok a s₁) ∧ f a s.2 = none

namespace Async

open Silmaril.Wasm.Component.Async (Store)

/-- The store after `task.return ws` of the task `t` (`none` if it fails). -/
def retStore (st : Store) (t : Nat) (ws : List Val) : Option Store :=
  (Silmaril.Wasm.Component.Async.step st (.taskReturn t ws)).map Prod.fst

/-- **The store after an async call** that returned `ws`: a fresh task is started and its
`task.return` stores `ws` (the fallback of `getD` is never taken, `retStore_fresh`). -/
def asyncStore (st : Store) (ws : List Val) : Store :=
  let p := Silmaril.Wasm.Component.Async.startSync st
  (retStore p.1 p.2 ws).getD p.1

/-- The store update of an async function returning `r`: `none` (a trap) outside the async
fragment. -/
def asyncPost (r : Option PVal) (st : Store) : Option Store := (resVals r).map (asyncStore st)

variable (M : CoreInst)

/-- **The closed form of `aspecCall`.** -/
def aspecCallClosed (md : AMeta) (s : ASig) (vs : List PVal) : RM M.withStore.St (Option PVal) :=
  match s.async with
  | none => RM.liftFst (md.sync.specCall M s.sig vs)
  | some _ => RM.alongside (md.sync.specCall M s.sig vs) asyncPost

/-- The closed form of `aspec`, by name. -/
def aspecClosed (md : AMeta) (name : String) (vs : List PVal) : RM M.withStore.St (Option PVal) :=
  match md.world.find? (·.sig.name == name) with
  | some s => aspecCallClosed M md s vs
  | none => RM.fail

end Async

end Silmaril.Wasm.Jco
