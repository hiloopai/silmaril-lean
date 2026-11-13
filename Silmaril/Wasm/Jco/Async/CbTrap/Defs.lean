module

public import Silmaril.Wasm.Jco.Async.CbRet.Defs

/-!
# A callback that goes on after its `task.return`

`Silmaril.Wasm.Jco.Async.EarlyDrive` (`Async/CbRet`) runs each call of the callback atomically: the
loop stops at `task.return` only between two calls. A callback that calls `task.return` and then
traps traps the caller there, whereas in the Component Model (`definitions.py` at `a25fc0b`,
`canon_task_return`) the caller has already continued with the values when the trap happens.

This module splits a callback call at its `task.return`:

* `CbStep`: what one call of the callback does up to its `task.return`: it returns a callback code
  without calling `task.return` (`code rs`), or it reaches `task.return ys` (`ret ys`).
* `NCbSplit M L`: `pre` (the core function's epilogue, the first code and local data `l`), the
  callback `cb t l` up to `task.return`, and `post t l`, the rest of a callback call after its
  `task.return` (returning the next code).
* `NCbSplit.atomic`: the same body as a `CbSplit` of `Async/CbRet`, each callback call running
  `cb`, `task.return` and `post` at once. `NCbSplit.cut`: the callback cut at `task.return`
  (the code after it is `EXIT`; the loop up to `task.return` never runs it).
* `asyncCallN`: **the caller's view**: `asyncCallC` of the cut body. The caller continues as soon
  as the callback reached `task.return`; `post` belongs to the callee.
* `NRest b t l s s'`: the callee after the caller continued: `post t l`, then the callback loop
  (`Finish`, other parties interleaved) with the atomic callback.
* `retTrap`: **a callback that traps after `task.return`**: the body yields, the callback calls
  `task.return` of the values and then traps.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

namespace Async

/-- One call of a callback up to its `task.return`. -/
inductive CbStep where
  /-- The call returned the callback code `rs` without calling `task.return`. -/
  | code (rs : List Flat)
  /-- The call reached `task.return ys`. -/
  | ret (ys : List Val)

variable (M : CoreInst)

/-- **A body whose callback calls are split at their `task.return`.** -/
structure NCbSplit (L : Type) where
  pre : Nat → List Val → RM M.withStore.St (List Flat × L)
  cb : Nat → L → List Flat → RM M.withStore.St CbStep
  post : Nat → L → RM M.withStore.St (List Flat)

namespace NCbSplit

variable {M} {L : Type} (b : NCbSplit M L)

/-- The body with atomic callback calls: `cb`, then `task.return` and `post`. -/
def atomic : CbSplit M L where
  pre := b.pre
  cb t l a := do
    let r ← b.cb t l a
    match r with
    | .code rs => pure rs
    | .ret ys => do
      let _ ← builtin M (.taskReturn t ys)
      b.post t l

/-- The body with each callback call cut at its `task.return`. -/
def cut : CbSplit M L where
  pre := b.pre
  cb t l a := do
    let r ← b.cb t l a
    match r with
    | .code rs => pure rs
    | .ret ys => do
      let _ ← builtin M (.taskReturn t ys)
      pure [i32n cbExit]

end NCbSplit

/-- **The caller's view**: it continues as soon as a callback call reached `task.return`. -/
def asyncCallN {L : Type} (R core : List Flat → RM M.withStore.St (List Flat)) (b : NCbSplit M L)
    (sig : Sig) (vs : List PVal) : RM M.withStore.St (Option PVal) :=
  asyncCallC M R core b.cut sig vs

/-- **The callee after the caller continued** in a callback call: the rest of that call, then the
callback loop with other parties interleaved. -/
def NRest {L : Type} (b : NCbSplit M L) (t : Nat) (l : L) (s s' : M.withStore.St) : Prop :=
  ∃ rs s₁, b.post t l s (.ok rs s₁) ∧ Finish M (b.atomic.cb t l) rs s₁ s'

/-- **A callback that traps after `task.return`**: the body yields, keeping the values; the
callback calls `task.return` of them, then traps. -/
def retTrap : NCbSplit M (List Val) where
  pre _ ws := pure ([i32n cbYield], ws)
  cb _ ws _ := pure (.ret ws)
  post _ _ := RM.fail

end Async

end Silmaril.Wasm.Jco
