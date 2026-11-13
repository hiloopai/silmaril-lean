module

public import Silmaril.Wasm.Component.Iface.Defs
public import Silmaril.Games.Handler.Defs
public import Silmaril.Games.Pair.Defs

/-!
# Wiring strategies over interface signatures

Combinators of `Silmaril.Games` specialised to the interface signatures:

* `splitH e`: the handler implementing `sigU` on top of `sigU ⊕ₛ sigU`:
  functions below `e` go left, the others right (shifted by `e`).
* `ext e D N`: extend an environment `D : Strategy X sigU` of `e` functions by
  an instance `N : Strategy sigU sigU` running on top of it; the new
  environment offers the old functions (by copycat) followed by those of `N`.
  This is `D.comp ((Strategy.id sigU).pair N).comp (ofHandler (splitH e))`:
  one instance `D`, shared by the forwarding copycat and by `N` (side by side,
  `Strategy.pair`).
* `selectH obs`: offer the functions `obs` (by index) of an interface.
* `widenH n : Handler (sigN n) sigU` and `narrowH n : Handler sigU (sigN n)`:
  the boundary between `sigN n` and `sigU` (out-of-range calls trap).

All answers are `Option Payload`, so these handlers are simply typed.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

/-- `sigU` on top of `sigU ⊕ₛ sigU`, splitting at `e`. -/
def splitH (e : Nat) : Handler (sigU ⊕ₛ sigU) sigU := fun q =>
  if q.1 < e then .call (.inl q) fun n => .pure n
  else .call (.inr (q.1 - e, q.2)) fun n => .pure n

/-- Extend the environment `D` (of `e` functions) by an instance `N`. -/
def ext {X : Sig.{0}} (e : Nat) (D : Strategy X sigU) (N : Strategy sigU sigU) :
    Strategy X sigU :=
  D.comp (((Strategy.id sigU).pair N).comp (Strategy.ofHandler (splitH e)))

/-- Offer the functions `obs` (in that order); an index out of range traps. -/
def selectH (obs : List Nat) : Handler sigU sigU := fun q =>
  match obs[q.1]? with
  | some j => .call (j, q.2) fun n => .pure n
  | none => .pure none

/-- `sigU` on top of an interface of `n` functions; out-of-range calls trap. -/
def widenH (n : Nat) : Handler (sigN n) sigU := fun q =>
  if h : q.1 < n then .call (⟨q.1, h⟩, q.2) fun r => .pure r else .pure none

/-- An interface of `n` functions on top of `sigU`. -/
def narrowH (n : Nat) : Handler sigU (sigN n) := fun q =>
  .call (q.1.val, q.2) fun r => .pure r

/-- A strategy over `sigU` seen at the interface sizes `n` (imports) and `k`
(exports). -/
def atSizes (n k : Nat) (σ : Strategy sigU sigU) : Strategy (sigN n) (sigN k) :=
  ((Strategy.ofHandler (widenH n)).comp σ).comp (Strategy.ofHandler (narrowH k))

end Silmaril.Wasm.Component
