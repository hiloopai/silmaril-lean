module

public import Silmaril.SSA.LambdaRTL.Defs
import Silmaril.Proofs.SSA.LambdaRTL.Agreement

/-!
# The two readings differ when a live-in is clobbered (proofs)

Variables, labels and values are `Bool`; the monad is `Id`. In

```
  (x := (); br ℓ ()) where { ℓ(y) => br exit x }      -- x = true, y = false, ℓ = false
```

the handler reads `x`, which the body overwrites before jumping. Lexically (λSSA) the handler
sees the *definition-site* `x` (initially `false`); the λRTL store reading sees the overwritten
`x` (`true`). So reading an arbitrary λRTL program as named λSSA is not semantics-preserving;
the agreement theorem needs `NoClobber`. Restated in `Silmaril.SSA.LambdaRTL.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.Counterexample

open Silmaril.SSA.LambdaRTL

/-- A model on `Bool` with no instructions; `() = true`. -/
def model : Model Empty Id Bool where
  unit := true
  pair a _ := a
  inl a := a
  inr a := a
  unpair a := (a, a)
  split a := Sum.inl a
  app f _ := nomatch f
  abort a := a

/-- `(x := (); br ℓ ()) where { ℓ(y) => br exit x }` with `x = true`, `y = false`,
`ℓ = false`, `exit = true`. -/
def clobber : Region Bool Bool Empty :=
  .join (.let1 true (.val .unit) (.br false .unit)) false false (.br true (.var true))

/-- The initial environment/store: every variable holds `false`. -/
def σ₀ : Bool → Bool := fun _ => false

theorem evalSSA_clobber : clobber.evalSSA model σ₀ = ((true, false) : Bool × Bool) := rfl

theorem evalObs_clobber : clobber.evalObs model σ₀ = ((true, true) : Bool × Bool) := rfl

theorem not_noClobber : ¬ clobber.NoClobber := by
  simp [clobber, Region.NoClobber, Region.fv, Region.bound, Val.fv]

theorem evalObs_ne_evalSSA : clobber.evalObs model σ₀ ≠ clobber.evalSSA model σ₀ := by
  rw [evalSSA_clobber, evalObs_clobber]
  exact fun h => absurd (congrArg Prod.snd h) (by decide)

end Silmaril.Proofs.SSA.LambdaRTL.Counterexample
