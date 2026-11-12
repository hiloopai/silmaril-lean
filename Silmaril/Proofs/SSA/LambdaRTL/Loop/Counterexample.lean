module

public import Silmaril.SSA.LambdaRTL.Loop.Defs
public import Silmaril.Semantics.Elgot.Thms

/-!
# A loop handler that clobbers its own live-in (proofs)

Variables, labels and values are `Bool`; the monad is `Part` (a lawful Elgot monad). With
`c = true`, the parameter `y = false`, `ℓ = false`, `exit = true`, `() = true`, and sums on
`Bool` read as `true ↦ inl`, `false ↦ inr`:

```
  br ℓ c  where rec { ℓ(y) => case y of
                                 inl y => br exit c
                                 inr y => c := (); br ℓ () }
```

The body `r` assigns nothing, so the acyclic (join-style) side condition
`Disjoint (t.fv.erase y) r.bound` holds; only the handler itself clobbers its live-in `c`.
Starting from the all-`false` store, both readings take two iterations, but the second
iteration of the lexical reading sees the definition-site `c = false` while the λRTL reading sees
the overwritten `c = true`. Hence the loop clause of `Loop.Region.NoClobber` (no handler
live-in assigned in `t`) cannot be dropped. Restated in `Silmaril.SSA.LambdaRTL.Loop.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.Loop.Counterexample

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.Loop Silmaril.Elgot

/-- A model on `Bool` in `Part` with no instructions; `() = true`, `true` is a left injection. -/
def model : Model Empty Part Bool where
  unit := true
  pair a _ := a
  inl a := a
  inr a := a
  unpair a := pure (a, a)
  split a := pure (if a then Sum.inl a else Sum.inr a)
  app f _ := nomatch f
  abort a := pure a

/-- The loop handler: exit with `c` on `inl`, otherwise assign `c := ()` and loop. -/
def handler : Loop.Region Bool Bool Empty :=
  .case (.val (.var false)) false (.br true (.var true)) false
    (.let1 true (.val .unit) (.br false .unit))

/-- `br ℓ c where rec { ℓ(y) => handler }`. -/
def selfClobber : Loop.Region Bool Bool Empty :=
  .loop (.br false (.var true)) false false handler

/-- The initial environment/store: every variable holds `false`. -/
def σ₀ : Bool → Bool := fun _ => false

theorem iter_unfold {A B : Type} (f : A → Part (B ⊕ A)) (a : A) :
    iter f a = f a >>= Sum.elim pure (iter f) :=
  congrFun (LawfulElgotMonad.fixpoint f) a

theorem evalSSA_selfClobber :
    selfClobber.evalSSA model σ₀ = pure ((true, false) : Bool × Bool) := by
  simp only [selfClobber, Loop.Region.evalSSA, Val.eval, pure_bind, σ₀, ↓reduceIte]
  rw [iter_unfold]
  simp [handler, Loop.Region.evalSSA, Op.eval, Val.eval, model, upd, routeSSA, σ₀]
  rw [iter_unfold]
  simp [routeSSA]

theorem evalObs_selfClobber :
    selfClobber.evalObs model σ₀ = pure ((true, true) : Bool × Bool) := by
  simp only [selfClobber, Loop.Region.evalObs, Loop.Region.evalRTL, Val.eval, pure_bind, σ₀,
    ↓reduceIte]
  rw [iter_unfold]
  simp [handler, Loop.Region.evalRTL, Op.eval, Val.eval, model, upd, routeRTL, σ₀]
  rw [iter_unfold]
  simp [upd, routeRTL, obs]

theorem not_noClobber : ¬ selfClobber.NoClobber := by
  simp [selfClobber, handler, Loop.Region.NoClobber, Loop.Region.fv, Loop.Region.bound,
    Val.fv, Op.fv]

/-- The join-style condition (body `r` does not clobber) holds: only the loop clause fails. -/
theorem joinCondition : Disjoint (handler.fv.erase false) (Loop.Region.br false (.var true) :
    Loop.Region Bool Bool Empty).bound := by
  simp [Loop.Region.bound]

theorem evalObs_ne_evalSSA : selfClobber.evalObs model σ₀ ≠ selfClobber.evalSSA model σ₀ := by
  rw [evalSSA_selfClobber, evalObs_selfClobber]
  intro h
  have := Part.some_injective h
  exact absurd (congrArg Prod.snd this) (by decide)

end Silmaril.Proofs.SSA.LambdaRTL.Loop.Counterexample
