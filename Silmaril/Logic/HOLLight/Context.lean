module

public import Silmaril.Logic.HOLLight.Typing
public import Cslib.Foundations.Syntax.Context

@[expose] public section

/-!
# Single-hole HOL term contexts

These contexts instantiate CSLib's syntax-context interface, not its separate
association-list notion of typing environments. Filling is raw syntactic
plugging. A hole below binders expects a term in those binders' scope; filling
does not silently weaken its argument. `scope_fill` gives the exact depth
contract, and `Context.HasType` records both the outer and hole typing contexts.
-/

namespace Silmaril.Logic.HOLLight
namespace Tm

inductive Context where
  | hole
  | appLeft (context : Context) (argument : Tm)
  | appRight (function : Tm) (context : Context)
  | lam (domain : Ty) (context : Context)
  deriving DecidableEq, Repr

namespace Context

def fill : Context → Tm → Tm
  | .hole, t => t
  | .appLeft c x, t => .app (c.fill t) x
  | .appRight f c, t => .app f (c.fill t)
  | .lam A c, t => .lam A (c.fill t)

/-- Replace the unique hole of `outer` by `inner`. -/
def compose : Context → Context → Context
  | .hole, inner => inner
  | .appLeft c x, inner => .appLeft (c.compose inner) x
  | .appRight f c, inner => .appRight f (c.compose inner)
  | .lam A c, inner => .lam A (c.compose inner)

/-- The number of binders between the root and the unique hole. -/
def depth : Context → Nat
  | .hole => 0
  | .appLeft c _ | .appRight _ c => c.depth
  | .lam _ c => c.depth + 1

/-- The bound-type environment at the hole, including every enclosing binder. -/
def holeContext (Γ : List Ty) : Context → List Ty
  | .hole => Γ
  | .appLeft c _ | .appRight _ c => c.holeContext Γ
  | .lam A c => c.holeContext (A :: Γ)

/-- All fixed subterms fit their surrounding scopes. The hole is unconstrained. -/
def Scope (d : Nat) : Context → Prop
  | .hole => True
  | .appLeft c x => c.Scope d ∧ x.Scope d
  | .appRight f c => f.Scope d ∧ c.Scope d
  | .lam _ c => c.Scope (d + 1)

@[simp] theorem fill_hole (t : Tm) : Context.hole.fill t = t := rfl

@[simp] theorem fill_compose (outer inner : Context) (t : Tm) :
    (outer.compose inner).fill t = outer.fill (inner.fill t) := by
  induction outer with
  | hole => rfl
  | appLeft c x ih => exact congrArg (fun f => Tm.app f x) ih
  | appRight f c ih => exact congrArg (Tm.app f) ih
  | lam A c ih => exact congrArg (Tm.lam A) ih

@[simp] theorem compose_hole (c : Context) : c.compose .hole = c := by
  induction c <;> simp_all [compose]

theorem compose_assoc (a b c : Context) : (a.compose b).compose c = a.compose (b.compose c) := by
  induction a <;> simp_all [compose]

@[simp] theorem depth_compose (outer inner : Context) :
    (outer.compose inner).depth = outer.depth + inner.depth := by
  induction outer <;> simp_all [compose, depth, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem holeContext_length (c : Context) (Γ : List Ty) :
    (c.holeContext Γ).length = Γ.length + c.depth := by
  induction c generalizing Γ with
  | hole => simp [holeContext, depth]
  | appLeft c x ih | appRight x c ih => exact ih Γ
  | lam A c ih => simp [holeContext, ih, depth, Nat.add_assoc, Nat.add_comm]

/-- Raw plugging is well scoped exactly when the fixed context is well scoped
and its argument fits the depth of the hole. -/
theorem scope_fill (c : Context) (t : Tm) (d : Nat) :
    (c.fill t).Scope d ↔ c.Scope d ∧ t.Scope (d + c.depth) := by
  induction c generalizing d with
  | hole => simp [fill, Scope, depth]
  | appLeft c x ih | appRight x c ih =>
    simp [fill, Tm.Scope, Scope, depth, ih, and_assoc, and_comm]
  | lam A c ih =>
    simp [fill, Tm.Scope, Scope, depth, ih, Nat.add_assoc, Nat.add_comm]

/-- A context takes a term of type `A` under `Δ` and produces a term of type `B`
under `Γ`. The different environments are essential when its hole lies under lambdas. -/
inductive HasType (sig : Signature) : List Ty → List Ty → Ty → Ty → Context → Prop where
  | hole {Γ : List Ty} {A : Ty} : HasType sig Γ Γ A A .hole
  | appLeft {Γ Δ : List Ty} {A B C : Ty} {c : Context} {x : Tm} :
      HasType sig Γ Δ A (.arr C B) c → Silmaril.Logic.HOLLight.HasType sig Γ x C →
      HasType sig Γ Δ A B (.appLeft c x)
  | appRight {Γ Δ : List Ty} {A B C : Ty} {c : Context} {f : Tm} :
      Silmaril.Logic.HOLLight.HasType sig Γ f (.arr C B) → HasType sig Γ Δ A C c →
      HasType sig Γ Δ A B (.appRight f c)
  | lam {Γ Δ : List Ty} {A B C : Ty} {c : Context} (hC : C.WellFormed sig.tyOps) :
      HasType sig (C :: Γ) Δ A B c → HasType sig Γ Δ A (.arr C B) (.lam C c)

theorem HasType.fill {sig : Signature} {Γ Δ : List Ty} {A B : Ty} {c : Context}
    (context : c.HasType sig Γ Δ A B) {t : Tm}
    (term : Silmaril.Logic.HOLLight.HasType sig Δ t A) :
    Silmaril.Logic.HOLLight.HasType sig Γ (c.fill t) B := by
  induction context with
  | hole => exact term
  | appLeft _ hx ih => exact .app (ih term) hx
  | appRight hf _ ih => exact .app hf (ih term)
  | lam hC _ ih => exact .lam hC (ih term)

theorem HasType.compose {sig : Signature} {Γ Δ Ξ : List Ty} {A B C : Ty}
    {outer inner : Context} (ho : outer.HasType sig Γ Δ B C)
    (hi : inner.HasType sig Δ Ξ A B) : (outer.compose inner).HasType sig Γ Ξ A C := by
  induction ho with
  | hole => exact hi
  | appLeft _ hx ih => exact .appLeft (ih hi) hx
  | appRight hf _ ih => exact .appRight hf (ih hi)
  | lam hC _ ih => exact .lam hC (ih hi)

theorem HasType.holeContext {sig : Signature} {Γ Δ : List Ty} {A B : Ty} {c : Context}
    (context : c.HasType sig Γ Δ A B) : Δ = c.holeContext Γ := by
  induction context with
  | hole => rfl
  | appLeft _ _ ih | appRight _ _ ih | lam _ _ ih => exact ih

/-- Type instantiation preserves the syntactic location of the hole. -/
def tySubst (σ : Nat → Ty) : Context → Context
  | .hole => .hole
  | .appLeft c x => .appLeft (c.tySubst σ) (x.tySubst σ)
  | .appRight f c => .appRight (f.tySubst σ) (c.tySubst σ)
  | .lam A c => .lam (A.subst σ) (c.tySubst σ)

theorem tySubst_fill (σ : Nat → Ty) (c : Context) (t : Tm) :
    (c.fill t).tySubst σ = (c.tySubst σ).fill (t.tySubst σ) := by
  induction c <;> simp_all [fill, tySubst, Tm.tySubst]

@[simp] theorem depth_tySubst (σ : Nat → Ty) (c : Context) : (c.tySubst σ).depth = c.depth := by
  induction c <;> simp_all [tySubst, depth]

theorem tySubst_compose (σ : Nat → Ty) (outer inner : Context) :
    (outer.compose inner).tySubst σ = (outer.tySubst σ).compose (inner.tySubst σ) := by
  induction outer <;> simp_all [tySubst, compose]

theorem HasType.tySubst {sig : Signature} {Γ Δ : List Ty} {A B : Ty} {c : Context}
    (context : c.HasType sig Γ Δ A B) (σ : Nat → Ty)
    (hσ : ∀ i, (σ i).WellFormed sig.tyOps) :
    (c.tySubst σ).HasType sig (Γ.map (Ty.subst σ)) (Δ.map (Ty.subst σ))
      (A.subst σ) (B.subst σ) := by
  induction context with
  | hole => exact .hole
  | appLeft _ hx ih => exact .appLeft ih (hx.tySubst σ hσ)
  | appRight hf _ ih => exact .appRight (hf.tySubst σ hσ) ih
  | lam hC _ ih => exact .lam (hC.subst hσ) ih

end Context

instance : Cslib.HasContext Tm where
  Context := Context
  fill := Context.fill

@[simp] theorem cslib_fill_def (c : Context) (t : Tm) : c<[t] = c.fill t := rfl

end Tm
end Silmaril.Logic.HOLLight
