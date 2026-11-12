module

public import Silmaril.Raw.SSA.Isotope.SSA.FiniteSum
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Structural

/-! Injection and elimination of finite heterogeneous sums in let-iter. -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless
open SSA.FiniteSum (sumTy)

variable {ν : Type u} {Φ : Type v} {n : Nat}

/-- Tag a payload with its finite alternative. -/
def inject : {k : Nat} → Fin k → Tm ν Φ n → Tm ν Φ n
  | _ + 1, i, a => Fin.cases (.inl a) (fun j => .inr (inject j a)) i

/-- Dispatch a finite sum. The selected payload becomes the newest variable;
extra sum binders introduced by right branches are inserted below it. -/
def dispatch : {k n : Nat} → Tm ν Φ n → (Fin k → Tm ν Φ (n + 1)) → Tm ν Φ n
  | 0, _, a, _ => .abort a
  | _ + 1, _, a, bs => .case a (bs 0)
      (dispatch (.bv 0) (fun i => (bs i.succ).underBinder))

variable {τ : Type w} [TypeFormers τ] [HasTy Φ τ] [DecidableEq ν] {Γ : Ctx ν τ}

/-- Each tag accepts its own payload type, not a common block-argument type. -/
theorem inject_hasType {k : Nat} (A : Fin k → τ) (i : Fin k)
    {β : BoundCtx τ n} {a : Tm ν Φ n} (h : HasType Φ Γ β a (A i)) :
    HasType Φ Γ β (inject i a) (sumTy A) := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
      revert h
      refine Fin.cases (fun h => ?_) (fun j h => ?_) i
      · exact .inl h
      · exact .inr (ih (fun j => A j.succ) j h)

/-- Finite dispatch has a common result type while each arm receives its own
heterogeneous payload type. -/
theorem dispatch_hasType {k : Nat} (A : Fin k → τ) {β : BoundCtx τ n} {B : τ}
    {a : Tm ν Φ n} {bs : Fin k → Tm ν Φ (n + 1)}
    (ha : HasType Φ Γ β a (sumTy A))
    (hbs : ∀ i, HasType Φ Γ (.snoc β (A i)) (bs i) B) :
    HasType Φ Γ β (dispatch a bs) B := by
  induction k generalizing n with
  | zero => exact .abort ha
  | succ k ih =>
      apply HasType.case ha (hbs 0)
      exact ih (fun i => A i.succ) HasType.bv (fun i => (hbs i.succ).underBinder)

end Silmaril.Isotope.Morphism.SSAIter
