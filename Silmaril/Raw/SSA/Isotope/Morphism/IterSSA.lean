module

public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Typing
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.VariableBranches

/-!
# Continuation-passing compilation from let-iter to lambda-SSA

Every computed result is bound once. Loops become single-block CFGs whose
parameter holds the current state; their branch arguments are variables.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.IterSSA

open LetIter.LocallyNameless (Tm)
open LambdaSSA (Region)

variable {ν : Type w} {Φ : Type v} {τ : Type u} {n : Nat}

/-- Locations of source free and bound variables in the target value context. -/
structure Vars (ν : Type w) (n : Nat) where
  free : ν → Nat
  bound : Fin n → Nat

namespace Vars

/-- Insert an administrative target variable without adding a source binder. -/
def shift (σ : Vars ν n) : Vars ν n :=
  ⟨fun x => σ.free x + 1, fun i => σ.bound i + 1⟩

/-- Add a common newest source and target variable. -/
def bind (σ : Vars ν n) : Vars ν (n + 1) :=
  ⟨fun x => σ.free x + 1, Fin.cases 0 (fun i => σ.bound i + 1)⟩

/-- Every mapped source variable has its original type in the target context. -/
structure HasType [DecidableEq ν] (Γ : Ctx ν τ) (β : BoundCtx τ n)
    (Δ : SSA.VCtx τ) (σ : Vars ν n) : Prop where
  free : ∀ ⦃x A⦄, Γ.lookup x = some A → SSA.At Δ (σ.free x) A
  bound : ∀ i, SSA.At Δ (σ.bound i) (β.get i)

variable [DecidableEq ν]

theorem HasType.shift {Γ : Ctx ν τ} {β : BoundCtx τ n} {Δ : SSA.VCtx τ}
    {σ : Vars ν n} (hσ : HasType Γ β Δ σ) (A : τ) : HasType Γ β (A :: Δ) σ.shift where
  free := by intro x B h; exact hσ.free h
  bound i := hσ.bound i

theorem HasType.bind {Γ : Ctx ν τ} {β : BoundCtx τ n} {Δ : SSA.VCtx τ}
    {σ : Vars ν n} (hσ : HasType Γ β Δ σ) (A : τ) :
    HasType Γ (.snoc β A) (A :: Δ) σ.bind where
  free := by intro x B h; exact hσ.free h
  bound := Fin.cases rfl (fun i => hσ.bound i)

end Vars

/-- Insert an administrative variable beneath the continuation's result. -/
def under (k : Region Φ) : Region Φ := k.renameVars (Silmaril.DeBruijn.lift Nat.succ)

/-- Compile a term with a value-variable assignment and a continuation under
one result binder. Source evaluation order is preserved by nested lets. -/
def compile : {n : Nat} → Tm ν Φ n → Vars ν n → Region Φ → Region Φ
  | _, .fv x, σ, k => .let₁ (.var (σ.free x)) k
  | _, .bv i, σ, k => .let₁ (.var (σ.bound i)) k
  | _, .unit, _, k => .let₁ .unit k
  | _, .op f a, σ, k => compile a σ (.let₁ (.op f (.var 0)) (under k))
  | _, .pair a b, σ, k =>
      compile a σ (compile b σ.shift (.let₁ (.pair (.var 1) (.var 0)) (under (under k))))
  | _, .let₁ a b, σ, k => compile a σ (compile b σ.bind (under k))
  | _, .let₂ a b, σ, k =>
      compile a σ (.let₂ (.var 0) (compile b σ.shift.bind.bind (under (under (under k)))))
  | _, .inl a, σ, k => compile a σ (.let₁ (.inl (.var 0)) (under k))
  | _, .inr a, σ, k => compile a σ (.let₁ (.inr (.var 0)) (under k))
  | _, .case a l r, σ, k => compile a σ (.case (.var 0)
      (compile l σ.shift.bind (under (under k)))
      (compile r σ.shift.bind (under (under k))))
  | _, .abort a, σ, k => compile a σ (.let₁ (.abort (.var 0)) (under k))
  | _, .iter init body, σ, k => .cfg (compile init σ (.br 0 (.var 0))) 1 (fun _ =>
      compile body σ.bind (.case (.var 0)
        (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0))))

/-- The continuation's branch discipline is unchanged by an administrative binder. -/
theorem under_variableBranches {k : Region Φ} (hk : Region.VariableBranches k) :
    Region.VariableBranches (under k) := hk.renameVars _

/-- Compilation introduces only variable branch arguments. Any other branch
arguments must come from the supplied continuation. -/
theorem compile_variableBranches (t : Tm ν Φ n) (σ : Vars ν n) {k : Region Φ}
    (hk : Region.VariableBranches k) : Region.VariableBranches (compile t σ k) := by
  induction t generalizing k with
  | fv => exact .let₁ hk
  | bv => exact .let₁ hk
  | unit => exact .let₁ hk
  | op f a ih => exact ih σ (.let₁ (under_variableBranches hk))
  | pair a b iha ihb =>
      exact iha σ (ihb σ.shift (.let₁ (under_variableBranches (under_variableBranches hk))))
  | let₁ a b iha ihb => exact iha σ (ihb σ.bind (under_variableBranches hk))
  | let₂ a b iha ihb =>
      exact iha σ (.let₂ (ihb σ.shift.bind.bind
        (under_variableBranches (under_variableBranches (under_variableBranches hk)))))
  | inl a ih => exact ih σ (.let₁ (under_variableBranches hk))
  | inr a ih => exact ih σ (.let₁ (under_variableBranches hk))
  | case a l r iha ihl ihr =>
      exact iha σ (.case
        (ihl σ.shift.bind (under_variableBranches (under_variableBranches hk)))
        (ihr σ.shift.bind (under_variableBranches (under_variableBranches hk))))
  | abort a ih => exact ih σ (.let₁ (under_variableBranches hk))
  | iter a b iha ihb =>
      exact .cfg (iha σ .br) (fun _ => ihb σ.bind (.case
        (under_variableBranches (under_variableBranches (hk.renameLabels Nat.succ))) .br))

variable [DecidableEq ν] [TypeFormers τ] [HasTy Φ τ]

/-- Adding a temporary beneath the result preserves continuation typing. -/
theorem under_typed {Δ : SSA.VCtx τ} {L : SSA.LCtx τ} {k : Region Φ} {A : τ}
    (hk : Region.HasType (A :: Δ) k L) (B : τ) :
    Region.HasType (A :: B :: Δ) (under k) L :=
  hk.renameVars ((SSA.Ren.wk Δ B).lift A)

/-- General CPS compilation preserves exact typing for arbitrary source
variables, ambient target values, result continuations, and exit labels. -/
theorem compile_typed {Γ : Ctx ν τ} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    {Δ : SSA.VCtx τ} {L : SSA.LCtx τ} {σ : Vars ν n} {k : Region Φ}
    (ht : LetIter.LocallyNameless.HasType Φ Γ β t A)
    (hσ : Vars.HasType Γ β Δ σ) (hk : Region.HasType (A :: Δ) k L) :
    Region.HasType Δ (compile t σ k) L := by
  induction ht generalizing Δ L k with
  | fv h => exact .let₁ (.var (hσ.free h)) hk
  | bv => exact .let₁ (.var (hσ.bound _)) hk
  | unit => exact .let₁ .unit hk
  | op ha ih => exact ih hσ (.let₁ (.op (.var rfl)) (under_typed hk _))
  | pair ha hb iha ihb =>
      exact iha hσ (ihb (hσ.shift _) (.let₁ (.pair (.var rfl) (.var rfl))
        (under_typed (under_typed hk _) _)))
  | let₁ ha hb iha ihb => exact iha hσ (ihb (hσ.bind _) (under_typed hk _))
  | let₂ ha hb iha ihb =>
      exact iha hσ (.let₂ (.var rfl) (ihb (((hσ.shift _).bind _).bind _)
        (under_typed (under_typed (under_typed hk _) _) _)))
  | inl ha ih => exact ih hσ (.let₁ (.inl (.var rfl)) (under_typed hk _))
  | inr ha ih => exact ih hσ (.let₁ (.inr (.var rfl)) (under_typed hk _))
  | case ha hl hr iha ihl ihr =>
      exact iha hσ (.case (.var rfl)
        (ihl ((hσ.shift _).bind _) (under_typed (under_typed hk _) _))
        (ihr ((hσ.shift _).bind _) (under_typed (under_typed hk _) _)))
  | abort ha ih => exact ih hσ (.let₁ (.abort (.var rfl)) (under_typed hk _))
  | @iter n β a b A B ha hb iha ihb =>
      apply Region.HasType.cfg (fun _ => A)
      · exact iha hσ (.br rfl (.var rfl))
      · intro i
        exact ihb (hσ.bind A) (.case (.var rfl)
          (under_typed (under_typed (hk.renameLabels (SSA.Ren.wk L A)) A) (coprod B A))
          (.br rfl (.var rfl)))

end Silmaril.Isotope.Morphism.IterSSA
