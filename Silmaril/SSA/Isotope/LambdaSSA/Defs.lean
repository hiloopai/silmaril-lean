module

public import Silmaril.Prelude.DeBruijn

/-!
# Lambda-SSA: syntax and operational semantics

The narrow lambda-SSA interface for code that only needs terms, regions and
their big-step semantics: runtime values (`Silmaril.Isotope.Value`), the syntax
(`Silmaril.Isotope.LambdaSSA.Tm`, `Body`, `Terminator`, `Block`, `Region`) with
its renaming and substitution functions, and the evaluation relations
`Semantics.Tm.Eval`, `Semantics.Region.Eval` and `Semantics.Region.Follow`.

Nothing here depends on typing. Typing is in
`Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs`; the renaming lemmas of evaluation
and its determinism are in `Silmaril.SSA.Isotope.LambdaSSA.Thms`.
-/

@[expose] public section

/-! # Runtime values shared by the compiler calculi -/

universe u

namespace Silmaril.Isotope

/-- Tagged runtime values over an arbitrary carrier of atomic values. -/
inductive Value (α : Type u) : Type u where
  | atom (a : α)
  | unit
  | pair (left right : Value α)
  | inl (value : Value α)
  | inr (value : Value α)
  deriving Repr, DecidableEq

end Silmaril.Isotope

end

@[expose] public section

/-!
# Lambda-SSA syntax

Value variables and block labels are separate de Bruijn namespaces. Raw syntax
is independent of instruction typing, effects, and categorical structure.
-/

universe u

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u}

open Silmaril.DeBruijn

/-- Expressions over primitive instructions `Φ`. Typing alone imposes no purity requirement. -/
inductive Tm (Φ : Type u) where
  | var (index : Nat)
  | op (opcode : Φ) (arg : Tm Φ)
  | let₁ (value body : Tm Φ)
  | pair (left right : Tm Φ)
  | unit
  | let₂ (value body : Tm Φ)
  | inl (value : Tm Φ)
  | inr (value : Tm Φ)
  | case (discr left right : Tm Φ)
  | abort (value : Tm Φ)
  deriving Repr, DecidableEq

namespace Tm

/-- Rename free value variables. -/
def rename (ρ : Nat → Nat) : Tm Φ → Tm Φ
  | .var i => .var (ρ i)
  | .op f a => .op f (a.rename ρ)
  | .let₁ a b => .let₁ (a.rename ρ) (b.rename (lift ρ))
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | .unit => .unit
  | .let₂ a b => .let₂ (a.rename ρ) (b.rename (liftN 2 ρ))
  | .inl a => .inl (a.rename ρ)
  | .inr a => .inr (a.rename ρ)
  | .case a l r => .case (a.rename ρ) (l.rename (lift ρ)) (r.rename (lift ρ))
  | .abort a => .abort (a.rename ρ)

/-- Lift a simultaneous substitution through one binder. -/
def liftSubst (σ : Nat → Tm Φ) : Nat → Tm Φ
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

/-- Lift a simultaneous substitution through `n` binders. -/
def liftSubstN : Nat → (Nat → Tm Φ) → Nat → Tm Φ
  | 0, σ => σ
  | n + 1, σ => liftSubst (liftSubstN n σ)

/-- Simultaneous substitution of free value variables. -/
def subst (σ : Nat → Tm Φ) : Tm Φ → Tm Φ
  | .var i => σ i
  | .op f a => .op f (a.subst σ)
  | .let₁ a b => .let₁ (a.subst σ) (b.subst (liftSubst σ))
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .unit => .unit
  | .let₂ a b => .let₂ (a.subst σ) (b.subst (liftSubstN 2 σ))
  | .inl a => .inl (a.subst σ)
  | .inr a => .inr (a.subst σ)
  | .case a l r => .case (a.subst σ) (l.subst (liftSubst σ)) (r.subst (liftSubst σ))
  | .abort a => .abort (a.subst σ)

end Tm

/-- A straight-line sequence of SSA definitions. -/
inductive Body (Φ : Type u) where
  | nil
  | let₁ (value : Tm Φ) (rest : Body Φ)
  | let₂ (value : Tm Φ) (rest : Body Φ)
  deriving Repr, DecidableEq

namespace Body

def bound : Body Φ → Nat
  | .nil => 0
  | .let₁ _ b => b.bound + 1
  | .let₂ _ b => b.bound + 2

def rename (ρ : Nat → Nat) : Body Φ → Body Φ
  | .nil => .nil
  | .let₁ a b => .let₁ (a.rename ρ) (b.rename (lift ρ))
  | .let₂ a b => .let₂ (a.rename ρ) (b.rename (liftN 2 ρ))

end Body

/-- Control transfer at the end of a block. -/
inductive Terminator (Φ : Type u) where
  | br (label : Nat) (arg : Tm Φ)
  | case (discr : Tm Φ) (left right : Terminator Φ)
  deriving Repr, DecidableEq

namespace Terminator

def renameVars (ρ : Nat → Nat) : Terminator Φ → Terminator Φ
  | .br ℓ a => .br ℓ (a.rename ρ)
  | .case a l r => .case (a.rename ρ) (l.renameVars (lift ρ)) (r.renameVars (lift ρ))

def renameLabels (ρ : Nat → Nat) : Terminator Φ → Terminator Φ
  | .br ℓ a => .br (ρ ℓ) a
  | .case a l r => .case a (l.renameLabels ρ) (r.renameLabels ρ)

end Terminator

/-- A straight-line body followed by a terminator. -/
structure Block (Φ : Type u) where
  body : Body Φ
  terminator : Terminator Φ
  deriving Repr, DecidableEq

namespace Block

def renameVars (ρ : Nat → Nat) (b : Block Φ) : Block Φ :=
  ⟨b.body.rename ρ, b.terminator.renameVars (liftN b.body.bound ρ)⟩

def renameLabels (ρ : Nat → Nat) (b : Block Φ) : Block Φ :=
  ⟨b.body, b.terminator.renameLabels ρ⟩

end Block

/-- Single-entry, multiple-exit regions with mutually recursive CFG binding. -/
inductive Region (Φ : Type u) where
  | br (label : Nat) (arg : Tm Φ)
  | case (discr : Tm Φ) (left right : Region Φ)
  | let₁ (value : Tm Φ) (body : Region Φ)
  | let₂ (value : Tm Φ) (body : Region Φ)
  | cfg (entry : Region Φ) (arity : Nat) (blocks : Fin arity → Region Φ)

namespace Region

def renameVars (ρ : Nat → Nat) : Region Φ → Region Φ
  | .br ℓ a => .br ℓ (a.rename ρ)
  | .case a l r => .case (a.rename ρ) (l.renameVars (lift ρ)) (r.renameVars (lift ρ))
  | .let₁ a r => .let₁ (a.rename ρ) (r.renameVars (lift ρ))
  | .let₂ a r => .let₂ (a.rename ρ) (r.renameVars (liftN 2 ρ))
  | .cfg e n bs => .cfg (e.renameVars ρ) n (fun i => (bs i).renameVars (lift ρ))

def renameLabels (ρ : Nat → Nat) : Region Φ → Region Φ
  | .br ℓ a => .br (ρ ℓ) a
  | .case a l r => .case a (l.renameLabels ρ) (r.renameLabels ρ)
  | .let₁ a r => .let₁ a (r.renameLabels ρ)
  | .let₂ a r => .let₂ a (r.renameLabels ρ)
  | .cfg e n bs =>
      .cfg (e.renameLabels (liftN n ρ)) n (fun i => (bs i).renameLabels (liftN n ρ))

end Region

end Silmaril.Isotope.LambdaSSA

end

/-!
# Operational semantics for lambda-SSA

Expressions evaluate left to right. A region returns an external label and its
argument. A CFG handles its internal labels by running the corresponding block
with its parameter and the environment captured at the CFG boundary. Local
temporaries from the caller are not visible in another block.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}

abbrev Env (α : Type u) := Nat → Value α

def extend (env : Env α) (value : Value α) : Env α
  | 0 => value
  | i + 1 => env i

@[simp] theorem extend_zero (env : Env α) (value : Value α) :
    extend env value 0 = value := rfl

@[simp] theorem extend_succ (env : Env α) (value : Value α) (i : Nat) :
    extend env value (i + 1) = env i := rfl

namespace Tm

/-- Finite expression evaluation with atomic instruction transitions. -/
inductive Eval (instr : Φ → Value α → σ → Value α → σ → Prop) :
    Env α → LambdaSSA.Tm Φ → σ → Value α → σ → Prop where
  | var {env : Env α} {i : Nat} {s : σ} : Eval instr env (.var i) s (env i) s
  | op {env : Env α} {f : Φ} {a : LambdaSSA.Tm Φ} {s s₁ s₂ : σ}
      {va value : Value α} :
      Eval instr env a s va s₁ → instr f va s₁ value s₂ →
      Eval instr env (.op f a) s value s₂
  | let₁ {env : Env α} {a b : LambdaSSA.Tm Φ} {s s₁ s₂ : σ} {va value : Value α} :
      Eval instr env a s va s₁ → Eval instr (extend env va) b s₁ value s₂ →
      Eval instr env (.let₁ a b) s value s₂
  | unit {env : Env α} {s : σ} : Eval instr env .unit s .unit s
  | pair {env : Env α} {a b : LambdaSSA.Tm Φ} {s s₁ s₂ : σ} {va vb : Value α} :
      Eval instr env a s va s₁ → Eval instr env b s₁ vb s₂ →
      Eval instr env (.pair a b) s (.pair va vb) s₂
  | let₂ {env : Env α} {a b : LambdaSSA.Tm Φ} {s s₁ s₂ : σ} {va vb value : Value α} :
      Eval instr env a s (.pair va vb) s₁ →
      Eval instr (extend (extend env va) vb) b s₁ value s₂ →
      Eval instr env (.let₂ a b) s value s₂
  | inl {env : Env α} {a : LambdaSSA.Tm Φ} {s s' : σ} {value : Value α} :
      Eval instr env a s value s' → Eval instr env (.inl a) s (.inl value) s'
  | inr {env : Env α} {a : LambdaSSA.Tm Φ} {s s' : σ} {value : Value α} :
      Eval instr env a s value s' → Eval instr env (.inr a) s (.inr value) s'
  | case_inl {env : Env α} {a l r : LambdaSSA.Tm Φ} {s s₁ s₂ : σ} {va value : Value α} :
      Eval instr env a s (.inl va) s₁ → Eval instr (extend env va) l s₁ value s₂ →
      Eval instr env (.case a l r) s value s₂
  | case_inr {env : Env α} {a l r : LambdaSSA.Tm Φ} {s s₁ s₂ : σ} {va value : Value α} :
      Eval instr env a s (.inr va) s₁ → Eval instr (extend env va) r s₁ value s₂ →
      Eval instr env (.case a l r) s value s₂

variable {instr : Φ → Value α → σ → Value α → σ → Prop} in
/-- Read a specified value from an arbitrary environment, without requiring
the surrounding environment to be given by a particular construction. -/
theorem Eval.var_of_eq {env : Env α} {i : Nat} {s : σ} {value : Value α}
    (same : env i = value) : Eval instr env (.var i) s value s := by
  subst value
  exact .var

end Tm

namespace Region

mutual

/-- Finite region execution, returning an external label and its argument. -/
inductive Eval (instr : Φ → Value α → σ → Value α → σ → Prop) :
    Env α → LambdaSSA.Region Φ → σ → Nat → Value α → σ → Prop where
  | br {env : Env α} {label : Nat} {arg : LambdaSSA.Tm Φ}
      {s s' : σ} {value : Value α} :
      Tm.Eval instr env arg s value s' → Eval instr env (.br label arg) s label value s'
  | let₁ {env : Env α} {a : LambdaSSA.Tm Φ} {r : LambdaSSA.Region Φ}
      {s s₁ s₂ : σ} {va value : Value α} {label : Nat} :
      Tm.Eval instr env a s va s₁ → Eval instr (extend env va) r s₁ label value s₂ →
      Eval instr env (.let₁ a r) s label value s₂
  | let₂ {env : Env α} {a : LambdaSSA.Tm Φ} {r : LambdaSSA.Region Φ}
      {s s₁ s₂ : σ} {va vb value : Value α} {label : Nat} :
      Tm.Eval instr env a s (.pair va vb) s₁ →
      Eval instr (extend (extend env va) vb) r s₁ label value s₂ →
      Eval instr env (.let₂ a r) s label value s₂
  | case_inl {env : Env α} {a : LambdaSSA.Tm Φ} {l r : LambdaSSA.Region Φ}
      {s s₁ s₂ : σ} {va value : Value α} {label : Nat} :
      Tm.Eval instr env a s (.inl va) s₁ → Eval instr (extend env va) l s₁ label value s₂ →
      Eval instr env (.case a l r) s label value s₂
  | case_inr {env : Env α} {a : LambdaSSA.Tm Φ} {l r : LambdaSSA.Region Φ}
      {s s₁ s₂ : σ} {va value : Value α} {label : Nat} :
      Tm.Eval instr env a s (.inr va) s₁ → Eval instr (extend env va) r s₁ label value s₂ →
      Eval instr env (.case a l r) s label value s₂
  | cfg {env : Env α} {entry : LambdaSSA.Region Φ} {n : Nat}
      {blocks : Fin n → LambdaSSA.Region Φ} {s s₁ s₂ : σ}
      {initial value : Value α} {first label : Nat} :
      Eval instr env entry s first initial s₁ →
      Follow instr env blocks first initial s₁ label value s₂ →
      Eval instr env (.cfg entry n blocks) s label value s₂

/-- Follow internal transfers, restoring the captured environment at each block. -/
inductive Follow (instr : Φ → Value α → σ → Value α → σ → Prop) :
    Env α → {n : Nat} → (Fin n → LambdaSSA.Region Φ) →
    Nat → Value α → σ → Nat → Value α → σ → Prop where
  | exit {env : Env α} {n label : Nat} {blocks : Fin n → LambdaSSA.Region Φ}
      {value : Value α} {s : σ} : n ≤ label →
      Follow instr env blocks label value s (label - n) value s
  | step {env : Env α} {n label next out : Nat} {blocks : Fin n → LambdaSSA.Region Φ}
      {current middle value : Value α} {s s₁ s₂ : σ} (inside : label < n) :
      Eval instr (extend env current) (blocks ⟨label, inside⟩) s next middle s₁ →
      Follow instr env blocks next middle s₁ out value s₂ →
      Follow instr env blocks label current s out value s₂

end

end Region

/-- Every primitive instruction has at most one result and final state. -/
def InstrDeterministic (instr : Φ → Value α → σ → Value α → σ → Prop) : Prop :=
  ∀ f a s b s' c s'', instr f a s b s' → instr f a s c s'' → b = c ∧ s' = s''

end Silmaril.Isotope.LambdaSSA.Semantics

end
