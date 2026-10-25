module

public import Mathlib.Data.Finset.Image

@[expose] public section

/-! Independent named, two-sorted syntax. Number and set names have separate
positions even when their underlying name types coincide. -/
namespace Silmaril.Logic.SecondOrderArithmetic

inductive Term (N : Type)
  | var (x : N) | zero | succ (t : Term N) | add (t u : Term N) | mul (t u : Term N)
  deriving DecidableEq, Repr

inductive Formula (N : Type)
  | equal (t u : Term N) | less (t u : Term N) | member (t : Term N) (X : N)
  | setEqual (X Y : N) | neg (φ : Formula N)
  | imp (φ ψ : Formula N) | iff (φ ψ : Formula N) | conj (φ ψ : Formula N)
  | all (x : N) (φ : Formula N) | ex (x : N) (φ : Formula N)
  | setAll (X : N) (φ : Formula N) | setEx (X : N) (φ : Formula N)
  deriving DecidableEq, Repr

variable {N : Type} [DecidableEq N]

namespace Term

def names : Term N → Finset N
  | .var x => {x} | .zero => ∅ | .succ t => t.names
  | .add t u | .mul t u => t.names ∪ u.names

/-- Simultaneous number substitution on terms. -/
def subst (σ : N → Term N) : Term N → Term N
  | .var x => σ x | .zero => .zero | .succ t => .succ (t.subst σ)
  | .add t u => .add (t.subst σ) (u.subst σ)
  | .mul t u => .mul (t.subst σ) (u.subst σ)

omit [DecidableEq N] in
@[simp] theorem subst_var (t : Term N) : t.subst .var = t := by
  induction t <;> simp_all [subst]

omit [DecidableEq N] in
theorem subst_comp (t : Term N) (σ τ : N → Term N) :
    (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  induction t <;> simp_all [subst]
end Term

namespace Formula

def free : Formula N → Finset (N ⊕ N)
  | .equal t u | .less t u => (t.names ∪ u.names).image Sum.inl
  | .member t X => t.names.image Sum.inl ∪ {Sum.inr X}
  | .setEqual X Y => {Sum.inr X, Sum.inr Y}
  | .neg φ => φ.free
  | .imp φ ψ | .iff φ ψ | .conj φ ψ => φ.free ∪ ψ.free
  | .all x φ | .ex x φ => φ.free.erase (.inl x)
  | .setAll X φ | .setEx X φ => φ.free.erase (.inr X)

/-- A closed sentence has no free names of either sort. -/
def Closed (φ : Formula N) : Prop := φ.free = ∅

/-- Capture-checked replacement of the free number name `x` by `t`.
Returns `none` when a number binder would capture a name in `t`. Set
binders cannot capture number names. It never silently renames a binder. -/
def substNum (x : N) (t : Term N) : Formula N → Option (Formula N)
  | .equal a b => some (.equal (a.subst (fun y => if y = x then t else .var y))
      (b.subst (fun y => if y = x then t else .var y)))
  | .less a b => some (.less (a.subst (fun y => if y = x then t else .var y))
      (b.subst (fun y => if y = x then t else .var y)))
  | .member a X => some (.member (a.subst (fun y => if y = x then t else .var y)) X)
  | .setEqual X Y => some (.setEqual X Y)
  | .neg φ => .neg <$> φ.substNum x t
  | .imp φ ψ => return .imp (← φ.substNum x t) (← ψ.substNum x t)
  | .iff φ ψ => return .iff (← φ.substNum x t) (← ψ.substNum x t)
  | .conj φ ψ => return .conj (← φ.substNum x t) (← ψ.substNum x t)
  | .all y φ => if y = x then some (.all y φ)
      else if y ∈ t.names then none else .all y <$> φ.substNum x t
  | .ex y φ => if y = x then some (.ex y φ)
      else if y ∈ t.names then none else .ex y <$> φ.substNum x t
  | .setAll Y φ => .setAll Y <$> φ.substNum x t
  | .setEx Y φ => .setEx Y <$> φ.substNum x t

/-- Capture-checked replacement of a free set name. Number binders are
unaffected because the syntax keeps the two sorts separate. -/
def substSet (X Y : N) : Formula N → Option (Formula N)
  | .equal a b => some (.equal a b)
  | .less a b => some (.less a b)
  | .member a Z => some (.member a (if Z = X then Y else Z))
  | .setEqual Z W => some (.setEqual (if Z = X then Y else Z) (if W = X then Y else W))
  | .neg φ => .neg <$> φ.substSet X Y
  | .imp φ ψ => return .imp (← φ.substSet X Y) (← ψ.substSet X Y)
  | .iff φ ψ => return .iff (← φ.substSet X Y) (← ψ.substSet X Y)
  | .conj φ ψ => return .conj (← φ.substSet X Y) (← ψ.substSet X Y)
  | .all z φ => .all z <$> φ.substSet X Y
  | .ex z φ => .ex z <$> φ.substSet X Y
  | .setAll Z φ => if Z = X then some (.setAll Z φ)
      else if Z = Y then none else .setAll Z <$> φ.substSet X Y
  | .setEx Z φ => if Z = X then some (.setEx Z φ)
      else if Z = Y then none else .setEx Z <$> φ.substSet X Y

/-- Bounded quantifiers are macros, with freshness enforced by `Bounded`. -/
def ball (x : N) (t : Term N) (φ : Formula N) : Formula N :=
  .all x (.imp (.less (.var x) t) φ)
def bex (x : N) (t : Term N) (φ : Formula N) : Formula N :=
  .ex x (.conj (.less (.var x) t) φ)
end Formula

/-- The exact bounded grammar used by the native database: set equality
is arithmetical but is not a bounded atom in this presentation. -/
inductive Bounded : Formula N → Prop
  | equal (t u) : Bounded (.equal t u)
  | less (t u) : Bounded (.less t u)
  | member (t X) : Bounded (.member t X)
  | neg {φ} : Bounded φ → Bounded (.neg φ)
  | imp {φ ψ} : Bounded φ → Bounded ψ → Bounded (.imp φ ψ)
  | iff {φ ψ} : Bounded φ → Bounded ψ → Bounded (.iff φ ψ)
  | conj {φ ψ} : Bounded φ → Bounded ψ → Bounded (.conj φ ψ)
  | ball (x t) {φ} : x ∉ t.names → Bounded φ → Bounded (.ball x t φ)
  | bex (x t) {φ} : x ∉ t.names → Bounded φ → Bounded (.bex x t φ)

/-- Native Σ⁰₁ normal form: bounded or one existential over bounded.
This is a syntax judgment, not the entire class up to logical equivalence. -/
inductive Sigma01 : Formula N → Prop
  | bounded {φ} : Bounded φ → Sigma01 φ
  | ex (x) {φ} : Bounded φ → Sigma01 (.ex x φ)

inductive Pi01 : Formula N → Prop
  | bounded {φ} : Bounded φ → Pi01 φ
  | all (x) {φ} : Bounded φ → Pi01 (.all x φ)

/-- No set quantifiers; free set parameters are permitted. -/
inductive Arithmetical : Formula N → Prop
  | equal (t u) : Arithmetical (.equal t u)
  | less (t u) : Arithmetical (.less t u)
  | member (t X) : Arithmetical (.member t X)
  | setEqual (X Y) : Arithmetical (.setEqual X Y)
  | neg {φ} : Arithmetical φ → Arithmetical (.neg φ)
  | imp {φ ψ} : Arithmetical φ → Arithmetical ψ → Arithmetical (.imp φ ψ)
  | iff {φ ψ} : Arithmetical φ → Arithmetical ψ → Arithmetical (.iff φ ψ)
  | conj {φ ψ} : Arithmetical φ → Arithmetical ψ → Arithmetical (.conj φ ψ)
  | all (x) {φ} : Arithmetical φ → Arithmetical (.all x φ)
  | ex (x) {φ} : Arithmetical φ → Arithmetical (.ex x φ)

theorem Bounded.arithmetical {φ : Formula N} (h : Bounded φ) : Arithmetical φ := by
  induction h with
  | equal t u => exact .equal t u
  | less t u => exact .less t u
  | member t X => exact .member t X
  | neg _ ih => exact .neg ih
  | imp _ _ ih ih' => exact .imp ih ih'
  | iff _ _ ih ih' => exact .iff ih ih'
  | conj _ _ ih ih' => exact .conj ih ih'
  | ball x t _ _ ih => exact .all x (.imp (.less _ _) ih)
  | bex x t _ _ ih => exact .ex x (.conj (.less _ _) ih)

theorem Sigma01.arithmetical {φ : Formula N} : Sigma01 φ → Arithmetical φ
  | .bounded h => h.arithmetical
  | .ex x h => .ex x h.arithmetical

theorem Pi01.arithmetical {φ : Formula N} : Pi01 φ → Arithmetical φ
  | .bounded h => h.arithmetical
  | .all x h => .all x h.arithmetical

end Silmaril.Logic.SecondOrderArithmetic
