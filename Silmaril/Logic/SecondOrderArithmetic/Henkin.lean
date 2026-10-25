module

public import Silmaril.Logic.SecondOrderArithmetic.Semantics

@[expose] public section

/-! General two-sorted structures. These may have nonstandard number carriers
and restricted set carriers. A structure is not claimed to satisfy any
subsystem until its axiom schemas have been checked. -/
namespace Silmaril.Logic.SecondOrderArithmetic

open Function

structure HenkinStructure where
  Numbers : Type
  Sets : Type
  zero : Numbers
  succ : Numbers → Numbers
  add : Numbers → Numbers → Numbers
  mul : Numbers → Numbers → Numbers
  less : Numbers → Numbers → Prop
  member : Numbers → Sets → Prop

abbrev HenkinStructure.Val (M : HenkinStructure) {N : Type} : N ⊕ N → Type
  | .inl _ => M.Numbers
  | .inr _ => M.Sets

abbrev HenkinStructure.Env (M : HenkinStructure) (N : Type) := (a : N ⊕ N) → M.Val a

variable {N : Type} [DecidableEq N]

def Term.henkinEval (M : HenkinStructure) : Term N → M.Env N → M.Numbers
  | .var x, ρ => ρ (.inl x)
  | .zero, _ => M.zero
  | .succ t, ρ => M.succ (t.henkinEval M ρ)
  | .add t u, ρ => M.add (t.henkinEval M ρ) (u.henkinEval M ρ)
  | .mul t u, ρ => M.mul (t.henkinEval M ρ) (u.henkinEval M ρ)

def Formula.henkinEval (M : HenkinStructure) : Formula N → M.Env N → Prop
  | .equal t u, ρ => t.henkinEval M ρ = u.henkinEval M ρ
  | .less t u, ρ => M.less (t.henkinEval M ρ) (u.henkinEval M ρ)
  | .member t X, ρ => M.member (t.henkinEval M ρ) (ρ (.inr X))
  | .setEqual X Y, ρ => ρ (.inr X) = ρ (.inr Y)
  | .neg φ, ρ => ¬ φ.henkinEval M ρ
  | .imp φ ψ, ρ => φ.henkinEval M ρ → ψ.henkinEval M ρ
  | .iff φ ψ, ρ => φ.henkinEval M ρ ↔ ψ.henkinEval M ρ
  | .conj φ ψ, ρ => φ.henkinEval M ρ ∧ ψ.henkinEval M ρ
  | .all x φ, ρ => ∀ n : M.Numbers, φ.henkinEval M (update ρ (.inl x) n)
  | .ex x φ, ρ => ∃ n : M.Numbers, φ.henkinEval M (update ρ (.inl x) n)
  | .setAll X φ, ρ => ∀ A : M.Sets, φ.henkinEval M (update ρ (.inr X) A)
  | .setEx X φ, ρ => ∃ A : M.Sets, φ.henkinEval M (update ρ (.inr X) A)

/-- Standard numbers and exactly the specified collection of sets. -/
def omegaStructure (𝒮 : Set (Set ℕ)) : HenkinStructure where
  Numbers := ℕ
  Sets := ↥𝒮
  zero := 0
  succ := (· + 1)
  add := (· + ·)
  mul := (· * ·)
  less := (· < ·)
  member n A := n ∈ A.val

omit [DecidableEq N] in
theorem Term.henkin_omega (t : Term N) (𝒮 : Set (Set ℕ)) :
    t.henkinEval (omegaStructure 𝒮) = t.eval (𝒮 := 𝒮) := by
  induction t <;> funext ρ <;> simp_all only [henkinEval, eval] <;> rfl

theorem Formula.henkin_omega (φ : Formula N) (𝒮 : Set (Set ℕ)) :
    φ.henkinEval (omegaStructure 𝒮) = φ.eval (𝒮 := 𝒮) := by
  induction φ <;> funext ρ <;>
    simp_all only [henkinEval, eval, Term.henkin_omega] <;> rfl

/-- Full standard second-order semantics uses every subset of ℕ. -/
def fullStandard : HenkinStructure := omegaStructure Set.univ

end Silmaril.Logic.SecondOrderArithmetic
