module

public import Silmaril.Logic.Arithmetic.Semantics

@[expose] public section

/-! Proof-relevant classical natural deduction, parameterized by an arithmetic
family of axioms. Quantifier introductions/eliminations use a fresh scoped variable:
the surrounding context and existential conclusion are shifted into the larger
scope, so neither can depend on the eigenvariable. -/
namespace Silmaril.Logic.Arithmetic


inductive Derivation (Ax : {n : ℕ} → Formula n → Type) :
    {n : ℕ} → Context n → Formula n → Type where
  | hyp {n : ℕ} {φ : Formula n} {Γ : Context n} : φ ∈ Γ → Derivation Ax Γ φ
  | ax {n : ℕ} {φ : Formula n} {Γ : Context n} : Ax φ → Derivation Ax Γ φ
  | weaken {n : ℕ} {ψ : Formula n} {Γ Δ : Context n} : (∀ φ ∈ Γ, φ ∈ Δ) → Derivation Ax Γ ψ → Derivation Ax Δ ψ
  | impIntro {n : ℕ} {φ ψ : Formula n} {Γ : Context n} : Derivation Ax (φ :: Γ) ψ → Derivation Ax Γ (.imp φ ψ)
  | impElim {n : ℕ} {φ ψ : Formula n} {Γ : Context n} : Derivation Ax Γ (.imp φ ψ) → Derivation Ax Γ φ → Derivation Ax Γ ψ
  | botElim {n : ℕ} {φ : Formula n} {Γ : Context n} : Derivation Ax Γ .bot → Derivation Ax Γ φ
  | classical {n : ℕ} {φ : Formula n} {Γ : Context n} : Derivation Ax Γ φ.neg.neg → Derivation Ax Γ φ
  | conjIntro {n : ℕ} {φ ψ : Formula n} {Γ : Context n} : Derivation Ax Γ φ → Derivation Ax Γ ψ → Derivation Ax Γ (.conj φ ψ)
  | conjLeft {n : ℕ} {φ ψ : Formula n} {Γ : Context n} : Derivation Ax Γ (.conj φ ψ) → Derivation Ax Γ φ
  | conjRight {n : ℕ} {φ ψ : Formula n} {Γ : Context n} : Derivation Ax Γ (.conj φ ψ) → Derivation Ax Γ ψ
  | disjLeft {n : ℕ} {φ ψ : Formula n} {Γ : Context n} : Derivation Ax Γ φ → Derivation Ax Γ (.disj φ ψ)
  | disjRight {n : ℕ} {φ ψ : Formula n} {Γ : Context n} : Derivation Ax Γ ψ → Derivation Ax Γ (.disj φ ψ)
  | disjElim {n : ℕ} {φ ψ χ : Formula n} {Γ : Context n} : Derivation Ax Γ (.disj φ ψ) → Derivation Ax (φ :: Γ) χ →
      Derivation Ax (ψ :: Γ) χ → Derivation Ax Γ χ
  | allIntro {n : ℕ} {Γ : Context n} {φ : Formula (n + 1)} : Derivation Ax (Γ.map Formula.shift) φ → Derivation Ax Γ (.all φ)
  | allElim {n : ℕ} {Γ : Context n} {φ : Formula (n + 1)} : Derivation Ax Γ (.all φ) → (t : Term n) → Derivation Ax Γ (φ.inst t)
  | exIntro {n : ℕ} {Γ : Context n} {φ : Formula (n + 1)} : (t : Term n) → Derivation Ax Γ (φ.inst t) → Derivation Ax Γ (.ex φ)
  | exElim {n : ℕ} {Γ : Context n} {φ : Formula (n + 1)} {ψ : Formula n} : Derivation Ax Γ (.ex φ) →
      Derivation Ax (φ :: Γ.map Formula.shift) ψ.shift → Derivation Ax Γ ψ
  | eqRefl {n : ℕ} {Γ : Context n} : (t : Term n) → Derivation Ax Γ (.equal t t)
  | eqElim {n : ℕ} {Γ : Context n} {s t : Term n} : (φ : Formula (n + 1)) → Derivation Ax Γ (.equal s t) →
      Derivation Ax Γ (φ.inst s) → Derivation Ax Γ (φ.inst t)

namespace Derivation

variable {n : ℕ} {Γ : Context n} {ψ : Formula n}
variable {Ax Bx : {n : ℕ} → Formula n → Type}

/-- Translate every proof constructor while replacing arithmetic axiom proofs. -/
def map {n : ℕ} {Γ : Context n} {ψ : Formula n} (f : ∀ {n} {φ : Formula n}, Ax φ → Derivation Bx [] φ) :
    Derivation Ax Γ ψ → Derivation Bx Γ ψ
  | .hyp h => .hyp h
  | .ax h => .weaken (by simp) (f h)
  | .weaken h d => .weaken h (map f d)
  | .impIntro d => .impIntro (map f d)
  | .impElim d e => .impElim (map f d) (map f e)
  | .botElim d => .botElim (map f d)
  | .classical d => .classical (map f d)
  | .conjIntro d e => .conjIntro (map f d) (map f e)
  | .conjLeft d => .conjLeft (map f d)
  | .conjRight d => .conjRight (map f d)
  | .disjLeft d => .disjLeft (map f d)
  | .disjRight d => .disjRight (map f d)
  | .disjElim d e f' => .disjElim (map f d) (map f e) (map f f')
  | .allIntro d => .allIntro (map f d)
  | .allElim d t => .allElim (map f d) t
  | .exIntro t d => .exIntro t (map f d)
  | .exElim d e => .exElim (map f d) (map f e)
  | .eqRefl t => .eqRefl t
  | .eqElim φ d e => .eqElim φ (map f d) (map f e)


end Derivation
end Silmaril.Logic.Arithmetic
