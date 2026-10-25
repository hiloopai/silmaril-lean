module

public import Silmaril.Logic.SecondOrderArithmetic.Base

@[expose] public section

/-! Effective Hilbert derivations and exact restricted schemata. `WKL0Sep`
names the Σ⁰₁-separation presentation; the tree formulation of weak König's
lemma and its equivalence over RCA₀ remain a separate milestone. -/
namespace Silmaril.Logic.SecondOrderArithmetic

variable {N : Type} [DecidableEq N]

namespace Formula

/-- Pointwise induction avoids an implicit substitution operation. The fresh
auxiliary name `y` is required by each induction axiom constructor below. -/
def induction (x y : N) (φ : Formula N) : Formula N :=
  .imp (.all x (.imp (.equal (.var x) .zero) φ))
    (.imp (.all y (.imp (.all x (.imp (.equal (.var x) (.var y)) φ))
      (.all x (.imp (.equal (.var x) (.succ (.var y))) φ)))) (.all x φ))

def comprehension (x X : N) (φ : Formula N) : Formula N :=
  .setEx X (.all x (.iff (.member (.var x) X) φ))

def deltaComprehension (x X : N) (φ ψ : Formula N) : Formula N :=
  .imp (.all x (.iff φ ψ)) (.comprehension x X φ)

def separation (x X : N) (φ ψ : Formula N) : Formula N :=
  .imp (.all x (.neg (.conj φ ψ)))
    (.setEx X (.all x (.conj (.imp φ (.member (.var x) X))
      (.imp ψ (.neg (.member (.var x) X))))))
end Formula

inductive Subsystem
  | RCA0 | WKL0Sep | ACA0 | Z2 | Z2Full
  deriving DecidableEq, Repr

/-- The schema family of each subsystem. Side conditions are syntactic
judgments, and full comprehension is a formula schema. -/
inductive Axiom (S : Subsystem) : Formula N → Type
  | base {φ} : BaseAxiom φ → Axiom S φ
  | sigmaInd (x y φ) : S ≠ .Z2Full → Sigma01 φ → x ≠ y → y ∉ φ.names →
      Axiom S (.induction x y φ)
  | deltaComp (x X φ ψ) : (S = .RCA0 ∨ S = .WKL0Sep) →
      Sigma01 φ → Pi01 ψ → X ∉ φ.names → X ∉ ψ.names →
      Axiom S (.deltaComprehension x X φ ψ)
  | sep (x X φ ψ) : S = .WKL0Sep →
      Sigma01 φ → Sigma01 ψ → X ∉ φ.names → X ∉ ψ.names →
      Axiom S (.separation x X φ ψ)
  | arithComp (x X φ) : (S = .ACA0 ∨ S = .Z2) →
      Arithmetical φ → X ∉ φ.names → Axiom S (.comprehension x X φ)
  | fullInd (x y φ) : (S = .Z2 ∨ S = .Z2Full) → x ≠ y → y ∉ φ.names →
      Axiom S (.induction x y φ)
  | fullComp (x X φ) : (S = .Z2 ∨ S = .Z2Full) → X ∉ φ.names →
      Axiom S (.comprehension x X φ)

/-- Finite proof trees, with no semantic-truth rule. Generalization applies
to theorems (there are no undischarged formula hypotheses). -/
inductive Proof (S : Subsystem) : Formula N → Type
  | axiom {φ} : Axiom S φ → Proof S φ
  | mp {φ ψ} : Proof S φ → Proof S (.imp φ ψ) → Proof S ψ
  | gen (x) {φ} : Proof S φ → Proof S (.all x φ)
  | setGen (X) {φ} : Proof S φ → Proof S (.setAll X φ)

abbrev Provable (S : Subsystem) (φ : Formula N) : Prop := Nonempty (Proof S φ)

namespace Proof

/-- Transport actual derivations once every source axiom has a target proof. -/
def map {S T : Subsystem} (f : ∀ {φ : Formula N}, Axiom S φ → Proof T φ)
    {φ : Formula N} : Proof S φ → Proof T φ
  | .axiom h => f h
  | .mp p q => .mp (p.map f) (q.map f)
  | .gen x p => .gen x (p.map f)
  | .setGen X p => .setGen X (p.map f)

/-- Adding an antecedent is proved by ax-1 and modus ponens. -/
def weaken {S : Subsystem} {φ : Formula N} (p : Proof S φ) (ψ : Formula N) :
    Proof S (.imp ψ φ) := .mp p (.axiom (.base (.ax1 φ ψ)))

/-- The native `dcomp-aca` argument, now as an independent proof tree. -/
def deltaCompACA (x X : N) (φ ψ : Formula N) (hφ : Sigma01 φ) (hX : X ∉ φ.names) :
    Proof .ACA0 (.deltaComprehension x X φ ψ) :=
  (Proof.axiom (.arithComp x X φ (Or.inl rfl) hφ.arithmetical hX)).weaken (.all x (.iff φ ψ))

def rcaToWkl {φ : Formula N} : Proof .RCA0 φ → Proof .WKL0Sep φ := map fun a => by
  cases a with
  | base h => exact .axiom (.base h)
  | sigmaInd x y φ _ h hxy hy => exact .axiom (.sigmaInd x y φ (by decide) h hxy hy)
  | deltaComp x X φ ψ _ hφ hψ hX hX' =>
    exact .axiom (.deltaComp x X φ ψ (Or.inr rfl) hφ hψ hX hX')
  | sep _ _ _ _ h _ _ _ _ => cases h
  | arithComp _ _ _ h _ _ => exact False.elim (by simp at h)
  | fullInd _ _ _ h _ _ => exact False.elim (by simp at h)
  | fullComp _ _ _ h _ => exact False.elim (by simp at h)

def rcaToACA {φ : Formula N} : Proof .RCA0 φ → Proof .ACA0 φ := map fun a => by
  cases a with
  | base h => exact .axiom (.base h)
  | sigmaInd x y φ _ h hxy hy => exact .axiom (.sigmaInd x y φ (by decide) h hxy hy)
  | deltaComp x X φ ψ _ hφ _ hX _ => exact deltaCompACA x X φ ψ hφ hX
  | sep _ _ _ _ h _ _ _ _ => cases h
  | arithComp _ _ _ h _ _ => exact False.elim (by simp at h)
  | fullInd _ _ _ h _ _ => exact False.elim (by simp at h)
  | fullComp _ _ _ h _ => exact False.elim (by simp at h)

def acaToZ2 {φ : Formula N} : Proof .ACA0 φ → Proof .Z2 φ := map fun a => by
  cases a with
  | base h => exact .axiom (.base h)
  | sigmaInd x y φ _ h hxy hy => exact .axiom (.sigmaInd x y φ (by decide) h hxy hy)
  | deltaComp _ _ _ _ h _ _ _ _ => exact False.elim (by simp at h)
  | sep _ _ _ _ h _ _ _ _ => cases h
  | arithComp x X φ _ hφ hX => exact .axiom (.arithComp x X φ (Or.inr rfl) hφ hX)
  | fullInd _ _ _ h _ _ => exact False.elim (by simp at h)
  | fullComp _ _ _ h _ => exact False.elim (by simp at h)

/-- Restricted induction and arithmetical comprehension are instances of
full schemas. This constructs a proof, without appealing to semantics. -/
def z2ToFull {φ : Formula N} : Proof .Z2 φ → Proof .Z2Full φ := map fun a => by
  cases a with
  | base h => exact .axiom (.base h)
  | sigmaInd x y φ _ _ hxy hy => exact .axiom (.fullInd x y φ (Or.inr rfl) hxy hy)
  | deltaComp _ _ _ _ h _ _ _ _ => exact False.elim (by simp at h)
  | sep _ _ _ _ h _ _ _ _ => cases h
  | arithComp x X φ _ _ hX => exact .axiom (.fullComp x X φ (Or.inr rfl) hX)
  | fullInd x y φ _ hxy hy => exact .axiom (.fullInd x y φ (Or.inr rfl) hxy hy)
  | fullComp x X φ _ hX => exact .axiom (.fullComp x X φ (Or.inr rfl) hX)

def fullToZ2 {φ : Formula N} : Proof .Z2Full φ → Proof .Z2 φ := map fun a => by
  cases a with
  | base h => exact .axiom (.base h)
  | sigmaInd _ _ _ h _ _ _ => exact False.elim (h rfl)
  | deltaComp _ _ _ _ h _ _ _ _ => exact False.elim (by simp at h)
  | sep _ _ _ _ h _ _ _ _ => cases h
  | arithComp _ _ _ h _ _ => exact False.elim (by simp at h)
  | fullInd x y φ _ hxy hy => exact .axiom (.fullInd x y φ (Or.inl rfl) hxy hy)
  | fullComp x X φ _ hX => exact .axiom (.fullComp x X φ (Or.inl rfl) hX)
end Proof

theorem z2_iff_full (φ : Formula N) : Provable .Z2 φ ↔ Provable .Z2Full φ :=
  ⟨Nonempty.map Proof.z2ToFull, Nonempty.map Proof.fullToZ2⟩

end Silmaril.Logic.SecondOrderArithmetic
