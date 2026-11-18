module

public import Silmaril.Logic.Consequence.FirstOrder.Syntax.Defs
public import Silmaril.Logic.Consequence.FirstOrder.Defs
public import Silmaril.Logic.Institution.Examples.Unsorted.SExp.Defs
public import Silmaril.Logic.Consequence.Derivation.Defs

/-!
# First-order logic as a derivation system: classical natural deduction over any signature

Unsorted first-order logic with equality (`Silmaril.Logic.Institution.Examples.UFOL`: `=`,
relations, `⊤`, `¬`, `∧`, `∀`), over a signature `Sg` whose symbols of each arity have decidable
equality.

**Judgments** (`Seq Sg`): `Γ ⊢ φ` with `k` de Bruijn variables in scope.

**Rules** (`Rule Sg k`): each label carries its context and formulas, so it determines its premises
(`Rule.prems`) and conclusion (`Rule.concl`); two have side conditions (`Rule.side`).

| rule | premises | conclusion |
|---|---|---|
| `hyp Γ φ` | — | `Γ ⊢ φ` (`φ ∈ Γ`) |
| `weaken Γ Δ φ` | `Γ ⊢ φ` | `Δ ⊢ φ` (`Γ ⊆ Δ`) |
| `ttIntro Γ` | — | `Γ ⊢ ⊤` |
| `notIntro Γ φ ψ` | `φ :: Γ ⊢ ψ`, `φ :: Γ ⊢ ¬ψ` | `Γ ⊢ ¬φ` |
| `notElim Γ φ ψ` | `Γ ⊢ φ`, `Γ ⊢ ¬φ` | `Γ ⊢ ψ` |
| `dne Γ φ` | `Γ ⊢ ¬¬φ` | `Γ ⊢ φ` |
| `andIntro`, `andLeft`, `andRight` | as usual | |
| `allIntro Γ φ` | `Γ↑ ⊢ φ` (one more variable) | `Γ ⊢ ∀ φ` |
| `allElim Γ φ t` | `Γ ⊢ ∀ φ` | `Γ ⊢ φ[t]` |
| `eqRefl Γ t` | — | `Γ ⊢ t = t` |
| `eqElim Γ φ s t` | `Γ ⊢ s = t`, `Γ ⊢ φ[s]` | `Γ ⊢ φ[t]` |

**Semantics.** `Seq.ValidIn M s`: every assignment in the structure `M` satisfying the hypotheses
satisfies the conclusion. `Thms` proves every rule instance preserves it in every structure, so
`treeDerives Sg` (valid trees from no assumptions concluding `Γ ⊢ φ` with no free variables) is
sound for semantic consequence (`consequence Sg`) and for truth in each structure.
-/

@[expose] public section

namespace Silmaril.Consequence.FirstOrder.ND

open Silmaril.Logic.Institution.Examples.UFOL

variable (Sg : Signature)

/-- A judgment `Γ ⊢ φ` with `k` variables in scope. -/
structure Seq where
  /-- The number of variables in scope. -/
  k : ℕ
  /-- The hypotheses. -/
  ctx : List (Formula Sg k)
  /-- The conclusion. -/
  goal : Formula Sg k

variable {Sg}

/-- Named signatures (`named`, used by the S-expression presentation) have decidable symbols. -/
instance (opArity relArity : String → Option ℕ) (n : ℕ) :
    DecidableEq ((named opArity relArity).Op n) :=
  inferInstanceAs (DecidableEq {f : String // opArity f = some n})

instance (opArity relArity : String → Option ℕ) (n : ℕ) :
    DecidableEq ((named opArity relArity).Rel n) :=
  inferInstanceAs (DecidableEq {r : String // relArity r = some n})

instance [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)] : DecidableEq (Seq Sg) :=
  fun ⟨k, Γ, φ⟩ ⟨k', Γ', φ'⟩ =>
    if h : k = k' then by
      subst h
      exact if h' : Γ = Γ' ∧ φ = φ' then .isTrue (by rw [h'.1, h'.2])
        else .isFalse fun e => h' (by cases e; exact ⟨rfl, rfl⟩)
    else .isFalse fun e => h (by cases e; rfl)

/-- **Validity in a structure**: every assignment satisfying the hypotheses satisfies the
conclusion. -/
def Seq.ValidIn (M : Structure Sg) (s : Seq Sg) : Prop :=
  ∀ η : Fin s.k → M.carrier, (∀ ψ ∈ s.ctx, ψ.Holds M η) → s.goal.Holds M η

variable (Sg) in
/-- **Rule instances** at `k` variables. -/
inductive Rule : ℕ → Type where
  | hyp {k : ℕ} (Γ : List (Formula Sg k)) (φ : Formula Sg k) : Rule k
  | weaken {k : ℕ} (Γ Δ : List (Formula Sg k)) (φ : Formula Sg k) : Rule k
  | ttIntro {k : ℕ} (Γ : List (Formula Sg k)) : Rule k
  | notIntro {k : ℕ} (Γ : List (Formula Sg k)) (φ ψ : Formula Sg k) : Rule k
  | notElim {k : ℕ} (Γ : List (Formula Sg k)) (φ ψ : Formula Sg k) : Rule k
  | dne {k : ℕ} (Γ : List (Formula Sg k)) (φ : Formula Sg k) : Rule k
  | andIntro {k : ℕ} (Γ : List (Formula Sg k)) (φ ψ : Formula Sg k) : Rule k
  | andLeft {k : ℕ} (Γ : List (Formula Sg k)) (φ ψ : Formula Sg k) : Rule k
  | andRight {k : ℕ} (Γ : List (Formula Sg k)) (φ ψ : Formula Sg k) : Rule k
  | allIntro {k : ℕ} (Γ : List (Formula Sg k)) (φ : Formula Sg (k + 1)) : Rule k
  | allElim {k : ℕ} (Γ : List (Formula Sg k)) (φ : Formula Sg (k + 1)) (t : Term Sg k) : Rule k
  | eqRefl {k : ℕ} (Γ : List (Formula Sg k)) (t : Term Sg k) : Rule k
  | eqElim {k : ℕ} (Γ : List (Formula Sg k)) (φ : Formula Sg (k + 1)) (s t : Term Sg k) : Rule k

namespace Rule

variable {k : ℕ}

/-- The premises of a rule instance, in order. -/
def prems : Rule Sg k → List (Seq Sg)
  | hyp .. | ttIntro .. | eqRefl .. => []
  | weaken Γ _ φ => [⟨k, Γ, φ⟩]
  | notIntro Γ φ ψ => [⟨k, φ :: Γ, ψ⟩, ⟨k, φ :: Γ, .not ψ⟩]
  | notElim Γ φ _ => [⟨k, Γ, φ⟩, ⟨k, Γ, .not φ⟩]
  | dne Γ φ => [⟨k, Γ, .not (.not φ)⟩]
  | andIntro Γ φ ψ => [⟨k, Γ, φ⟩, ⟨k, Γ, ψ⟩]
  | andLeft Γ φ ψ | andRight Γ φ ψ => [⟨k, Γ, .and φ ψ⟩]
  | allIntro Γ φ => [⟨k + 1, Γ.map Formula.shift, φ⟩]
  | allElim Γ φ _ => [⟨k, Γ, .all φ⟩]
  | eqElim Γ φ s t => [⟨k, Γ, .eq s t⟩, ⟨k, Γ, φ.inst s⟩]

/-- The conclusion of a rule instance. -/
def concl : Rule Sg k → Seq Sg
  | hyp Γ φ | dne Γ φ => ⟨k, Γ, φ⟩
  | weaken _ Δ φ => ⟨k, Δ, φ⟩
  | ttIntro Γ => ⟨k, Γ, .tt⟩
  | notIntro Γ φ _ => ⟨k, Γ, .not φ⟩
  | notElim Γ _ ψ => ⟨k, Γ, ψ⟩
  | andIntro Γ φ ψ => ⟨k, Γ, .and φ ψ⟩
  | andLeft Γ φ _ => ⟨k, Γ, φ⟩
  | andRight Γ _ ψ => ⟨k, Γ, ψ⟩
  | allIntro Γ φ => ⟨k, Γ, .all φ⟩
  | allElim Γ φ t => ⟨k, Γ, φ.inst t⟩
  | eqRefl Γ t => ⟨k, Γ, .eq t t⟩
  | eqElim Γ φ _ t => ⟨k, Γ, φ.inst t⟩

/-- The side conditions: a hypothesis is in the context, and weakening is along `⊆`. -/
def side [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)] : Rule Sg k → Bool
  | hyp Γ φ => decide (φ ∈ Γ)
  | weaken Γ Δ _ => decide (∀ φ ∈ Γ, φ ∈ Δ)
  | _ => true

end Rule

variable [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)]

variable (Sg) in
/-- **The derivation system** of first-order natural deduction over `Sg`. -/
def system : DerivationSystem (Seq Sg) where
  Rule := Σ k, Rule Sg k
  Instance r ps c := r.2.side = true ∧ r.2.prems = ps ∧ r.2.concl = c

instance : ∀ r ps c, Decidable ((system Sg).Instance r ps c) :=
  fun r ps c => inferInstanceAs (Decidable (r.2.side = true ∧ r.2.prems = ps ∧ r.2.concl = c))

variable (Sg) in
/-- **Derivability by checked proof trees** of sentences from sentences. -/
def treeDerives : System (List (Sentence Sg)) (Sentence Sg) :=
  fun Γ φ => (system Sg).derives [] ⟨0, Γ, φ⟩

end Silmaril.Consequence.FirstOrder.ND
