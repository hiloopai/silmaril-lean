module

public import Silmaril.Logic.Consequence.Derivation.Defs
public import Silmaril.Logic.Consequence.Arithmetic.Defs

/-!
# Peano and Robinson arithmetic as derivation systems

The natural deduction of `Silmaril.Logic.Arithmetic.Derivation`, with each rule *instance* a
checkable label, so that proofs are explicit data that a checker validates.

**Judgments** (`Seq`): `Γ ⊢ φ` with `n` de Bruijn variables in scope.

**Axioms** (`AxiomCode n`): an axiom instance and its data:
* the six recursion and successor axioms of Q and PA (`BasicAxiom`);
* Q's predecessor axiom `pred t`, for Q only;
* the induction schema `induction φ`, for PA only.

**Rules** (`Rule n`, at `n` variables): every constructor of `Derivation`, carrying its context
and formulas, so that each label determines its premises (`Rule.prems`) and conclusion
(`Rule.concl`). Two rules have side conditions (`Rule.side`): `hyp` needs `φ ∈ Γ`, `weaken` needs
`Γ ⊆ Δ`. An axiom must belong to the theory.

| rule | premises | conclusion |
|---|---|---|
| `hyp Γ φ` | — | `Γ ⊢ φ` (`φ ∈ Γ`) |
| `ax Γ a` | — | `Γ ⊢ a.formula` |
| `weaken Γ Δ ψ` | `Γ ⊢ ψ` | `Δ ⊢ ψ` (`Γ ⊆ Δ`) |
| `impIntro Γ φ ψ` | `φ :: Γ ⊢ ψ` | `Γ ⊢ φ → ψ` |
| `impElim Γ φ ψ` | `Γ ⊢ φ → ψ`, `Γ ⊢ φ` | `Γ ⊢ ψ` |
| `botElim Γ φ` | `Γ ⊢ ⊥` | `Γ ⊢ φ` |
| `classical Γ φ` | `Γ ⊢ ¬¬φ` | `Γ ⊢ φ` |
| `conjIntro`, `conjLeft`, `conjRight` | as usual | |
| `disjLeft`, `disjRight`, `disjElim Γ φ ψ χ` | as usual; `disjElim` discharges `φ`, `ψ` | |
| `allIntro Γ φ` | `Γ↑ ⊢ φ` (at `n + 1`) | `Γ ⊢ ∀ φ` |
| `allElim Γ φ t` | `Γ ⊢ ∀ φ` | `Γ ⊢ φ[t]` |
| `exIntro Γ φ t` | `Γ ⊢ φ[t]` | `Γ ⊢ ∃ φ` |
| `exElim Γ φ ψ` | `Γ ⊢ ∃ φ`, `φ :: Γ↑ ⊢ ψ↑` (at `n + 1`) | `Γ ⊢ ψ` |
| `eqRefl Γ t` | — | `Γ ⊢ t = t` |
| `eqElim Γ φ s t` | `Γ ⊢ s = t`, `Γ ⊢ φ[s]` | `Γ ⊢ φ[t]` |

`system T` is the derivation system of the theory `T` (`.q` or `.pa`), with decidable instances.
`treeDerives T Γ φ` holds when a valid proof tree from no assumptions concludes `Γ ⊢ φ` with no
free variables; `Thms` proves it **equals** `qDerives` and `paDerives`.

**Validity in ℕ** (`Seq.Valid`): every assignment satisfying `Γ` satisfies `φ`. The rules are
locally sound for it (`Thms`).
-/

@[expose] public section

namespace Silmaril.Consequence.Arithmetic.ND

open Silmaril.Logic.Arithmetic

/-- A natural-deduction judgment `Γ ⊢ φ` with `n` variables in scope. -/
structure Seq where
  /-- The number of variables in scope. -/
  n : ℕ
  /-- The hypotheses. -/
  ctx : Context n
  /-- The conclusion. -/
  goal : Formula n
  deriving DecidableEq, Repr

/-- The theories: Robinson's Q and Peano arithmetic. -/
inductive Theory where
  | q
  | pa
  deriving DecidableEq, Repr

/-- The axioms of a theory, as in `Silmaril.Logic.Arithmetic`. -/
def Theory.Ax : Theory → {n : ℕ} → Formula n → Type
  | .q => QAxiom
  | .pa => PAAxiom

/-- **Derivability of a judgment** in `Derivation`: the reference the derivation system is
checked against. -/
def Seq.Derivable (T : Theory) (s : Seq) : Prop := Nonempty (Derivation T.Ax s.ctx s.goal)

/-- **Validity in ℕ**: every assignment satisfying the hypotheses satisfies the conclusion. -/
def Seq.Valid (s : Seq) : Prop := ∀ e : Assignment s.n, Satisfies e s.ctx → s.goal.eval e

/-- Axiom instances with their data. -/
inductive AxiomCode : ℕ → Type where
  | succNonzero {n : ℕ} (t : Term n) : AxiomCode n
  | succInjective {n : ℕ} (s t : Term n) : AxiomCode n
  | addZero {n : ℕ} (t : Term n) : AxiomCode n
  | addSucc {n : ℕ} (s t : Term n) : AxiomCode n
  | mulZero {n : ℕ} (t : Term n) : AxiomCode n
  | mulSucc {n : ℕ} (s t : Term n) : AxiomCode n
  /-- Q's predecessor axiom. -/
  | pred {n : ℕ} (t : Term n) : AxiomCode n
  /-- PA's induction schema. -/
  | induction {n : ℕ} (φ : Formula (n + 1)) : AxiomCode n
  deriving DecidableEq, Repr

namespace AxiomCode

variable {n : ℕ}

/-- The axiom an axiom code names. -/
def formula : AxiomCode n → Formula n
  | succNonzero t => (Formula.equal (.succ t) .zero).neg
  | succInjective s t => .imp (.equal (.succ s) (.succ t)) (.equal s t)
  | addZero t => .equal (.add t .zero) t
  | addSucc s t => .equal (.add s (.succ t)) (.succ (.add s t))
  | mulZero t => .equal (.mul t .zero) .zero
  | mulSucc s t => .equal (.mul s (.succ t)) (.add (.mul s t) s)
  | pred t => predecessor t
  | induction φ => inductionSchema φ

/-- Whether the axiom belongs to the theory: the basic axioms to both, `pred` to Q, `induction`
to PA. -/
def inTheory : Theory → AxiomCode n → Bool
  | .q, induction _ => false
  | .pa, pred _ => false
  | _, _ => true

end AxiomCode

/-- **Rule instances** at `n` variables, carrying their contexts and formulas. -/
inductive Rule : ℕ → Type where
  | hyp {n : ℕ} (Γ : Context n) (φ : Formula n) : Rule n
  | ax {n : ℕ} (Γ : Context n) (a : AxiomCode n) : Rule n
  | weaken {n : ℕ} (Γ Δ : Context n) (ψ : Formula n) : Rule n
  | impIntro {n : ℕ} (Γ : Context n) (φ ψ : Formula n) : Rule n
  | impElim {n : ℕ} (Γ : Context n) (φ ψ : Formula n) : Rule n
  | botElim {n : ℕ} (Γ : Context n) (φ : Formula n) : Rule n
  | classical {n : ℕ} (Γ : Context n) (φ : Formula n) : Rule n
  | conjIntro {n : ℕ} (Γ : Context n) (φ ψ : Formula n) : Rule n
  | conjLeft {n : ℕ} (Γ : Context n) (φ ψ : Formula n) : Rule n
  | conjRight {n : ℕ} (Γ : Context n) (φ ψ : Formula n) : Rule n
  | disjLeft {n : ℕ} (Γ : Context n) (φ ψ : Formula n) : Rule n
  | disjRight {n : ℕ} (Γ : Context n) (φ ψ : Formula n) : Rule n
  | disjElim {n : ℕ} (Γ : Context n) (φ ψ χ : Formula n) : Rule n
  | allIntro {n : ℕ} (Γ : Context n) (φ : Formula (n + 1)) : Rule n
  | allElim {n : ℕ} (Γ : Context n) (φ : Formula (n + 1)) (t : Term n) : Rule n
  | exIntro {n : ℕ} (Γ : Context n) (φ : Formula (n + 1)) (t : Term n) : Rule n
  | exElim {n : ℕ} (Γ : Context n) (φ : Formula (n + 1)) (ψ : Formula n) : Rule n
  | eqRefl {n : ℕ} (Γ : Context n) (t : Term n) : Rule n
  | eqElim {n : ℕ} (Γ : Context n) (φ : Formula (n + 1)) (s t : Term n) : Rule n
  deriving DecidableEq, Repr

namespace Rule

variable {n : ℕ}

/-- The premises of a rule instance, in order. -/
def prems : Rule n → List Seq
  | hyp .. | ax .. | eqRefl .. => []
  | weaken Γ _ ψ => [⟨n, Γ, ψ⟩]
  | impIntro Γ φ ψ => [⟨n, φ :: Γ, ψ⟩]
  | impElim Γ φ ψ => [⟨n, Γ, .imp φ ψ⟩, ⟨n, Γ, φ⟩]
  | botElim Γ _ => [⟨n, Γ, .bot⟩]
  | classical Γ φ => [⟨n, Γ, φ.neg.neg⟩]
  | conjIntro Γ φ ψ => [⟨n, Γ, φ⟩, ⟨n, Γ, ψ⟩]
  | conjLeft Γ φ ψ | conjRight Γ φ ψ => [⟨n, Γ, .conj φ ψ⟩]
  | disjLeft Γ φ _ => [⟨n, Γ, φ⟩]
  | disjRight Γ _ ψ => [⟨n, Γ, ψ⟩]
  | disjElim Γ φ ψ χ => [⟨n, Γ, .disj φ ψ⟩, ⟨n, φ :: Γ, χ⟩, ⟨n, ψ :: Γ, χ⟩]
  | allIntro Γ φ => [⟨n + 1, Γ.map Formula.shift, φ⟩]
  | allElim Γ φ _ => [⟨n, Γ, .all φ⟩]
  | exIntro Γ φ t => [⟨n, Γ, φ.inst t⟩]
  | exElim Γ φ ψ => [⟨n, Γ, .ex φ⟩, ⟨n + 1, φ :: Γ.map Formula.shift, ψ.shift⟩]
  | eqElim Γ φ s t => [⟨n, Γ, .equal s t⟩, ⟨n, Γ, φ.inst s⟩]

/-- The conclusion of a rule instance. -/
def concl : Rule n → Seq
  | hyp Γ φ | botElim Γ φ | classical Γ φ => ⟨n, Γ, φ⟩
  | ax Γ a => ⟨n, Γ, a.formula⟩
  | weaken _ Δ ψ => ⟨n, Δ, ψ⟩
  | impIntro Γ φ ψ => ⟨n, Γ, .imp φ ψ⟩
  | impElim Γ _ ψ => ⟨n, Γ, ψ⟩
  | conjIntro Γ φ ψ => ⟨n, Γ, .conj φ ψ⟩
  | conjLeft Γ φ _ => ⟨n, Γ, φ⟩
  | conjRight Γ _ ψ => ⟨n, Γ, ψ⟩
  | disjLeft Γ φ ψ | disjRight Γ φ ψ => ⟨n, Γ, .disj φ ψ⟩
  | disjElim Γ _ _ χ => ⟨n, Γ, χ⟩
  | allIntro Γ φ => ⟨n, Γ, .all φ⟩
  | allElim Γ φ t => ⟨n, Γ, φ.inst t⟩
  | exIntro Γ φ _ => ⟨n, Γ, .ex φ⟩
  | exElim Γ _ ψ => ⟨n, Γ, ψ⟩
  | eqRefl Γ t => ⟨n, Γ, .equal t t⟩
  | eqElim Γ φ _ t => ⟨n, Γ, φ.inst t⟩

/-- The side conditions: a hypothesis is in the context, weakening is along `⊆`, an axiom belongs
to the theory. -/
def side (T : Theory) : Rule n → Bool
  | hyp Γ φ => decide (φ ∈ Γ)
  | weaken Γ Δ _ => decide (∀ φ ∈ Γ, φ ∈ Δ)
  | ax _ a => a.inTheory T
  | _ => true

end Rule

/-- **The derivation system of `T`**: a label is a rule instance at some number of variables; it
applies when its side condition holds, and its premises and conclusion are the given ones. -/
def system (T : Theory) : DerivationSystem Seq where
  Rule := Σ n, Rule n
  Instance r ps c := r.2.side T = true ∧ r.2.prems = ps ∧ r.2.concl = c

instance (T : Theory) : ∀ r ps c, Decidable ((system T).Instance r ps c) :=
  fun r ps c => inferInstanceAs (Decidable (r.2.side T = true ∧ r.2.prems = ps ∧ r.2.concl = c))

/-- **Derivability by checked proof trees**: a valid tree from no assumptions concludes `Γ ⊢ φ`
with no free variables. -/
def treeDerives (T : Theory) : System (List Sentence) Sentence :=
  fun Γ φ => (system T).derives [] ⟨0, Γ, φ⟩

end Silmaril.Consequence.Arithmetic.ND
