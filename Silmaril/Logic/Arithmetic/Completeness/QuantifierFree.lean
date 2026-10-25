module

public import Silmaril.Logic.Arithmetic.Completeness.Numerals

/-!
# Closed quantifier-free completeness for Robinson Q

`reflect` is an executable proof constructor for the existing scoped syntax.
It returns a Q derivation of the input formula or its formal negation. The
semantic completeness theorem follows from these constructed derivations and
the independently proved soundness theorem; soundness is not a completeness
assumption or an extra inference rule.
-/

@[expose] public section

namespace Silmaril.Logic.Arithmetic.Completeness

/-- Grammar evidence for the quantifier-free fragment of the existing syntax. -/
inductive QuantifierFree : {n : ℕ} → Formula n → Type where
  | bot {n : ℕ} : QuantifierFree (Formula.bot : Formula n)
  | equal {n : ℕ} (s t : Term n) : QuantifierFree (.equal s t)
  | imp {n : ℕ} {φ ψ : Formula n} :
      QuantifierFree φ → QuantifierFree ψ → QuantifierFree (.imp φ ψ)
  | conj {n : ℕ} {φ ψ : Formula n} :
      QuantifierFree φ → QuantifierFree ψ → QuantifierFree (.conj φ ψ)
  | disj {n : ℕ} {φ ψ : Formula n} :
      QuantifierFree φ → QuantifierFree ψ → QuantifierFree (.disj φ ψ)

variable {n m : ℕ} {Γ : Context n} {φ : Formula n}

/-- Capture-avoiding substitution preserves this actual syntax fragment. -/
def QuantifierFree.subst {φ : Formula n} (q : QuantifierFree φ) (σ : Fin n → Term m) :
    QuantifierFree (φ.subst σ) :=
  match q with
  | .bot => .bot
  | .equal s t => .equal (s.subst σ) (t.subst σ)
  | .imp p q => .imp (p.subst σ) (q.subst σ)
  | .conj p q => .conj (p.subst σ) (q.subst σ)
  | .disj p q => .disj (p.subst σ) (q.subst σ)

/-- Add one hypothesis without changing the represented derivation's conclusion. -/
def under (d : QProof Γ φ) (ψ : Formula n) : QProof (ψ :: Γ) φ :=
  .weaken (fun _ h => List.mem_cons_of_mem _ h) d

/-- Compute proof data for either polarity of any closed quantifier-free formula. -/
def reflect {Γ : Context 0} {φ : Sentence} (q : QuantifierFree φ) :
    QProof Γ φ ⊕ QProof Γ φ.neg :=
  match q with
  | .bot => .inr (.impIntro (.hyp (by simp)))
  | .equal s t =>
      if h : s.eval Fin.elim0 = t.eval Fin.elim0 then .inl (proveEqual s t h)
      else .inr (refuteEqual s t h)
  | .imp (φ := φ) (ψ := ψ) qφ qψ =>
      match reflect qφ, reflect qψ with
      | .inr dφ, _ => .inl (.impIntro
          (.botElim (.impElim (under dφ φ) (.hyp (by simp)))))
      | .inl _, .inl dψ => .inl (.impIntro (under dψ φ))
      | .inl dφ, .inr dψ => .inr (.impIntro
          (.impElim (under dψ (.imp φ ψ))
            (.impElim (.hyp (by simp)) (under dφ (.imp φ ψ)))))
  | .conj (φ := φ) (ψ := ψ) qφ qψ =>
      match reflect qφ, reflect qψ with
      | .inl dφ, .inl dψ => .inl (.conjIntro dφ dψ)
      | .inr dφ, _ => .inr (.impIntro
          (.impElim (under dφ (.conj φ ψ))
            (.conjLeft (ψ := ψ) (.hyp (by simp)))))
      | .inl _, .inr dψ => .inr (.impIntro
          (.impElim (under dψ (.conj φ ψ))
            (.conjRight (φ := φ) (.hyp (by simp)))))
  | .disj (φ := φ) (ψ := ψ) qφ qψ =>
      match reflect qφ, reflect qψ with
      | .inl dφ, _ => .inl (.disjLeft dφ)
      | .inr _, .inl dψ => .inl (.disjRight dψ)
      | .inr dφ, .inr dψ => .inr (.impIntro
          (.disjElim (.hyp (by simp))
            (.impElim (under (under dφ (.disj φ ψ)) φ) (.hyp (by simp)))
            (.impElim (under (under dψ (.disj φ ψ)) ψ) (.hyp (by simp)))))

/-- Truth supplies the positive branch of the explicitly constructed proof sum. -/
def proveQuantifierFree {φ : Sentence} (q : QuantifierFree φ)
    (h : φ.eval Fin.elim0) : QProof [] φ :=
  match reflect (Γ := []) q with
  | .inl d => d
  | .inr d => (qSound d Fin.elim0 (by simp [Satisfies]) h).elim

/-- Falsehood supplies a proof of the same formula's actual formal negation. -/
def refuteQuantifierFree {φ : Sentence} (q : QuantifierFree φ)
    (h : ¬ φ.eval Fin.elim0) : QProof [] φ.neg :=
  match reflect (Γ := []) q with
  | .inl d => (h (qSound d Fin.elim0 (by simp [Satisfies]))).elim
  | .inr d => d

/-- Q's actual proof family agrees with standard truth on this closed fragment. -/
theorem quantifierFree_complete {φ : Sentence} (q : QuantifierFree φ) :
    Nonempty (QProof [] φ) ↔ φ.eval Fin.elim0 :=
  ⟨fun ⟨d⟩ => qSound d Fin.elim0 (by simp [Satisfies]),
    fun h => ⟨proveQuantifierFree q h⟩⟩

theorem eval_numeral (k : ℕ) (e : Assignment n) : (Term.numeral k).eval e = k := by
  induction k <;> simp_all [Term.eval]

/-- A concrete existential witness yields an actual Q proof of its closure. -/
def proveExistentialWitness (φ : Formula 1) (q : QuantifierFree φ) (k : ℕ)
    (h : φ.eval (extend Fin.elim0 k)) : QProof [] (.ex φ) := by
  apply Derivation.exIntro (Term.numeral k)
  apply proveQuantifierFree (q.subst (Fin.cases (Term.numeral k) Term.var))
  exact (Formula.eval_inst φ _ Fin.elim0).mpr (by simpa only [eval_numeral] using h)

/-- The first existential fragment follows from witness-based proof reconstruction. -/
theorem existentialQuantifierFree_complete (φ : Formula 1) (q : QuantifierFree φ) :
    Nonempty (QProof [] (.ex φ)) ↔ ∃ k, φ.eval (extend Fin.elim0 k) := by
  constructor
  · rintro ⟨d⟩
    exact qSound d Fin.elim0 (by simp [Satisfies])
  · rintro ⟨k, h⟩
    exact ⟨proveExistentialWitness φ q k h⟩

end Silmaril.Logic.Arithmetic.Completeness
