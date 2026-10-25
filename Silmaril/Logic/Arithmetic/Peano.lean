module

public import Silmaril.Logic.Arithmetic.Robinson

@[expose] public section

namespace Silmaril.Logic.Arithmetic

variable {n m : ℕ} {φ : Formula n} {Γ : Context n}

/-- Induction for an arbitrary formula in one induction variable and n parameters.
The step instance substitutes Sx without disturbing any parameter. -/
def inductionSchema (φ : Formula (n + 1)) : Formula n :=
  .imp (.conj (φ.inst .zero)
    (.all (.imp φ φ.step))) (.all φ)

inductive PAAxiom : {n : ℕ} → Formula n → Type where
  | basic {n : ℕ} {φ : Formula n} : BasicAxiom φ → PAAxiom φ
  | induction {n : ℕ} (φ : Formula (n + 1)) : PAAxiom (inductionSchema φ)

abbrev PAProof {n : ℕ} (Γ : Context n) (φ : Formula n) := Derivation PAAxiom Γ φ

theorem paAxiomSound (h : PAAxiom φ) : Valid φ := by
  cases h with
  | basic h => exact h.sound
  | induction φ =>
    intro e h x
    induction x with
    | zero => exact (Formula.eval_inst φ .zero e).1 h.1
    | succ x ih =>
      have hs := h.2 x ih
      exact (Formula.eval_step φ e x).1 hs

theorem paSound (d : PAProof Γ φ) (e : Assignment n) (hΓ : Satisfies e Γ) : φ.eval e :=
  d.sound (fun h => paAxiomSound h) e hΓ

/-- Every number is zero or a successor; derived from induction rather than
included as an additional PA axiom. -/
def zeroOrSuccessorBody (n : ℕ) : Formula (n + 1) :=
  .disj (.equal (.var 0) .zero) (.ex (.equal (.var 1) (.succ (.var 0))))

def paZeroOrSuccessor (n : ℕ) : PAProof [] (.all (zeroOrSuccessorBody n)) := by
  apply Derivation.impElim (.ax (.induction (zeroOrSuccessorBody n)))
  apply Derivation.conjIntro
  · change PAProof [] (.disj (.equal .zero .zero) _)
    exact .disjLeft (.eqRefl .zero)
  · apply Derivation.allIntro
    apply Derivation.impIntro
    change PAProof _ (.disj _ (.ex (.equal (.succ (.var 1)) (.succ (.var 0)))))
    apply Derivation.disjRight
    apply Derivation.exIntro (.var 0)
    exact .eqRefl (.succ (.var 0))

/-- The seventh Q axiom is a theorem of PA for every term instance. -/
def paPredecessor (t : Term n) : PAProof [] (predecessor t) := by
  apply Derivation.impIntro
  have casesProof : PAProof [(Formula.equal t .zero).neg]
      (.disj (.equal t .zero) (.ex (.equal t.shift (.succ (.var 0))))) := by
    exact .weaken (by simp) (.allElim (paZeroOrSuccessor n) t)
  apply Derivation.disjElim casesProof
  · apply Derivation.botElim
    exact .impElim (φ := .equal t .zero) (.hyp (by simp)) (.hyp (by simp))
  · exact .hyp (by simp)

/-- Proof-preserving inclusion of Q into PA; logical constructors are retained
and the predecessor axiom is replaced by the induction proof above. -/
def qToPA {n : ℕ} {Γ : Context n} {φ : Formula n} (d : QProof Γ φ) : PAProof Γ φ :=
  d.map fun h => match h with
    | .basic b => .ax (.basic b)
    | .pred t => paPredecessor t

def paZeroAddZero : PAProof [] (.equal (.add .zero .zero) .zero : Sentence) :=
  qToPA qZeroAddZero

end Silmaril.Logic.Arithmetic
