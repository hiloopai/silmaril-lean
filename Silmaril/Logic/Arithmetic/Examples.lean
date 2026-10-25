module

public import Silmaril.Logic.Arithmetic.Peano

@[expose] public section

/-! Concrete proof trees exercise recursion equations, equality elimination,
and induction. -/
namespace Silmaril.Logic.Arithmetic

/-- Q proves 1 + 1 = 2 using addition recursion and equality substitution. -/
def qOneAddOne : QProof []
    (.equal (.add (.succ .zero) (.succ .zero)) (.succ (.succ .zero)) : Sentence) := by
  apply Derivation.eqElim
    (.equal (.add (.succ .zero) (.succ .zero)) (.succ (.var 0)))
    (.ax (.basic (.addZero (.succ .zero))))
  exact .ax (.basic (.addSucc (.succ .zero) .zero))

/-- PA proves left addition by zero is the identity; Q only has right-zero
addition as an axiom, so this proof uses the full induction rule. -/
def paLeftZeroAdd (n : ℕ) : PAProof []
    (.all (.equal (.add .zero (.var 0)) (.var 0)) : Formula n) := by
  apply Derivation.impElim
    (.ax (.induction (.equal (.add .zero (.var 0)) (.var 0))))
  apply Derivation.conjIntro
  · exact .ax (.basic (.addZero .zero))
  · apply Derivation.allIntro
    apply Derivation.impIntro
    apply Derivation.eqElim (s := .add .zero (.var 0)) (t := .var 0)
      (.equal (.add .zero (.succ (.var 1))) (.succ (.var 0)))
      (.hyp (by simp))
    exact .ax (.basic (.addSucc .zero (.var 0)))

/-- Closed-sentence soundness has no assignment or context obligations. -/
theorem qSentenceSound {φ : Sentence} (d : QProof [] φ) : φ.eval Fin.elim0 :=
  qSound d Fin.elim0 (by simp [Satisfies])

theorem paSentenceSound {φ : Sentence} (d : PAProof [] φ) : φ.eval Fin.elim0 :=
  paSound d Fin.elim0 (by simp [Satisfies])

end Silmaril.Logic.Arithmetic
