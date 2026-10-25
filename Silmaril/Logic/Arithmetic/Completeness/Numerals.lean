module

public import Silmaril.Logic.Arithmetic.Robinson

/-!
# Proof-producing arithmetic evaluation in Robinson Q

These functions construct the existing Q derivation trees. Recursion takes place
in Lean over concrete terms and numeral values; no induction schema is added to Q.
-/

@[expose] public section

namespace Silmaril.Logic.Arithmetic.Completeness

variable {n : ℕ} {Γ : Context n}

theorem subst_shift (t u : Term n) :
    t.shift.subst (Fin.cases u Term.var) = t := by
  induction t <;> simp_all [Term.shift, Term.rename, Term.subst]

/-- Symmetry is constructed from the existing equality elimination rule. -/
def eqSymm {s t : Term n} (d : QProof Γ (.equal s t)) : QProof Γ (.equal t s) := by
  have h : QProof Γ ((Formula.equal (.var 0) s.shift).inst s) := by
    simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
      (Derivation.eqRefl s : QProof Γ _)
  simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
    (Derivation.eqElim (.equal (.var 0) s.shift) d h)

/-- Transitivity, with both input derivations retained. -/
def eqTrans {r s t : Term n} (d : QProof Γ (.equal r s))
    (e : QProof Γ (.equal s t)) : QProof Γ (.equal r t) := by
  have h : QProof Γ ((Formula.equal r.shift (.var 0)).inst s) := by
    simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using d
  simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
    (Derivation.eqElim (.equal r.shift (.var 0)) e h)

def succCongr {s t : Term n} (d : QProof Γ (.equal s t)) :
    QProof Γ (.equal (.succ s) (.succ t)) := by
  have h : QProof Γ ((Formula.equal (.succ s.shift) (.succ (.var 0))).inst s) := by
    simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
      (Derivation.eqRefl (.succ s) : QProof Γ _)
  simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
    (Derivation.eqElim (.equal (.succ s.shift) (.succ (.var 0))) d h)

def addCongrLeft {s t : Term n} (d : QProof Γ (.equal s t)) (u : Term n) :
    QProof Γ (.equal (.add s u) (.add t u)) := by
  have h : QProof Γ ((Formula.equal (.add s.shift u.shift) (.add (.var 0) u.shift)).inst s) := by
    simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
      (Derivation.eqRefl (.add s u) : QProof Γ _)
  simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
    (Derivation.eqElim (.equal (.add s.shift u.shift) (.add (.var 0) u.shift)) d h)

def addCongrRight (u : Term n) {s t : Term n} (d : QProof Γ (.equal s t)) :
    QProof Γ (.equal (.add u s) (.add u t)) := by
  have h : QProof Γ ((Formula.equal (.add u.shift s.shift) (.add u.shift (.var 0))).inst s) := by
    simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
      (Derivation.eqRefl (.add u s) : QProof Γ _)
  simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
    (Derivation.eqElim (.equal (.add u.shift s.shift) (.add u.shift (.var 0))) d h)

def mulCongrLeft {s t : Term n} (d : QProof Γ (.equal s t)) (u : Term n) :
    QProof Γ (.equal (.mul s u) (.mul t u)) := by
  have h : QProof Γ ((Formula.equal (.mul s.shift u.shift) (.mul (.var 0) u.shift)).inst s) := by
    simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
      (Derivation.eqRefl (.mul s u) : QProof Γ _)
  simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
    (Derivation.eqElim (.equal (.mul s.shift u.shift) (.mul (.var 0) u.shift)) d h)

def mulCongrRight (u : Term n) {s t : Term n} (d : QProof Γ (.equal s t)) :
    QProof Γ (.equal (.mul u s) (.mul u t)) := by
  have h : QProof Γ ((Formula.equal (.mul u.shift s.shift) (.mul u.shift (.var 0))).inst s) := by
    simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
      (Derivation.eqRefl (.mul u s) : QProof Γ _)
  simpa only [Formula.inst, Formula.subst, Term.subst, Fin.cases_zero, subst_shift] using
    (Derivation.eqElim (.equal (.mul u.shift s.shift) (.mul u.shift (.var 0))) d h)

/-- Every concrete addition of numerals has an actual Q derivation. -/
def numeralAdd (a : ℕ) : (b : ℕ) →
    QProof Γ (.equal (.add (.numeral a) (.numeral b)) (.numeral (a + b)))
  | 0 => .ax (.basic (.addZero (.numeral a)))
  | b + 1 => eqTrans (.ax (.basic (.addSucc (.numeral a) (.numeral b))))
      (succCongr (numeralAdd a b))

/-- Every concrete multiplication of numerals has an actual Q derivation. -/
def numeralMul (a : ℕ) : (b : ℕ) →
    QProof Γ (.equal (.mul (.numeral a) (.numeral b)) (.numeral (a * b)))
  | 0 => .ax (.basic (.mulZero (.numeral a)))
  | b + 1 => eqTrans (.ax (.basic (.mulSucc (.numeral a) (.numeral b))))
      (eqTrans (addCongrLeft (numeralMul a b) (.numeral a)) (numeralAdd (a * b) a))

/-- Normalization constructs proof data for arbitrary closed arithmetic terms. -/
def normalize {Γ : Context 0} : (t : Term 0) →
    QProof Γ (.equal t (.numeral (t.eval Fin.elim0)))
  | .var i => Fin.elim0 i
  | .zero => .eqRefl .zero
  | .succ t => succCongr (normalize t)
  | .add s t => eqTrans (addCongrLeft (normalize s) t)
      (eqTrans (addCongrRight (.numeral (s.eval Fin.elim0)) (normalize t))
        (numeralAdd (s.eval Fin.elim0) (t.eval Fin.elim0)))
  | .mul s t => eqTrans (mulCongrLeft (normalize s) t)
      (eqTrans (mulCongrRight (.numeral (s.eval Fin.elim0)) (normalize t))
        (numeralMul (s.eval Fin.elim0) (t.eval Fin.elim0)))

/-- Distinct natural numerals are refutable using only Q's successor axioms. -/
def numeralNe : (a b : ℕ) → a ≠ b → (Δ : Context n) →
    QProof Δ (Formula.equal (.numeral a) (.numeral b)).neg
  | 0, 0, h, _ => (h rfl).elim
  | 0, b + 1, _, _ => .impIntro (.impElim
      (.ax (.basic (.succNonzero (.numeral b)))) (eqSymm (.hyp (by simp))))
  | a + 1, 0, _, _ => .ax (.basic (.succNonzero (.numeral a)))
  | a + 1, b + 1, h, Δ => .impIntro (.impElim
      (numeralNe a b (fun heq => h (congrArg Nat.succ heq))
        (Formula.equal (.numeral (a + 1)) (.numeral (b + 1)) :: Δ))
      (.impElim (.ax (.basic (.succInjective (.numeral a) (.numeral b))))
        (.hyp (by simp))))

/-- Closed true equalities are turned into Q proof trees, rather than merely checked. -/
def proveEqual {Γ : Context 0} (s t : Term 0)
    (h : s.eval Fin.elim0 = t.eval Fin.elim0) : QProof Γ (.equal s t) := by
  have d : QProof Γ (.equal s (.numeral (t.eval Fin.elim0))) := by
    simpa only [h] using (normalize s : QProof Γ _)
  exact eqTrans d (eqSymm (normalize t))

/-- Closed false equalities similarly produce derivations of formal negation. -/
def refuteEqual {Γ : Context 0} (s t : Term 0)
    (h : s.eval Fin.elim0 ≠ t.eval Fin.elim0) : QProof Γ (Formula.equal s t).neg := by
  apply Derivation.impIntro
  have ds := normalize (Γ := .equal s t :: Γ) s
  have dt := normalize (Γ := .equal s t :: Γ) t
  have de : QProof (.equal s t :: Γ)
      (.equal (.numeral (s.eval Fin.elim0)) (.numeral (t.eval Fin.elim0))) :=
    eqTrans (eqSymm ds) (eqTrans (.hyp (by simp)) dt)
  exact .impElim (numeralNe _ _ h _) de

end Silmaril.Logic.Arithmetic.Completeness
