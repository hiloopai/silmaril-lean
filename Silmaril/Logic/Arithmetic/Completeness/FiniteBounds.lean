module

public import Silmaril.Logic.Arithmetic.Completeness.QuantifierFree

/-!
# Finite numeral bounds in Robinson Q

The bound is represented by ordinary arithmetic syntax, not an enumerated
semantic predicate. Q's predecessor axiom and addition equations prove that a
term bounded by a concrete numeral equals one of the finitely many numerals.
-/

@[expose] public section

namespace Silmaril.Logic.Arithmetic.Completeness

variable {n m : ℕ} {Γ : Context n}

def excludedMiddle (φ : Formula n) : QProof Γ (.disj φ φ.neg) := by
  apply Derivation.classical
  apply Derivation.impIntro
  have hn : QProof ((Formula.disj φ φ.neg).neg :: Γ) φ.neg := by
    apply Derivation.impIntro
    exact .impElim (φ := .disj φ φ.neg) (.hyp (by simp))
      (.disjLeft (ψ := φ.neg) (.hyp (by simp)))
  exact .impElim (.hyp (by simp)) (.disjRight (φ := φ) hn)

/-- Q's predecessor axiom supplies an exhaustive zero/successor case split. -/
def zeroOrSuccessor (t : Term n) :
    QProof Γ (.disj (.equal t .zero) (.ex (.equal t.shift (.succ (.var 0))))) :=
  .disjElim (excludedMiddle (.equal t .zero))
    (.disjLeft (.hyp (by simp)))
    (.disjRight (.impElim (.ax (.pred t)) (.hyp (by simp))))

/-- An addition returning zero has zero in its second argument, provably in Q. -/
def zeroSecond (s t : Term n) :
    QProof Γ (.imp (.equal (.add s t) .zero) (.equal t .zero)) := by
  apply Derivation.impIntro
  apply Derivation.disjElim (zeroOrSuccessor t)
  · exact .hyp (by simp)
  · apply Derivation.exElim (φ := .equal t.shift (.succ (.var 0))) (.hyp (by simp))
    let Δ : Context (n + 1) := (.equal t.shift (.succ (.var 0))) ::
      ((Formula.ex (.equal t.shift (.succ (.var 0)))) ::
        (.equal (.add s t) .zero) :: Γ).map Formula.shift
    have ht : QProof Δ (.equal t.shift (.succ (.var 0))) := .hyp (by simp [Δ])
    have hz : QProof Δ (.equal (.add s.shift t.shift) .zero) :=
      .hyp (by simp [Δ, Formula.shift, Formula.rename, Term.rename])
    have he : QProof Δ (.equal (.succ (.add s.shift (.var 0))) .zero) :=
      eqTrans (eqSymm (.ax (.basic (.addSucc s.shift (.var 0)))))
        (eqTrans (eqSymm (addCongrRight s.shift ht)) hz)
    exact .botElim (.impElim (.ax (.basic (.succNonzero (.add s.shift (.var 0))))) he)

/-- A finite, independent syntactic disjunction of consecutive numeral equalities. -/
def enumeration (start : ℕ) : ℕ → Term n → Formula n
  | 0, t => .equal t (.numeral start)
  | k + 1, t => .disj (.equal t (.numeral start)) (enumeration (start + 1) k t)

theorem numeral_subst (k : ℕ) (σ : Fin n → Term m) :
    (Term.numeral k : Term n).subst σ = .numeral k := by
  induction k <;> simp_all [Term.subst]

theorem numeral_rename (k : ℕ) (ρ : Fin n → Fin m) :
    (Term.numeral k : Term n).rename ρ = .numeral k := by
  induction k <;> simp_all [Term.rename]

theorem enumeration_subst (start k : ℕ) (t : Term n) (σ : Fin n → Term m) :
    (enumeration start k t).subst σ = enumeration start k (t.subst σ) := by
  induction k generalizing start with
  | zero => simp [enumeration, Formula.subst, numeral_subst]
  | succ k ih => simp [enumeration, Formula.subst, numeral_subst, ih]

theorem enumeration_rename (start k : ℕ) (t : Term n) (ρ : Fin n → Fin m) :
    (enumeration start k t).rename ρ = enumeration start k (t.rename ρ) := by
  induction k generalizing start with
  | zero => simp [enumeration, Formula.rename, numeral_rename]
  | succ k ih => simp [enumeration, Formula.rename, numeral_rename, ih]

theorem enumeration_inst (start k : ℕ) (t : Term n) :
    (enumeration start k (.var 0)).inst t = enumeration start k t := by
  simp [Formula.inst, enumeration_subst, Term.subst]

/-- Successor shifts a finite numeral enumeration, using actual equality proofs. -/
def successorEnumeration (k : ℕ) : {n : ℕ} → (Δ : Context n) → (start : ℕ) →
    (t : Term n) → QProof Δ (enumeration start k t) →
      QProof Δ (enumeration (start + 1) k (.succ t))
  | _, Δ, start, t, d =>
    match k with
    | 0 => succCongr d
    | k + 1 => .disjElim d
        (.disjLeft (succCongr (.hyp (by simp))))
        (.disjRight (successorEnumeration k _ (start + 1) t (.hyp (by simp))))

/-- If `s+t=k`, Q proves that `t` is one of `0,...,k`. The recursion is over
the concrete metatheoretic bound, not an induction schema inside Q. -/
def finiteSumBound (k : ℕ) : {n : ℕ} → (Δ : Context n) → (s t : Term n) →
    QProof Δ (.imp (.equal (.add s t) (.numeral k)) (enumeration 0 k t))
  | n, Δ, s, t =>
    match k with
    | 0 => zeroSecond s t
    | k + 1 => by
      apply Derivation.impIntro
      apply Derivation.disjElim (zeroOrSuccessor t)
      · exact .disjLeft (.hyp (by simp))
      · apply Derivation.exElim (φ := .equal t.shift (.succ (.var 0))) (.hyp (by simp))
        let Ω : Context (n + 1) := (.equal t.shift (.succ (.var 0))) ::
          ((Formula.ex (.equal t.shift (.succ (.var 0)))) ::
            (.equal (.add s t) (.numeral (k + 1))) :: Δ).map Formula.shift
        have ht : QProof Ω (.equal t.shift (.succ (.var 0))) := .hyp (by simp [Ω])
        have hs : QProof Ω (.equal (.add s.shift t.shift) (.numeral (k + 1))) := by
          have hm : (Formula.equal (.add s t) (.numeral (k + 1))).shift ∈ Ω := by simp [Ω]
          have hr : (Formula.equal (.add s t) (.numeral (k + 1))).shift =
              .equal (.add s.shift t.shift) (.numeral (k + 1)) := by
            change Formula.equal ((Term.add s t).rename Fin.succ)
              ((Term.numeral (k + 1)).rename Fin.succ) = _
            rw [numeral_rename]
            rfl
          exact .hyp (hr ▸ hm)
        have he : QProof Ω
            (.equal (.succ (.add s.shift (.var 0))) (.succ (.numeral k))) :=
          eqTrans (eqSymm (.ax (.basic (.addSucc s.shift (.var 0)))))
            (eqTrans (eqSymm (addCongrRight s.shift ht)) hs)
        have hp : QProof Ω (.equal (.add s.shift (.var 0)) (.numeral k)) :=
          .impElim (.ax (.basic (.succInjective (.add s.shift (.var 0)) (.numeral k)))) he
        have hb := Derivation.impElim (finiteSumBound k Ω s.shift (.var 0)) hp
        have hsucc := successorEnumeration k Ω 0 (.var 0) hb
        have hinst : QProof Ω ((enumeration 1 k (.var 0)).inst (.succ (.var 0))) := by
          simpa only [enumeration_inst] using hsucc
        have hterm : QProof Ω (enumeration 1 k t.shift) := by
          simpa only [enumeration_inst] using
            (Derivation.eqElim (enumeration 1 k (.var 0)) (eqSymm ht) hinst)
        change QProof Ω ((enumeration 0 (k + 1) t).rename Fin.succ)
        rw [enumeration_rename]
        exact .disjRight hterm

/-- An arithmetic presentation of a non-strict bound: `∃ z, z+t=bound`. -/
def atMost (t bound : Term n) : Formula n :=
  .ex (.equal (.add (.var 0) t.shift) bound.shift)

/-- Independent standard-model agreement of the arithmetic bound. -/
theorem atMost_eval (t bound : Term n) (e : Assignment n) :
    (atMost t bound).eval e ↔ t.eval e ≤ bound.eval e := by
  simp only [atMost, Formula.eval, Term.eval, Term.eval_shift, extend, Fin.cases_zero]
  constructor
  · rintro ⟨z, hz⟩
    omega
  · intro h
    obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le h
    exact ⟨z, by omega⟩

/-- Standard-model meaning of the independently constructed finite disjunction. -/
theorem enumeration_eval (start k : ℕ) (t : Term n) (e : Assignment n) :
    (enumeration start k t).eval e ↔ start ≤ t.eval e ∧ t.eval e ≤ start + k := by
  induction k generalizing start with
  | zero =>
    simp only [enumeration, Formula.eval, eval_numeral]
    omega
  | succ k ih =>
    simp only [enumeration, Formula.eval, eval_numeral, ih]
    omega

/-- A concrete arithmetic bound entails its finite enumeration in Q itself. -/
def finiteBound (k : ℕ) (t : Term n) :
    QProof Γ (.imp (atMost t (.numeral k)) (enumeration 0 k t)) := by
  apply Derivation.impIntro
  apply Derivation.exElim (φ := .equal (.add (.var 0) t.shift) (Term.numeral k).shift)
    (.hyp (by simp [atMost]))
  let Δ : Context (n + 1) := (.equal (.add (.var 0) t.shift) (Term.numeral k).shift) ::
    (atMost t (.numeral k) :: Γ).map Formula.shift
  have hs : QProof Δ (.equal (.add (.var 0) t.shift) (.numeral k)) := by
    have hnum : (Term.numeral k : Term n).shift = (Term.numeral k : Term (n + 1)) :=
      numeral_rename k Fin.succ
    exact .hyp (by simp only [Δ, hnum, List.mem_cons, true_or])
  change QProof Δ ((enumeration 0 k t).rename Fin.succ)
  rw [enumeration_rename]
  exact .impElim (finiteSumBound k Δ (.var 0) t.shift) hs

/-- A numeral summand is cancelled by finitely many addition and successor rules. -/
def cancelNumeral : (k j : ℕ) → {n : ℕ} → (Δ : Context n) → (s : Term n) →
    QProof Δ (.imp (.equal (.add s (.numeral j)) (.numeral k))
      (.equal s (.numeral (k - j))))
  | k, 0, _, _, s => .impIntro
      (eqTrans (eqSymm (.ax (.basic (.addZero s)))) (.hyp (by simp)))
  | 0, j + 1, _, _, s => .impIntro (.botElim (.impElim
      (.ax (.basic (.succNonzero (.add s (.numeral j)))))
      (eqTrans (eqSymm (.ax (.basic (.addSucc s (.numeral j))))) (.hyp (by simp)))))
  | k + 1, j + 1, _, Δ, s => by
      have hsub : k + 1 - (j + 1) = k - j := by omega
      rw [hsub]
      exact .impIntro (.impElim
        (cancelNumeral k j _ s)
        (.impElim (.ax (.basic (.succInjective (.add s (.numeral j)) (.numeral k))))
          (eqTrans (eqSymm (.ax (.basic (.addSucc s (.numeral j))))) (.hyp (by simp)))))

/-- Insert an actual equality proof at its numeral's position in the finite disjunction. -/
def enumerationIntro (k : ℕ) : {n : ℕ} → (Δ : Context n) → (start a : ℕ) →
    (s : Term n) → start ≤ a → a ≤ start + k → QProof Δ (.equal s (.numeral a)) →
      QProof Δ (enumeration start k s)
  | _, _, start, a, s, hstart, hend, d =>
    match k with
    | 0 => by
      have ha : a = start := by omega
      simpa only [ha, enumeration] using d
    | k + 1 =>
      if ha : a = start then by
        apply Derivation.disjLeft
        simpa only [ha] using d
      else .disjRight (enumerationIntro k _ (start + 1) a s (by omega) (by omega) d)

/-- Finite case analysis retains each equality hypothesis as an actual Q derivation. -/
def enumerationElim (k : ℕ) : {n : ℕ} → (Δ : Context n) → (start : ℕ) →
    (s : Term n) → (χ : Formula n) → QProof Δ (enumeration start k s) →
    (∀ a, start ≤ a → a ≤ start + k → QProof (.equal s (.numeral a) :: Δ) χ) →
      QProof Δ χ
  | _, Δ, start, s, χ, d, cases =>
    match k with
    | 0 => .impElim (.impIntro (cases start (by omega) (by omega))) d
    | k + 1 => .disjElim d
        (cases start (by omega) (by omega))
        (enumerationElim k _ (start + 1) s χ (.hyp (by simp)) (fun a hstart hend =>
          .weaken (by
            intro ξ hξ
            rcases List.mem_cons.mp hξ with rfl | hξ
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hξ))
            (cases a (by omega) (by omega))))

/-- Both summands are provably bounded by a concrete numeral. This direction
does not assume addition commutativity, which Q does not generally prove. -/
def finiteFirstSumBound (k : ℕ) (s t : Term n) :
    QProof Γ (.imp (.equal (.add s t) (.numeral k)) (enumeration 0 k s)) := by
  apply Derivation.impIntro
  let Δ : Context n := .equal (.add s t) (.numeral k) :: Γ
  have hb : QProof Δ (enumeration 0 k t) :=
    .impElim (finiteSumBound k Δ s t) (.hyp (by simp [Δ]))
  apply enumerationElim k Δ 0 t (enumeration 0 k s) hb
  intro j _ _
  let Ω : Context n := .equal t (.numeral j) :: Δ
  have hs : QProof Ω (.equal (.add s t) (.numeral k)) := .hyp (by simp [Ω, Δ])
  have hj : QProof Ω (.equal t (.numeral j)) := .hyp (by simp [Ω])
  have he : QProof Ω (.equal (.add s (.numeral j)) (.numeral k)) :=
    eqTrans (eqSymm (addCongrRight s hj)) hs
  have hc : QProof Ω (.equal s (.numeral (k - j))) :=
    .impElim (cancelNumeral k j Ω s) he
  exact enumerationIntro k Ω 0 (k - j) s (Nat.zero_le _) (by omega) hc

/-- Strict order in the same pure arithmetic presentation used by the hierarchy
bridge: `∃ z, S(s)+z=bound`. -/
def below (s bound : Term n) : Formula n :=
  .ex (.equal (.add (.succ s.shift) (.var 0)) bound.shift)

theorem below_eval (s bound : Term n) (e : Assignment n) :
    (below s bound).eval e ↔ s.eval e < bound.eval e := by
  simp only [below, Formula.eval, Term.eval, Term.eval_shift, extend, Fin.cases_zero]
  constructor
  · rintro ⟨z, hz⟩
    omega
  · intro h
    obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt h)
    exact ⟨z, by omega⟩

/-- The actual strict-order arithmetic graph yields a finite Q case split.
The enumeration conservatively includes the endpoint; strictness can exclude it. -/
def belowFinite (k : ℕ) (s : Term n) :
    QProof Γ (.imp (below s (.numeral k)) (enumeration 0 k s)) := by
  apply Derivation.impIntro
  apply Derivation.exElim
    (φ := .equal (.add (.succ s.shift) (.var 0)) (Term.numeral k).shift)
    (.hyp (by simp [below]))
  let Δ : Context (n + 1) := (.equal (.add (.succ s.shift) (.var 0)) (Term.numeral k).shift) ::
    (below s (.numeral k) :: Γ).map Formula.shift
  have hs : QProof Δ (.equal (.add (.succ s.shift) (.var 0)) (.numeral k)) := by
    have hnum : (Term.numeral k : Term n).shift = (Term.numeral k : Term (n + 1)) :=
      numeral_rename k Fin.succ
    exact .hyp (by simp only [Δ, hnum, List.mem_cons, true_or])
  have hb : QProof Δ (enumeration 0 k (.succ s.shift)) :=
    .impElim (finiteFirstSumBound k (.succ s.shift) (.var 0)) hs
  change QProof Δ ((enumeration 0 k s).rename Fin.succ)
  rw [enumeration_rename]
  apply enumerationElim k Δ 0 (.succ s.shift) (enumeration 0 k s.shift) hb
  intro a _ hend
  cases a with
  | zero =>
    exact .botElim (.impElim (.ax (.basic (.succNonzero s.shift))) (.hyp (by simp)))
  | succ j =>
    have he : QProof (.equal (.succ s.shift) (.numeral (j + 1)) :: Δ)
        (.equal s.shift (.numeral j)) :=
      .impElim (.ax (.basic (.succInjective s.shift (.numeral j)))) (.hyp (by simp))
    exact enumerationIntro k _ 0 j s.shift (Nat.zero_le _) (by omega) he

end Silmaril.Logic.Arithmetic.Completeness
