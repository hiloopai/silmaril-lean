module

public import Silmaril.Logic.ArithmeticToSecondOrder.Equality

@[expose] public section

namespace Silmaril.Logic.ArithmeticToSecondOrder

open SecondOrderArithmetic

variable {S : Subsystem} {n : ℕ}

/-- A finite set avoids the binder interval. -/
def Avoid (k h : ℕ) (xs : Finset ℕ) : Prop := ∀ x ∈ xs, x < k ∨ k + h ≤ x

def ParametersAvoid (k h : ℕ) (e : Fin n → Term ℕ) : Prop :=
  ∀ i, Avoid k h (e i).names

theorem ParametersAvoid.mono {k h h' : ℕ} {e : Fin n → Term ℕ}
    (he : ParametersAvoid k h e) (hh : h' ≤ h) : ParametersAvoid k h' e := by
  intro i x hx
  rcases he i x hx with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem ParametersAvoid.fresh {k h : ℕ} {e : Fin n → Term ℕ}
    (he : ParametersAvoid k (h + 1) e) (i : Fin n) : k + h ∉ (e i).names := by
  intro hx
  rcases he i _ hx with h | h <;> omega

theorem term_avoid (t : Arithmetic.Term n) {k h : ℕ} {e : Fin n → Term ℕ}
    (he : ParametersAvoid k h e) : Avoid k h (term e t).names := by
  intro x hx
  obtain ⟨i, hi⟩ := term_names t e x hx
  exact he i x hi

theorem formula_fresh (p : Arithmetic.Formula n) (k x : ℕ)
    (e : Fin n → Term ℕ) (hx : x < k ∨ k + height p ≤ x)
    (he : ∀ i, x ∉ (e i).names) : x ∉ (formula k e p).names := by
  intro h
  rcases formula_names p k e x h with h | ⟨i, hi⟩
  · rcases hx with hx | hx <;> omega
  · exact he i hi

/-- The SOA equality schema for every translated arithmetic formula,
including nested universal and existential number quantifiers. -/
def replacement (p : Arithmetic.Formula (n + 1)) (k : ℕ)
    (e : Fin n → Term ℕ) (s t : Term ℕ)
    (hs : Avoid k (height p) s.names) (ht : Avoid k (height p) t.names) :
    EquivalenceUnder S (.equal s t)
      (formula k (Fin.cases s e) p) (formula k (Fin.cases t e) p) := by
  have hi : ∀ i, Proof S (.imp (.equal s t)
      (.equal (Fin.cases s e i) (Fin.cases t e i))) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (HProof.identity (.equal s t)).toProof
    · exact ((HProof.eqRefl (e j)).weaken (.equal s t)).toProof
  apply formula_congr k (.equal s t) p _ _ hi
  intro x hx
  simp only [Formula.names, Finset.mem_union] at hx
  exact hx.elim (hs x) (ht x)

namespace HProof

variable {Γ : List (Formula ℕ)} {p q : Formula ℕ}

/-- Universally quantified equality transport plus ax-Tex yields substitution.
No semantic premise and no added universal-instantiation axiom is used. -/
def instantiateGuard (x : ℕ) (t : Term ℕ) (hx : x ∉ t.names) (hq : x ∉ q.names)
    (d : Proof S (.imp (.equal (.var x) t) (.imp p q)))
    (hp : HProof S Γ (.all x p)) : HProof S Γ q := by
  have heq : HProof S [.equal (.var x) t, p] (.equal (.var x) t) := .hyp (by simp)
  have hi : Proof S (.imp p (.imp (.equal (.var x) t) q)) :=
    (HProof.mp (HProof.hyp (by simp)) (applyGuard d heq)).discharge.discharge.toProof
  exact allGuard x t hx hq (allMP x hp (.proved (.gen x hi)))

end HProof

/-- Eliminate an encoded universal using a named term, preserving the source
body's literal substitution convention. The binder may be a fresh eigenname. -/
def allInstantiate (p : Arithmetic.Formula (n + 1)) (k x : ℕ)
    (e : Fin n → Term ℕ) (t : Term ℕ)
    (hx : x < k ∨ k + height p ≤ x)
    (he : ∀ i, x ∉ (e i).names) (htx : x ∉ t.names)
    (ht : Avoid k (height p) t.names) :
    Proof S (.imp (.all x (formula k (Fin.cases (.var x) e) p))
      (formula k (Fin.cases t e) p)) := by
  have hs : Avoid k (height p) (Term.var x).names := by
    intro y hy
    have hy' : y = x := by simpa [Term.names] using hy
    subst y
    exact hx
  have hf : x ∉ (formula k (Fin.cases t e) p).names := by
    apply formula_fresh p k x _ hx
    intro i
    refine Fin.cases htx (fun j => he j) i
  have hp : HProof S [.all x (formula k (Fin.cases (.var x) e) p)]
      (.all x (formula k (Fin.cases (.var x) e) p)) := .hyp (by simp)
  exact (HProof.instantiateGuard x t htx hf
    (replacement p k e (.var x) t hs ht).forward hp).discharge.toProof

/-- The corresponding rule for the primitive negation of an encoded body. -/
def allInstantiateNeg (p : Arithmetic.Formula (n + 1)) (k x : ℕ)
    (e : Fin n → Term ℕ) (t : Term ℕ)
    (hx : x < k ∨ k + height p ≤ x)
    (he : ∀ i, x ∉ (e i).names) (htx : x ∉ t.names)
    (ht : Avoid k (height p) t.names) :
    Proof S (.imp (.all x (.neg (formula k (Fin.cases (.var x) e) p)))
      (.neg (formula k (Fin.cases t e) p))) := by
  have hs : Avoid k (height p) (Term.var x).names := by
    intro y hy
    have hy' : y = x := by simpa [Term.names] using hy
    subst y
    exact hx
  have hf : x ∉ (formula k (Fin.cases t e) p).names := by
    apply formula_fresh p k x _ hx
    intro i
    refine Fin.cases htx (fun j => he j) i
  have hp : HProof S [.all x (.neg (formula k (Fin.cases (.var x) e) p))]
      (.all x (.neg (formula k (Fin.cases (.var x) e) p))) := .hyp (by simp)
  exact (HProof.instantiateGuard (q := .neg (formula k (Fin.cases t e) p)) x t htx
    (by simpa only [Formula.names] using hf)
    (replacement p k e (.var x) t hs ht).neg.forward hp).discharge.toProof

/-- Existential introduction derived from df-Ex and universal instantiation. -/
def exInstantiate (p : Arithmetic.Formula (n + 1)) (k x : ℕ)
    (e : Fin n → Term ℕ) (t : Term ℕ)
    (hx : x < k ∨ k + height p ≤ x)
    (he : ∀ i, x ∉ (e i).names) (htx : x ∉ t.names)
    (ht : Avoid k (height p) t.names) :
    Proof S (.imp (formula k (Fin.cases t e) p)
      (.ex x (formula k (Fin.cases (.var x) e) p))) := by
  let body := formula k (Fin.cases (.var x) e) p
  have h : HProof S [formula k (Fin.cases t e) p] (formula k (Fin.cases t e) p) := .hyp (by simp)
  have dn := HProof.contrapose (HProof.proved (S := S) (Γ := [])
    (allInstantiateNeg p k x e t hx he htx ht))
  have hn := HProof.mp h.doubleNeg (HProof.proved dn.toProof)
  exact (HProof.mp hn (HProof.iffBackward (HProof.base (.dfEx body x)))).discharge.toProof

namespace HProof

variable {Γ : List (Formula ℕ)} {p q : Formula ℕ}

/-- Existential elimination from a generalized implication. -/
def existsEliminate (x : ℕ) (hq : x ∉ q.names) (d : HProof S Γ (.ex x p))
    (di : HProof S Γ (.all x (.imp p q))) : HProof S Γ q := by
  have contra : Proof S (.imp (.imp p q) (.imp (.neg q) (.neg p))) :=
    (contrapose (HProof.hyp (S := S) (Γ := [.imp p q]) (by simp))).discharge.toProof
  have hd := allMP x di (.proved (.gen x contra))
  have hnq : HProof S (.neg q :: Γ) (.all x (.neg q)) :=
    .mp (.hyp (by simp)) (base (.ax5 (.neg q) x hq))
  have hdn := hd.lift (Δ := .neg q :: Γ) (fun r hr => List.mem_cons_of_mem _ hr)
  have hnp := allMP x hnq hdn
  have he := d.lift (Δ := .neg q :: Γ) (fun r hr => List.mem_cons_of_mem _ hr)
  have hne : HProof S (.neg q :: Γ) (.neg (.all x (.neg p))) := .mp he (iffForward (base (.dfEx p x)))
  exact clavius (explosion hnp hne q).discharge

end HProof

/-- Rename an outer binder by a finite proof, rather than a syntax quotient. -/
def allRename (p : Arithmetic.Formula (n + 1)) (k x y : ℕ)
    (e : Fin n → Term ℕ) (hxy : x ≠ y)
    (hx : x < k ∨ k + height p ≤ x) (hy : y < k ∨ k + height p ≤ y)
    (hex : ∀ i, x ∉ (e i).names) (hey : ∀ i, y ∉ (e i).names) :
    Proof S (.imp (.all y (formula k (Fin.cases (.var y) e) p))
      (.all x (formula k (Fin.cases (.var x) e) p))) := by
  have htx : y ∉ (Term.var x).names := by simp [Term.names, Ne.symm hxy]
  have ht : Avoid k (height p) (Term.var x).names := by
    intro z hz
    have hz' : z = x := by simpa [Term.names] using hz
    subst z
    exact hx
  have hf : x ∉ (formula k (Fin.cases (.var y) e) p).names := by
    apply formula_fresh p k x _ hx
    intro i
    refine Fin.cases ?_ (fun j => hex j) i
    simpa [Term.names] using hxy
  have hp : HProof S [.all y (formula k (Fin.cases (.var y) e) p)]
      (.all y (formula k (Fin.cases (.var y) e) p)) := .hyp (by simp)
  have hi := HProof.mp hp
    (HProof.proved (allInstantiate (S := S) p k y e (.var x) hy hey htx ht))
  have hg : HProof S [.all y (formula k (Fin.cases (.var y) e) p)]
      (.all x (formula k (Fin.cases (.var x) e) p)) :=
    hi.generalize x (by simp [Formula.names, hxy, hf])
  exact hg.discharge.toProof

def allRenameNeg (p : Arithmetic.Formula (n + 1)) (k x y : ℕ)
    (e : Fin n → Term ℕ) (hxy : x ≠ y)
    (hx : x < k ∨ k + height p ≤ x) (hy : y < k ∨ k + height p ≤ y)
    (hex : ∀ i, x ∉ (e i).names) (hey : ∀ i, y ∉ (e i).names) :
    Proof S (.imp (.all y (.neg (formula k (Fin.cases (.var y) e) p)))
      (.all x (.neg (formula k (Fin.cases (.var x) e) p)))) := by
  have htx : y ∉ (Term.var x).names := by simp [Term.names, Ne.symm hxy]
  have ht : Avoid k (height p) (Term.var x).names := by
    intro z hz
    have hz' : z = x := by simpa [Term.names] using hz
    subst z
    exact hx
  have hf : x ∉ (formula k (Fin.cases (.var y) e) p).names := by
    apply formula_fresh p k x _ hx
    intro i
    refine Fin.cases ?_ (fun j => hex j) i
    simpa [Term.names] using hxy
  have hp : HProof S [.all y (.neg (formula k (Fin.cases (.var y) e) p))]
      (.all y (.neg (formula k (Fin.cases (.var y) e) p))) := .hyp (by simp)
  have hi := HProof.mp hp
    (HProof.proved (allInstantiateNeg (S := S) p k y e (.var x) hy hey htx ht))
  have hg : HProof S [.all y (.neg (formula k (Fin.cases (.var y) e) p))]
      (.all x (.neg (formula k (Fin.cases (.var x) e) p))) :=
    hi.generalize x (by simp [Formula.names, hxy, hf])
  exact hg.discharge.toProof

/-- Binder renaming for existential formulas uses the same universal proof map. -/
def exRename (p : Arithmetic.Formula (n + 1)) (k x y : ℕ)
    (e : Fin n → Term ℕ) (hxy : x ≠ y)
    (hx : x < k ∨ k + height p ≤ x) (hy : y < k ∨ k + height p ≤ y)
    (hex : ∀ i, x ∉ (e i).names) (hey : ∀ i, y ∉ (e i).names) :
    Proof S (.imp (.ex y (formula k (Fin.cases (.var y) e) p))
      (.ex x (formula k (Fin.cases (.var x) e) p))) := by
  let px := formula k (Fin.cases (.var x) e) p
  let py := formula k (Fin.cases (.var y) e) p
  have dn := HProof.contrapose (HProof.proved (S := S) (Γ := [])
    (allRenameNeg p k y x e (Ne.symm hxy) hy hx hey hex))
  have hp : HProof S [.ex y py] (.neg (.all y (.neg py))) :=
    .mp (.hyp (by simp)) (HProof.iffForward (HProof.base (.dfEx py y)))
  have hq := HProof.mp hp (HProof.proved dn.toProof)
  exact (HProof.mp hq (HProof.iffBackward (HProof.base (.dfEx px x)))).discharge.toProof

/-- Eliminate the pointwise equality form of an encoded instance. -/
def guardEliminate (p : Arithmetic.Formula (n + 1)) (k x : ℕ)
    (e : Fin n → Term ℕ) (t : Term ℕ)
    (hx : x < k ∨ k + height p ≤ x)
    (he : ∀ i, x ∉ (e i).names) (htx : x ∉ t.names)
    (ht : Avoid k (height p) t.names) :
    Proof S (.imp (.all x (.imp (.equal (.var x) t)
      (formula k (Fin.cases (.var x) e) p))) (formula k (Fin.cases t e) p)) := by
  have hs : Avoid k (height p) (Term.var x).names := by
    intro y hy
    have hy' : y = x := by simpa [Term.names] using hy
    subst y
    exact hx
  let eq := Formula.equal (.var x) t
  let px := formula k (Fin.cases (.var x) e) p
  have hg : HProof S [.imp eq px, eq] eq := .hyp (by simp)
  have hp : HProof S [.imp eq px, eq] px := .mp hg (.hyp (by simp))
  have dr : Proof S (.imp eq (.imp (.imp eq px) (formula k (Fin.cases t e) p))) :=
    (HProof.mp hp (HProof.applyGuard (replacement (S := S) p k e (.var x) t hs ht).forward hg)).discharge.discharge.toProof
  have hf : x ∉ (formula k (Fin.cases t e) p).names := by
    apply formula_fresh p k x _ hx
    intro i
    refine Fin.cases htx (fun j => he j) i
  have ha : HProof S [.all x (.imp eq px)] (.all x (.imp eq px)) := .hyp (by simp)
  exact (HProof.instantiateGuard x t htx hf dr ha).discharge.toProof

/-- Pointwise equality guards can be introduced from a term instance. -/
def guardIntroduce (p : Arithmetic.Formula (n + 1)) (k x : ℕ)
    (e : Fin n → Term ℕ) (t : Term ℕ)
    (hx : x < k ∨ k + height p ≤ x)
    (he : ∀ i, x ∉ (e i).names) (htx : x ∉ t.names)
    (ht : Avoid k (height p) t.names) :
    Proof S (.imp (formula k (Fin.cases t e) p)
      (.all x (.imp (.equal (.var x) t) (formula k (Fin.cases (.var x) e) p)))) := by
  have hs : Avoid k (height p) (Term.var x).names := by
    intro y hy
    have hy' : y = x := by simpa [Term.names] using hy
    subst y
    exact hx
  let pt := formula k (Fin.cases t e) p
  have hg : HProof S [.equal (.var x) t, pt] (.equal (.var x) t) := .hyp (by simp)
  have hp : HProof S [.equal (.var x) t, pt] pt := .hyp (by simp)
  have hi := (HProof.mp hp (HProof.applyGuard
    (replacement (S := S) p k e (.var x) t hs ht).backward hg)).discharge
  have hf : x ∉ pt.names := by
    apply formula_fresh p k x _ hx
    intro i
    refine Fin.cases htx (fun j => he j) i
  exact (hi.generalize x (by simp [hf])).discharge.toProof


end Silmaril.Logic.ArithmeticToSecondOrder
