module

public import Silmaril.Logic.ArithmeticToSecondOrder.Syntax
public import Silmaril.Logic.ArithmeticToSecondOrder.Hilbert

@[expose] public section

namespace Silmaril.Logic.ArithmeticToSecondOrder

open SecondOrderArithmetic

variable {N : Type} [DecidableEq N] {S : Subsystem}

namespace HProof

variable {Γ : List (Formula N)} {s t u : Term N} {g p q : Formula N}

def eqSymm (d : HProof S Γ (.equal s t)) : HProof S Γ (.equal t s) :=
  .mp (eqRefl s) (.mp d (base (.ax7 s t s)))

def eqTrans (d : HProof S Γ (.equal s t)) (e : HProof S Γ (.equal t u)) :
    HProof S Γ (.equal s u) := .mp e (.mp d.eqSymm (base (.ax7 t s u)))

def applyGuard (d : Proof S (.imp g p)) (h : HProof S Γ g) : HProof S Γ p :=
  .mp h (.proved d)

end HProof

/-- Both directions are finite target proofs under a common antecedent. -/
structure EquivalenceUnder (S : Subsystem) (g p q : Formula N) where
  forward : Proof S (.imp g (.imp p q))
  backward : Proof S (.imp g (.imp q p))

namespace EquivalenceUnder

variable {g p q p' q' : Formula N}

def refl (g p : Formula N) : EquivalenceUnder S g p p :=
  ⟨((HProof.identity p).weaken g).toProof, ((HProof.identity p).weaken g).toProof⟩

def swap (d : EquivalenceUnder S g p q) : EquivalenceUnder S g q p :=
  ⟨d.backward, d.forward⟩

def impForward (d : Proof S (.imp g (.imp p' p)))
    (e : Proof S (.imp g (.imp q q'))) : Proof S (.imp g (.imp (.imp p q) (.imp p' q'))) := by
  have hg : HProof S [p', .imp p q, g] g := .hyp (by simp)
  have hp : HProof S [p', .imp p q, g] p :=
    .mp (.hyp (by simp)) (HProof.applyGuard d hg)
  have hq : HProof S [p', .imp p q, g] q := .mp hp (.hyp (by simp))
  exact (HProof.mp hq (HProof.applyGuard e hg)).discharge.discharge.discharge.toProof

def imp (d : EquivalenceUnder S g p p') (e : EquivalenceUnder S g q q') :
    EquivalenceUnder S g (.imp p q) (.imp p' q') :=
  ⟨impForward d.backward e.forward, impForward d.forward e.backward⟩

def negForward (d : Proof S (.imp g (.imp q p))) :
    Proof S (.imp g (.imp (.neg p) (.neg q))) :=
  (HProof.contrapose (HProof.applyGuard d (HProof.hyp (Γ := [g]) (by simp)))).discharge.toProof

def neg (d : EquivalenceUnder S g p q) : EquivalenceUnder S g (.neg p) (.neg q) :=
  ⟨negForward d.backward, negForward d.forward⟩

def conjForward (d : Proof S (.imp g (.imp p p')))
    (e : Proof S (.imp g (.imp q q'))) :
    Proof S (.imp g (.imp (.conj p q) (.conj p' q'))) := by
  have hg : HProof S [.conj p q, g] g := .hyp (by simp)
  have h : HProof S [.conj p q, g] (.conj p q) := .hyp (by simp)
  exact (HProof.conjIntro (.mp h.conjLeft (HProof.applyGuard d hg))
    (.mp h.conjRight (HProof.applyGuard e hg))).discharge.discharge.toProof

def conj (d : EquivalenceUnder S g p p') (e : EquivalenceUnder S g q q') :
    EquivalenceUnder S g (.conj p q) (.conj p' q') :=
  ⟨conjForward d.forward e.forward, conjForward d.backward e.backward⟩

def allForward (x : N) (hx : x ∉ g.names) (d : Proof S (.imp g (.imp p q))) :
    Proof S (.imp g (.imp (.all x p) (.all x q))) := by
  have hg : HProof S [.all x p, g] (.all x g) :=
    .mp (.hyp (by simp)) (HProof.base (.ax5 g x hx))
  have di : HProof S [.all x p, g] (.all x (.imp p q)) :=
    HProof.allMP x hg (.proved (.gen x d))
  exact (HProof.allMP x (.hyp (by simp)) di).discharge.discharge.toProof

def all (x : N) (hx : x ∉ g.names) (d : EquivalenceUnder S g p q) :
    EquivalenceUnder S g (.all x p) (.all x q) :=
  ⟨allForward x hx d.forward, allForward x hx d.backward⟩

def exForward (x : N) (d : Proof S (.imp g (.imp (.neg (.all x (.neg p)))
      (.neg (.all x (.neg q)))))) : Proof S (.imp g (.imp (.ex x p) (.ex x q))) := by
  have hg : HProof S [.ex x p, g] g := .hyp (by simp)
  have hp : HProof S [.ex x p, g] (.neg (.all x (.neg p))) :=
    .mp (.hyp (by simp)) (HProof.iffForward (HProof.base (.dfEx p x)))
  have hq := HProof.mp hp (HProof.applyGuard d hg)
  exact (HProof.mp hq (HProof.iffBackward (HProof.base (.dfEx q x)))).discharge.discharge.toProof

def ex (x : N) (hx : x ∉ g.names) (d : EquivalenceUnder S g p q) :
    EquivalenceUnder S g (.ex x p) (.ex x q) := by
  let e := ((d.neg).all x hx).neg
  exact ⟨exForward x e.forward, exForward x e.backward⟩

end EquivalenceUnder

variable {n : ℕ}

/-- Pointwise equality of parameter terms extends through arithmetic terms. -/
def term_congr (g : Formula ℕ) (e f : Fin n → Term ℕ)
    (h : ∀ i, Proof S (.imp g (.equal (e i) (f i)))) :
    (t : Arithmetic.Term n) → Proof S (.imp g (.equal (term e t) (term f t)))
  | .var i => h i
  | .zero => ((HProof.eqRefl .zero).weaken g).toProof
  | .succ t =>
    (HProof.mp (HProof.applyGuard (term_congr g e f h t) (HProof.hyp (Γ := [g]) (by simp)))
      (HProof.base (.axEqS (term e t) (term f t)))).discharge.toProof
  | .add s t => by
    have hg : HProof S [g] g := .hyp (by simp)
    have hs := HProof.applyGuard (term_congr g e f h s) hg
    have ht := HProof.applyGuard (term_congr g e f h t) hg
    exact (HProof.eqTrans (.mp hs (HProof.base (.axEqpl1 _ _ _)))
      (.mp ht (HProof.base (.axEqpl2 _ _ _)))).discharge.toProof
  | .mul s t => by
    have hg : HProof S [g] g := .hyp (by simp)
    have hs := HProof.applyGuard (term_congr g e f h s) hg
    have ht := HProof.applyGuard (term_congr g e f h t) hg
    exact (HProof.eqTrans (.mp hs (HProof.base (.axEqmu1 _ _ _)))
      (.mp ht (HProof.base (.axEqmu2 _ _ _)))).discharge.toProof

def equalForward {g : Formula ℕ} {s s' t t' : Term ℕ}
    (d : Proof S (.imp g (.equal s s'))) (e : Proof S (.imp g (.equal t t'))) :
    Proof S (.imp g (.imp (.equal s t) (.equal s' t'))) := by
  have hg : HProof S [.equal s t, g] g := .hyp (by simp)
  have hs := HProof.applyGuard d hg
  have ht := HProof.applyGuard e hg
  exact (hs.eqSymm.eqTrans ((HProof.hyp (by simp)).eqTrans ht)).discharge.discharge.toProof

def equalCongr {g : Formula ℕ} {s s' t t' : Term ℕ}
    (d : Proof S (.imp g (.equal s s'))) (e : Proof S (.imp g (.equal t t'))) :
    EquivalenceUnder S g (.equal s t) (.equal s' t') := by
  have ds := (HProof.applyGuard d (HProof.hyp (Γ := [g]) (by simp))).eqSymm.discharge.toProof
  have es := (HProof.applyGuard e (HProof.hyp (Γ := [g]) (by simp))).eqSymm.discharge.toProof
  exact ⟨equalForward d e, equalForward ds es⟩

/-- Equal parameter assignments preserve formulas by actual Hilbert proofs.
Only the guard needs freshness at binders: quantifier distribution generalizes
the closed induction hypothesis, rather than hypotheses mentioning that binder. -/
def formula_congr (k : ℕ) (g : Formula ℕ) {n : ℕ} (p : Arithmetic.Formula n)
    (e f : Fin n → Term ℕ) (h : ∀ i, Proof S (.imp g (.equal (e i) (f i))))
    (hg : ∀ x ∈ g.names, x < k ∨ k + height p ≤ x) :
    EquivalenceUnder S g (formula k e p) (formula k f p) :=
  match p with
  | .bot => .refl g falsum
  | .equal s t => equalCongr (term_congr g e f h s) (term_congr g e f h t)
  | .imp p q | .conj p q | .disj p q => by
    have hp : ∀ x ∈ g.names, x < k ∨ k + height p ≤ x := by
      intro x hx
      rcases hg x hx with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [height] at h; omega)
    have hq : ∀ x ∈ g.names, x < k ∨ k + height q ≤ x := by
      intro x hx
      rcases hg x hx with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [height] at h; omega)
    have dp := formula_congr k g p e f h hp
    have dq := formula_congr k g q e f h hq
    first | exact dp.imp dq | exact dp.conj dq | exact (dp.neg.conj dq.neg).neg
  | .all p | .ex p => by
    have hx : k + height p ∉ g.names := by
      intro hx
      rcases hg _ hx with h | h
      · omega
      · simp only [height] at h
        omega
    have hp : ∀ x ∈ g.names, x < k ∨ k + height p ≤ x := by
      intro x hx
      rcases hg x hx with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [height] at h; omega)
    have hi : ∀ i, Proof S (.imp g
        (.equal (Fin.cases (.var (k + height p)) e i)
          (Fin.cases (.var (k + height p)) f i))) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ((HProof.eqRefl _).weaken g).toProof
      · exact h j
    have dp := formula_congr k g p _ _ hi hp
    first | exact dp.all _ hx | exact dp.ex _ hx
termination_by structural p

end Silmaril.Logic.ArithmeticToSecondOrder
