module

public import Silmaril.Logic.SecondOrderArithmetic.Systems

@[expose] public section

/-! Hilbert proof trees with temporary assumptions. Discharging assumptions
constructs ax-1/ax-2 proof trees; the empty-context compiler returns the existing
SOA proof type. Every leaf is an existing subsystem axiom or a hypothesis. -/

namespace Silmaril.Logic.ArithmeticToSecondOrder

open SecondOrderArithmetic

variable {N : Type} [DecidableEq N] {S : Subsystem}

inductive HProof (S : Subsystem) (Γ : List (Formula N)) : Formula N → Type
  | hyp {p} : p ∈ Γ → HProof S Γ p
  | proved {p} : Proof S p → HProof S Γ p
  | mp {p q} : HProof S Γ p → HProof S Γ (.imp p q) → HProof S Γ q

namespace HProof

variable {Γ Δ : List (Formula N)} {p q r : Formula N}

def base (a : BaseAxiom p) : HProof S Γ p := .proved (.axiom (.base a))

def identity (p : Formula N) : HProof S Γ (.imp p p) :=
  .mp (base (.ax1 p p)) (.mp (base (.ax1 p (.imp p p))) (base (.ax2 p (.imp p p) p)))

def weaken (d : HProof S Γ p) (q : Formula N) : HProof S Γ (.imp q p) :=
  .mp d (base (.ax1 p q))

def lift (h : ∀ p ∈ Γ, p ∈ Δ) {p} : HProof S Γ p → HProof S Δ p
  | .hyp hp => .hyp (h _ hp)
  | .proved a => .proved a
  | .mp d e => .mp (lift h d) (lift h e)

/-- The deduction theorem constructs a finite Hilbert tree. -/
def discharge {q} : HProof S (p :: Γ) q → HProof S Γ (.imp p q)
  | .hyp h => by
    by_cases hp : q = p
    · subst q; exact identity p
    · exact (HProof.hyp ((List.mem_cons.1 h).resolve_left hp)).weaken p
  | .proved a => (HProof.proved a).weaken p
  | @HProof.mp _ _ _ _ q r d e => .mp (discharge d) (.mp (discharge e) (base (.ax2 p q r)))

/-- Generalize a derivation whose assumptions have the required freshness.
The distribution axiom handles modus ponens; ax-5 handles hypotheses. -/
def generalize (x : N) (hx : ∀ q ∈ Γ, x ∉ q.names) {p} :
    HProof S Γ p → HProof S Γ (.all x p)
  | .hyp h => .mp (.hyp h) (base (.ax5 p x (hx p h)))
  | .proved a => .proved (.gen x a)
  | @HProof.mp _ _ _ _ p q d e => .mp (generalize x hx d)
      (.mp (generalize x hx e) (base (.ax4 p q x)))

/-- Closed temporary-assumption trees compile to the original SOA proof type. -/
def toProof {p} : HProof S ([] : List (Formula N)) p → Proof S p
  | .hyp h => nomatch h
  | .proved a => a
  | .mp d e => .mp (toProof d) (toProof e)

/-- Contradictory formulas yield a finite ax-3 proof of any conclusion. -/
def explosion (dp : HProof S Γ p) (dn : HProof S Γ (.neg p)) (q : Formula N) :
    HProof S Γ q := .mp dp (.mp (dn.weaken (.neg q)) (base (.ax3 q p)))

/-- Clavius law, following the elementary ax-3 argument used by Metamath
`pm2.18d`: https://us.metamath.org/mpeuni/pm2.18d.html. -/
def clavius (d : HProof S Γ (.imp (.neg p) p)) : HProof S Γ p := by
  let h : ∀ q ∈ Γ, q ∈ (.neg p :: Γ) := fun q hq => List.mem_cons_of_mem _ hq
  have dp : HProof S (.neg p :: Γ) p := .mp (.hyp (by simp)) (d.lift h)
  have dn : HProof S (.neg p :: Γ) (.neg (.imp (.neg p) p)) :=
    explosion dp (.hyp (by simp)) _
  exact .mp d (.mp dn.discharge (base (.ax3 p (.imp (.neg p) p))))

def dne (d : HProof S Γ (.neg (.neg p))) : HProof S Γ p := by
  have dn : HProof S (.neg p :: Γ) (.neg (.neg p)) :=
    d.lift (fun q hq => List.mem_cons_of_mem _ hq)
  exact clavius (explosion (.hyp (by simp)) dn p).discharge

/-- Negation introduction discharges a contradictory positive assumption. -/
def negIntro (dq : HProof S (p :: Γ) q) (dn : HProof S (p :: Γ) (.neg q)) :
    HProof S Γ (.neg p) := by
  have dnnp : HProof S (.neg (.neg p) :: Γ) (.neg (.neg p)) := .hyp (by simp)
  have dp := dne dnnp
  have hdq : HProof S (.neg (.neg p) :: Γ) q := .mp dp (dq.discharge.lift (fun q hq => List.mem_cons_of_mem _ hq))
  have hdn : HProof S (.neg (.neg p) :: Γ) (.neg q) := .mp dp (dn.discharge.lift (fun q hq => List.mem_cons_of_mem _ hq))
  exact clavius (explosion hdq hdn (.neg p)).discharge

def doubleNeg (d : HProof S Γ p) : HProof S Γ (.neg (.neg p)) :=
  negIntro (d.lift (fun q hq => List.mem_cons_of_mem _ hq)) (.hyp (by simp))


def iffForward (d : HProof S Γ (.iff p q)) : HProof S Γ (.imp p q) :=
  .mp d (base (.dfBi1 p q))

def iffBackward (d : HProof S Γ (.iff p q)) : HProof S Γ (.imp q p) :=
  .mp d (base (.dfBi2 p q))

def conjIntro (dp : HProof S Γ p) (dq : HProof S Γ q) : HProof S Γ (.conj p q) := by
  have hp := dp.lift (Δ := .imp p (.neg q) :: Γ) (fun r hr => List.mem_cons_of_mem _ hr)
  have hq := dq.lift (Δ := .imp p (.neg q) :: Γ) (fun r hr => List.mem_cons_of_mem _ hr)
  have hn : HProof S Γ (.neg (.imp p (.neg q))) :=
    negIntro hq (.mp hp (.hyp (by simp)))
  exact .mp hn (iffBackward (base (.dfAn p q)))

def conjLeft (d : HProof S Γ (.conj p q)) : HProof S Γ p := by
  have dn : HProof S Γ (.neg (.imp p (.neg q))) := .mp d (iffForward (base (.dfAn p q)))
  have hd := dn.lift (Δ := .neg p :: Γ) (fun r hr => List.mem_cons_of_mem _ hr)
  have hp : HProof S (p :: .neg p :: Γ) p := .hyp (by simp)
  have hnp : HProof S (p :: .neg p :: Γ) (.neg p) := .hyp (by simp)
  have hi : HProof S (.neg p :: Γ) (.imp p (.neg q)) := (explosion hp hnp _).discharge
  exact clavius (explosion hi hd p).discharge

def conjRight (d : HProof S Γ (.conj p q)) : HProof S Γ q := by
  have dn : HProof S Γ (.neg (.imp p (.neg q))) := .mp d (iffForward (base (.dfAn p q)))
  have hd := dn.lift (Δ := .neg q :: Γ) (fun r hr => List.mem_cons_of_mem _ hr)
  have hnq : HProof S (.neg q :: Γ) (.neg q) := .hyp (by simp)
  exact clavius (explosion (hnq.weaken p) hd q).discharge

def disjLeft (d : HProof S Γ p) : HProof S Γ (.neg (.conj (.neg p) (.neg q))) := by
  have hp := d.lift (Δ := .conj (.neg p) (.neg q) :: Γ) (fun r hr => List.mem_cons_of_mem _ hr)
  have hn : HProof S (.conj (.neg p) (.neg q) :: Γ) (.conj (.neg p) (.neg q)) := .hyp (by simp)
  exact negIntro hp hn.conjLeft

def disjRight (d : HProof S Γ q) : HProof S Γ (.neg (.conj (.neg p) (.neg q))) := by
  have hq := d.lift (Δ := .conj (.neg p) (.neg q) :: Γ) (fun r hr => List.mem_cons_of_mem _ hr)
  have hn : HProof S (.conj (.neg p) (.neg q) :: Γ) (.conj (.neg p) (.neg q)) := .hyp (by simp)
  exact negIntro hq hn.conjRight

def disjElim (d : HProof S Γ (.neg (.conj (.neg p) (.neg q))))
    (dp : HProof S (p :: Γ) r) (dq : HProof S (q :: Γ) r) : HProof S Γ r := by
  have hp : HProof S (p :: .neg r :: Γ) r :=
    dp.lift (fun s hs => by
      rcases List.mem_cons.1 hs with h | h
      · exact List.mem_cons.2 (Or.inl h)
      · exact List.mem_cons.2 (Or.inr (List.mem_cons_of_mem _ h)))
  have hq : HProof S (q :: .neg r :: Γ) r :=
    dq.lift (fun s hs => by
      rcases List.mem_cons.1 hs with h | h
      · exact List.mem_cons.2 (Or.inl h)
      · exact List.mem_cons.2 (Or.inr (List.mem_cons_of_mem _ h)))
  have hnp : HProof S (.neg r :: Γ) (.neg p) := negIntro hp (.hyp (by simp))
  have hnq : HProof S (.neg r :: Γ) (.neg q) := negIntro hq (.hyp (by simp))
  have hd := d.lift (Δ := .neg r :: Γ) (fun s hs => List.mem_cons_of_mem _ hs)
  exact clavius (explosion (conjIntro hnp hnq) hd r).discharge

/-- Equality reflexivity follows from ax-Pl0 and ax-7 for every term. -/
def eqRefl (t : Term N) : HProof S Γ (.equal t t) :=
  .mp (base (.axPl0 t)) (.mp (base (.axPl0 t)) (base (.ax7 (.add t .zero) t t)))

/-- Transport an implication through contraposition with explicit ax-3 trees. -/
def contrapose (d : HProof S Γ (.imp p q)) : HProof S Γ (.imp (.neg q) (.neg p)) := by
  have dd := d.lift (Δ := p :: .neg q :: Γ)
    (fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  have dq : HProof S (p :: .neg q :: Γ) q := .mp (.hyp (by simp)) dd
  have dnq : HProof S (p :: .neg q :: Γ) (.neg q) := .hyp (by simp)
  exact (negIntro dq dnq).discharge

/-- Number quantifier distribution is an inference on existing SOA proofs. -/
def allMP (x : N) (dp : HProof S Γ (.all x p))
    (di : HProof S Γ (.all x (.imp p q))) : HProof S Γ (.all x q) :=
  .mp dp (.mp di (base (.ax4 p q x)))

/-- A fresh universal guard can be discharged using ax-Tex. This is the
witness step needed for universal instantiation and equality replacement. -/
def allGuard (x : N) (t : Term N) (hx : x ∉ t.names) (hp : x ∉ p.names)
    (d : HProof S Γ (.all x (.imp (.equal (.var x) t) p))) : HProof S Γ p := by
  let eq : Formula N := .equal (.var x) t
  have contra : Proof S (.imp (.imp eq p) (.imp (.neg p) (.neg eq))) :=
    (contrapose (HProof.hyp (S := S) (Γ := [.imp eq p]) (by simp))).discharge.toProof
  have dc := (HProof.proved (Proof.gen x contra) :
    HProof S Γ (.all x (.imp (.imp eq p) (.imp (.neg p) (.neg eq)))))
  have di := allMP x d dc
  have hn : HProof S (.neg p :: Γ) (.all x (.neg p)) :=
    .mp (.hyp (by simp)) (base (.ax5 (.neg p) x hp))
  have hd := di.lift (Δ := .neg p :: Γ) (fun r hr => List.mem_cons_of_mem _ hr)
  have he := allMP x hn hd
  have hne : HProof S (.neg p :: Γ) (.neg (.all x (.neg eq))) := base (.axTex x t hx)
  exact clavius (explosion he hne p).discharge


end HProof

end Silmaril.Logic.ArithmeticToSecondOrder
