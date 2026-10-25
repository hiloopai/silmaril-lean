module

public import Silmaril.Logic.ArithmeticToSecondOrder.Induction
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace Silmaril.Logic.ArithmeticToSecondOrder

open SecondOrderArithmetic

variable {n : ℕ}

/-- Written support used to choose an eigenname absent even from bound names. -/
def support (Γ : List (Formula ℕ)) (e : Fin n → Term ℕ) : Finset ℕ :=
  Γ.toFinset.biUnion Formula.names ∪ Finset.univ.biUnion (fun i => (e i).names)

def eigenname (k h : ℕ) (Γ : List (Formula ℕ)) (e : Fin n → Term ℕ) : ℕ :=
  max (k + h) ((support Γ e).sup id) + 1

theorem eigenname_high (k h : ℕ) (Γ : List (Formula ℕ)) (e : Fin n → Term ℕ) :
    k + h < eigenname k h Γ e := by simp only [eigenname]; omega

theorem eigenname_fresh (k h : ℕ) (Γ : List (Formula ℕ)) (e : Fin n → Term ℕ) :
    eigenname k h Γ e ∉ support Γ e := by
  intro hx
  have hh := Finset.le_sup (f := id) hx
  simp only [id_eq, eigenname] at hh
  omega

theorem eigenname_param (k h : ℕ) (Γ : List (Formula ℕ)) (e : Fin n → Term ℕ)
    (i : Fin n) : eigenname k h Γ e ∉ (e i).names := by
  intro hx
  exact eigenname_fresh k h Γ e (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩))

theorem eigenname_context (k h : ℕ) (Γ : List (Formula ℕ)) (e : Fin n → Term ℕ) :
    ∀ p ∈ Γ, eigenname k h Γ e ∉ p.names := by
  intro p hp hx
  exact eigenname_fresh k h Γ e (Finset.mem_union_left _
    (Finset.mem_biUnion.mpr ⟨p, List.mem_toFinset.mpr hp, hx⟩))

theorem ParametersAvoid.extend {k h y : ℕ} {e : Fin n → Term ℕ}
    (he : ParametersAvoid k h e) (hy : k + h ≤ y) :
    ParametersAvoid k h (Fin.cases (.var y) e) := by
  intro i
  refine Fin.cases ?_ (fun j => he j) i
  intro z hz
  have hz' : z = y := by simpa [Term.names] using hz
  subst z
  exact Or.inr hy

theorem term_fresh (t : Arithmetic.Term n) (e : Fin n → Term ℕ) (x : ℕ)
    (he : ∀ i, x ∉ (e i).names) : x ∉ (term e t).names := by
  intro hx
  obtain ⟨i, hi⟩ := term_names t e x hx
  exact he i hi

/-- A bound on every formula height occurring in the source proof. -/
def bound {n : ℕ} {Γ : Arithmetic.Context n} {p : Arithmetic.Formula n}
    (d : Arithmetic.PAProof Γ p) : ℕ :=
  match d with
  | .hyp _ | .ax _ | .eqRefl _ => height p
  | .weaken _ d | .impIntro d | .botElim d | .classical d
  | .conjLeft d | .conjRight d | .disjLeft d | .disjRight d
  | .allIntro d | .allElim d _ | .exIntro _ d => max (height p) (bound d)
  | .impElim d e | .conjIntro d e | .exElim d e | .eqElim _ d e =>
    max (height p) (max (bound d) (bound e))
  | .disjElim d e f => max (height p) (max (bound d) (max (bound e) (bound f)))

theorem height_le_bound {Γ : Arithmetic.Context n} {p : Arithmetic.Formula n}
    (d : Arithmetic.PAProof Γ p) : height p ≤ bound d := by
  cases d <;> simp only [bound] <;> omega

/-- Each of PA's six basic arithmetic axioms becomes an existing SOA proof. -/
def basicProof {p : Arithmetic.Formula n} (a : Arithmetic.BasicAxiom p)
    (k : ℕ) (e : Fin n → Term ℕ) : Proof .Z2Full (formula k e p) := by
  cases a with
  | succNonzero t =>
    have hp : HProof .Z2Full [.equal (.succ (term e t)) .zero]
        (.equal (.succ (term e t)) .zero) := .hyp (by simp)
    exact (HProof.explosion hp (HProof.base (.axS0 _)) falsum).discharge.toProof
  | succInjective s t => exact .axiom (.base (.axSinj _ _))
  | addZero t => exact .axiom (.base (.axPl0 _))
  | addSucc s t => exact .axiom (.base (.axPlS _ _))
  | mulZero t => exact .axiom (.base (.axMu0 _))
  | mulSucc s t => exact .axiom (.base (.axMuS _ _))

def axiomProof {p : Arithmetic.Formula n} (a : Arithmetic.PAAxiom p)
    (k : ℕ) (e : Fin n → Term ℕ) (he : ParametersAvoid k (height p) e) :
    Proof .Z2Full (formula k e p) := by
  cases a with
  | basic a => exact basicProof a k e
  | induction p =>
    have hh : height (Arithmetic.inductionSchema p) = height p + 1 := by
      simp [Arithmetic.inductionSchema, height, Arithmetic.Formula.step]
    exact inductionProof p k (eigenname k (height p) [] e) e
      (by simpa only [hh] using he) (by have h := eigenname_high k (height p) [] e; omega)
      (eigenname_param k (height p) [] e)

/-- Compile all constructors of scoped PA natural deduction into finite SOA
Hilbert trees. A proof-height reserve prevents capture in intermediate formulas. -/
def compile {n : ℕ} {Γ : Arithmetic.Context n} {p : Arithmetic.Formula n}
    (d : Arithmetic.PAProof Γ p) (k : ℕ) (e : Fin n → Term ℕ)
    (he : ParametersAvoid k (bound d) e) :
    HProof .Z2Full (Γ.map (formula k e)) (formula k e p) :=
  match d with
  | .hyp h => .hyp (List.mem_map.mpr ⟨_, h, rfl⟩)
  | .ax a => .proved (axiomProof a k e (he.mono (height_le_bound (.ax a))))
  | .weaken h d => by
    apply (compile d k e (he.mono (by simp only [bound]; omega))).lift
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact List.mem_map.mpr ⟨r, h r hr, rfl⟩
  | .impIntro d => (compile d k e (he.mono (by simp only [bound]; omega))).discharge
  | .impElim d f => .mp (compile f k e (he.mono (by simp only [bound]; omega)))
      (compile d k e (he.mono (by simp only [bound]; omega)))
  | .botElim d => HProof.explosion (HProof.eqRefl .zero)
      (compile d k e (he.mono (by simp only [bound]; omega))) _
  | .classical (φ := p) d => by
    let ctx := Γ.map (formula k e)
    have dn : HProof .Z2Full (.neg (formula k e p) :: ctx) (.neg (formula k e p)) := .hyp (by simp)
    have hp : HProof .Z2Full (formula k e p :: .neg (formula k e p) :: ctx)
        (formula k e p) := .hyp (by simp)
    have hn := dn.lift (Δ := formula k e p :: .neg (formula k e p) :: ctx)
      (fun q hq => List.mem_cons_of_mem _ hq)
    have ni := (HProof.explosion hp hn falsum).discharge
    have dd := (compile d k e (he.mono (by simp only [bound]; omega))).lift
      (Δ := .neg (formula k e p) :: ctx) (fun q hq => List.mem_cons_of_mem _ hq)
    have hb : HProof .Z2Full (.neg (formula k e p) :: ctx) falsum := .mp ni dd
    exact HProof.clavius (HProof.explosion (HProof.eqRefl .zero) hb (formula k e p)).discharge
  | .conjIntro d f => HProof.conjIntro
      (compile d k e (he.mono (by simp only [bound]; omega)))
      (compile f k e (he.mono (by simp only [bound]; omega)))
  | .conjLeft d => (compile d k e (he.mono (by simp only [bound]; omega))).conjLeft
  | .conjRight d => (compile d k e (he.mono (by simp only [bound]; omega))).conjRight
  | .disjLeft d => (compile d k e (he.mono (by simp only [bound]; omega))).disjLeft
  | .disjRight d => (compile d k e (he.mono (by simp only [bound]; omega))).disjRight
  | .disjElim d f g => HProof.disjElim
      (compile d k e (he.mono (by simp only [bound]; omega)))
      (compile f k e (he.mono (by simp only [bound]; omega)))
      (compile g k e (he.mono (by simp only [bound]; omega)))
  | .allIntro (φ := p) d => by
    let ctx := Γ.map (formula k e)
    let x := k + height p
    let y := eigenname k (bound d) ctx e
    have hy := eigenname_high k (bound d) ctx e
    have hph := height_le_bound d
    have hx : x < k ∨ k + height p ≤ x := Or.inr (by omega)
    have hy' : y < k ∨ k + height p ≤ y := Or.inr (by omega)
    have hxy : x ≠ y := by omega
    have hex : ∀ i, x ∉ (e i).names :=
      (he.mono (show height p + 1 ≤ bound (.allIntro d) by simp only [bound, height]; omega)).fresh
    have hey := eigenname_param k (bound d) ctx e
    have hc : HProof .Z2Full ctx (formula k (Fin.cases (.var y) e) p) := by
      simpa only [List.map_map, Function.comp_def, formula_shift] using
        compile d k (Fin.cases (.var y) e)
          ((he.mono (by simp only [bound]; omega)).extend (by omega))
    have hg := hc.generalize y (eigenname_context k (bound d) ctx e)
    exact .mp hg (.proved (allRename p k x y e hxy hx hy' hex hey))
  | .allElim (φ := p) d t => by
    let x := k + height p
    have hx : x < k ∨ k + height p ≤ x := Or.inr (by omega)
    have hb : height p + 1 ≤ bound (.allElim d t) := by
      have h := height_le_bound d
      simp only [height] at h
      simp only [bound]
      omega
    have hex := (he.mono hb).fresh
    have ht := term_avoid t (he.mono (show height p ≤ bound (.allElim d t) by omega))
    have di := allInstantiate (S := .Z2Full) p k x e (term e t) hx hex (term_fresh t e x hex) ht
    simpa only [formula_inst] using HProof.mp
      (compile d k e (he.mono (by simp only [bound]; omega))) (HProof.proved di)
  | .exIntro (φ := p) t d => by
    let x := k + height p
    have hx : x < k ∨ k + height p ≤ x := Or.inr (by omega)
    have hb : height p + 1 ≤ bound (.exIntro t d) := by simp only [bound, height]; omega
    have hex := (he.mono hb).fresh
    have ht := term_avoid t (he.mono (show height p ≤ bound (.exIntro t d) by omega))
    have di := exInstantiate (S := .Z2Full) p k x e (term e t) hx hex (term_fresh t e x hex) ht
    have hd : HProof .Z2Full (Γ.map (formula k e)) (formula k (Fin.cases (term e t) e) p) := by
      simpa only [formula_inst] using compile d k e (he.mono (by simp only [bound]; omega))
    exact .mp hd (.proved di)
  | .exElim (φ := p) (ψ := q) d f => by
    let ctx := Γ.map (formula k e)
    let x := k + height p
    let y := eigenname k (max (bound f) (height p)) ctx e
    have hy := eigenname_high k (max (bound f) (height p)) ctx e
    have hx : x < k ∨ k + height p ≤ x := Or.inr (by omega)
    have hy' : y < k ∨ k + height p ≤ y := Or.inr (by omega)
    have hxy : y ≠ x := by omega
    have hb : height p + 1 ≤ bound (.exElim d f) := by
      have h := height_le_bound d
      simp only [height] at h
      simp only [bound]
      omega
    have hex := (he.mono hb).fresh
    have hey := eigenname_param k (max (bound f) (height p)) ctx e
    have hf : HProof .Z2Full (formula k (Fin.cases (.var y) e) p :: ctx) (formula k e q) := by
      simpa only [List.map_cons, List.map_map, Function.comp_def, formula_shift] using
        compile f k (Fin.cases (.var y) e)
          ((he.mono (by simp only [bound]; omega)).extend (by omega))
    have hq : y ∉ (formula k e q).names := by
      have h := height_le_bound f
      simp only [Arithmetic.Formula.shift, height_rename] at h
      exact formula_fresh q k y e (Or.inr (by omega)) hey
    have hd := HProof.mp (compile d k e (he.mono (by simp only [bound]; omega)))
      (HProof.proved (exRename p k y x e hxy hy' hx hey hex))
    exact HProof.existsEliminate y hq hd
      (hf.discharge.generalize y (eigenname_context k (max (bound f) (height p)) ctx e))
  | .eqRefl t => HProof.eqRefl (term e t)
  | .eqElim (s := s) (t := t) p d f => by
    have hb : height p ≤ bound (.eqElim p d f) := by
      simp only [bound, Arithmetic.Formula.inst, height_subst]
      omega
    have hs := term_avoid s (he.mono hb)
    have ht := term_avoid t (he.mono hb)
    have di := (replacement (S := .Z2Full) p k e (term e s) (term e t) hs ht).forward
    have heq := compile d k e (he.mono (by simp only [bound]; omega))
    have hf : HProof .Z2Full (Γ.map (formula k e)) (formula k (Fin.cases (term e s) e) p) := by
      simpa only [formula_inst] using compile f k e (he.mono (by simp only [bound]; omega))
    simpa only [formula_inst] using HProof.mp hf (HProof.mp heq (HProof.proved di))
termination_by structural d

/-- The actual closed PA-to-full-SOA proof map. -/
def paToSOA {p : Arithmetic.Sentence} (d : Arithmetic.PAProof [] p) :
    Proof .Z2Full (sentence p) :=
  (compile d 0 Fin.elim0 (fun i => Fin.elim0 i)).toProof


end Silmaril.Logic.ArithmeticToSecondOrder
