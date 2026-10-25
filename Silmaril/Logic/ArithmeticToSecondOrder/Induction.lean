module

public import Silmaril.Logic.Arithmetic.Peano
public import Silmaril.Logic.ArithmeticToSecondOrder.Quantifiers

@[expose] public section

namespace Silmaril.Logic.ArithmeticToSecondOrder

open SecondOrderArithmetic

variable {n : ℕ}

/-- Ordinary arithmetic induction is derived from the target's existing
pointwise full-induction schema, including arbitrary parameter terms. -/
def inductionProof (p : Arithmetic.Formula (n + 1)) (k y : ℕ)
    (e : Fin n → Term ℕ) (he : ParametersAvoid k (height p + 1) e)
    (hy : k + height p + 1 ≤ y) (hey : ∀ i, y ∉ (e i).names) :
    Proof .Z2Full (formula k e (Arithmetic.inductionSchema p)) := by
  let x := k + height p
  let px := formula k (Fin.cases (.var x) e) p
  let py := formula k (Fin.cases (.var y) e) p
  let psy := formula k (Fin.cases (.succ (.var y)) e) p
  let p0 := formula k (Fin.cases .zero e) p
  let step : Formula ℕ := .all x (formula k (Fin.cases (.var x) e) (.imp p p.step))
  let gy : Formula ℕ := .all x (.imp (.equal (.var x) (.var y)) px)
  let gsy : Formula ℕ := .all x (.imp (.equal (.var x) (.succ (.var y))) px)
  have hx : x < k ∨ k + height p ≤ x := Or.inr (by omega)
  have hy' : y < k ∨ k + height p ≤ y := Or.inr (by omega)
  have hxy : x ≠ y := by omega
  have ht : Avoid k (height p) (Term.var y).names := by
    intro z hz
    have hz' : z = y := by simpa [Term.names] using hz
    subst z
    exact hy'
  have htx : x ∉ (Term.var y).names := by simp [Term.names, hxy]
  have h0 : Avoid k (height p) (Term.zero : Term ℕ).names := by simp [Avoid, Term.names]
  have hx0 : x ∉ (Term.zero : Term ℕ).names := by simp [Term.names]
  have de := guardEliminate (S := .Z2Full) p k x e (.var y) hx he.fresh htx ht
  have di := guardIntroduce (S := .Z2Full) p k x e (.succ (.var y)) hx he.fresh htx ht
  have hstep : height (.imp p p.step) = height p := by
    simp [height, Arithmetic.Formula.step]
  have dt := allInstantiate (S := .Z2Full) (.imp p p.step) k x e (.var y)
    (by simpa only [hstep] using hx) he.fresh htx (by simpa only [hstep] using ht)
  have hp : HProof .Z2Full [gy, step] py := .mp (.hyp (p := gy) (by simp)) (.proved de)
  have dst : HProof .Z2Full [gy, step] (.imp py psy) := by
    simpa only [formula, formula_step] using
      (HProof.mp (HProof.hyp (p := step) (by simp)) (HProof.proved dt))
  have hsy : HProof .Z2Full [gy, step] psy := .mp hp dst
  have dsy : HProof .Z2Full [gy, step] gsy := .mp hsy (.proved di)
  have hf : y ∉ (formula k (Fin.cases (.var x) e) p).names := by
    apply formula_fresh p k y _ hy'
    intro i
    refine Fin.cases ?_ (fun j => hey j) i
    simpa [Term.names] using Ne.symm hxy
  have hfs : y ∉ step.names := by
    dsimp [step]
    simp only [Formula.names, Finset.mem_insert, not_or]
    refine ⟨Ne.symm hxy, ?_⟩
    apply formula_fresh (.imp p p.step) k y _ (by simpa only [hstep] using hy')
    intro i
    refine Fin.cases ?_ (fun j => hey j) i
    simpa [Term.names] using Ne.symm hxy
  have ds : Proof .Z2Full (.imp step (.all y (.imp gy gsy))) :=
    (dsy.discharge.generalize y (by simpa using hfs)).discharge.toProof
  have db := guardIntroduce (S := .Z2Full) p k x e .zero hx he.fresh hx0 h0
  have hg : HProof .Z2Full [.conj p0 step] (.conj p0 step) := .hyp (by simp)
  have hb : HProof .Z2Full [.conj p0 step] (.all x (.imp (.equal (.var x) .zero) px)) :=
    .mp hg.conjLeft (.proved db)
  have hs : HProof .Z2Full [.conj p0 step] (.all y (.imp gy gsy)) := .mp hg.conjRight (.proved ds)
  have ax : HProof .Z2Full [.conj p0 step] (.induction x y px) :=
    .proved (.axiom (.fullInd x y px (Or.inr rfl) hxy hf))
  have result := (HProof.mp hs (HProof.mp hb ax)).discharge.toProof
  dsimp [p0, step, x, px] at result
  simpa only [Arithmetic.inductionSchema, formula, formula_inst, term, hstep] using result

end Silmaril.Logic.ArithmeticToSecondOrder
