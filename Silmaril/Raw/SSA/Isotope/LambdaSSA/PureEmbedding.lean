module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Embedding
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Purity

/-! # Restricted primitive simulations and environment agreement

The existing syntactic purity predicate certifies every primitive occurrence.
A simulation may therefore require that certificate at every executed step.
Environment transport only needs agreement at variables actually used by the
expression, leaving unrelated slots available for other value representations.
-/

@[expose] public section
universe u v a b s t e
namespace Silmaril.Isotope.LambdaSSA

namespace Tm
variable {Φ : Type u} {Ψ : Type v}

/-- A free variable occurrence, accounting for every local binder. -/
def UsesVar : Tm Φ → Nat → Prop
  | .var j, i => i = j
  | .op _ x, i | .inl x, i | .inr x, i | .abort x, i => x.UsesVar i
  | .let₁ x body, i => x.UsesVar i ∨ body.UsesVar (i + 1)
  | .pair x y, i => x.UsesVar i ∨ y.UsesVar i
  | .unit, _ => False
  | .let₂ x body, i => x.UsesVar i ∨ body.UsesVar (i + 2)
  | .case x left right, i => x.UsesVar i ∨ left.UsesVar (i + 1) ∨ right.UsesVar (i + 1)

@[simp] theorem usesVar_mapInstr (f : Φ → Ψ) (term : Tm Φ) (i : Nat) :
    (term.mapInstr f).UsesVar i ↔ term.UsesVar i := by
  induction term generalizing i <;> simp_all [mapInstr, UsesVar]

theorem Pure.mapInstr {ε : Type e} {ε' : Type t} [HasEff Φ ε] [HasEff Ψ ε']
    {pureEff : ε} {pureEff' : ε'} (f : Φ → Ψ)
    (preserves : ∀ i, IsPure pureEff i → IsPure pureEff' (f i))
    {term : Tm Φ} (h : term.Pure pureEff) : (term.mapInstr f).Pure pureEff' := by
  induction h with
  | var => exact .var
  | op hp _ ih => exact .op (preserves _ hp) ih
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | unit => exact .unit
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .abort ih

end Tm
namespace Semantics.Tm
variable {Φ : Type u} {Ψ : Type v} {α : Type a} {β : Type b} {σ : Type s} {τ : Type t}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}
variable {instr' : Ψ → Value β → τ → Value β → τ → Prop}

/-- Restrict each executed primitive by its syntactic purity certificate. -/
theorem Eval.restrict_pure {ε : Type e} [HasEff Φ ε] {pureEff : ε}
    {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (h : Eval instr env term before value after) (pure : term.Pure pureEff) :
    Eval (fun i x s y t => IsPure pureEff i ∧ instr i x s y t) env term before value after := by
  induction h with
  | var => exact .var
  | op _ step ih => cases pure with | op hp ha => exact .op (ih ha) ⟨hp, step⟩
  | let₁ _ _ ih₁ ih₂ => cases pure with | let₁ h₁ h₂ => exact .let₁ (ih₁ h₁) (ih₂ h₂)
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => cases pure with | pair h₁ h₂ => exact .pair (ih₁ h₁) (ih₂ h₂)
  | let₂ _ _ ih₁ ih₂ => cases pure with | let₂ h₁ h₂ => exact .let₂ (ih₁ h₁) (ih₂ h₂)
  | inl _ ih => cases pure with | inl h => exact .inl (ih h)
  | inr _ ih => cases pure with | inr h => exact .inr (ih h)
  | case_inl _ _ ih₁ ih₂ => cases pure with | case h₁ h₂ _ => exact .case_inl (ih₁ h₁) (ih₂ h₂)
  | case_inr _ _ ih₁ ih₂ => cases pure with | case h₁ _ h₂ => exact .case_inr (ih₁ h₁) (ih₂ h₂)

theorem Eval.state_eq (preserves : ∀ i x before y after, instr i x before y after → after = before)
    {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (h : Eval instr env term before value after) : after = before := by
  induction h with
  | var | unit => rfl
  | op _ step ih => exact (preserves _ _ _ _ _ step).trans ih
  | let₁ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂
  | case_inl _ _ ih₁ ih₂ | case_inr _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | inl _ ih | inr _ ih => exact ih

theorem Eval.state_eq_of_pure {ε : Type e} [HasEff Φ ε] {pureEff : ε}
    (preserves : ∀ i x before y after, IsPure pureEff i → instr i x before y after → after = before)
    {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (h : Eval instr env term before value after) (pure : term.Pure pureEff) : after = before :=
  (h.restrict_pure pure).state_eq (fun _ _ _ _ _ step => preserves _ _ _ _ _ step.1 step.2)

theorem Eval.embed_pure {ε : Type e} [HasEff Φ ε] {pureEff : ε}
    (instruction : Φ → Ψ) (atom : α → β) (state : σ → τ)
    (step : ∀ i input before output after, IsPure pureEff i → instr i input before output after →
      instr' (instruction i) (input.map atom) (state before) (output.map atom) (state after))
    {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (h : Eval instr env term before value after) (pure : term.Pure pureEff) :
    Eval instr' (mapEnv atom env) (term.mapInstr instruction)
      (state before) (value.map atom) (state after) :=
  (h.restrict_pure pure).embed instruction atom state (fun _ _ _ _ _ h => step _ _ _ _ _ h.1 h.2)

/-- Renaming into a mixed environment only checks free variables of this term. -/
theorem Eval.rename_on {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (h : Eval instr env term before value after) {env' : Env α} {ρ : Nat → Nat}
    (agree : ∀ i, term.UsesVar i → env' (ρ i) = env i) :
    Eval instr env' (term.rename ρ) before value after := by
  induction h generalizing env' ρ with
  | @var env i state =>
    change Eval instr env' (.var (ρ i)) state (env i) state
    rw [← agree i rfl]
    exact .var
  | op _ step ih => exact .op (ih agree) step
  | let₁ _ _ ih₁ ih₂ =>
    refine .let₁ (ih₁ (fun i hi => agree i (Or.inl hi))) (ih₂ ?_)
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact agree i (Or.inr hi)
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ (fun i hi => agree i (Or.inl hi))) (ih₂ (fun i hi => agree i (Or.inr hi)))
  | let₂ _ _ ih₁ ih₂ =>
    refine .let₂ (ih₁ (fun i hi => agree i (Or.inl hi))) (ih₂ ?_)
    intro i hi
    cases i with
    | zero => rfl
    | succ i => cases i with
      | zero => rfl
      | succ i => exact agree i (Or.inr hi)
  | inl _ ih => exact .inl (ih agree)
  | inr _ ih => exact .inr (ih agree)
  | case_inl _ _ ih₁ ih₂ =>
    refine .case_inl (ih₁ (fun i hi => agree i (Or.inl hi))) (ih₂ ?_)
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact agree i (Or.inr (Or.inl hi))
  | case_inr _ _ ih₁ ih₂ =>
    refine .case_inr (ih₁ (fun i hi => agree i (Or.inl hi))) (ih₂ ?_)
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact agree i (Or.inr (Or.inr hi))

theorem Eval.congr_env_on {env env' : Env α} {term : LambdaSSA.Tm Φ}
    {before after : σ} {value : Value α} (h : Eval instr env term before value after)
    (agree : ∀ i, term.UsesVar i → env' i = env i) : Eval instr env' term before value after := by
  have renamed := h.rename_on (ρ := id) agree
  simpa only [LambdaSSA.Tm.rename_id] using renamed

end Semantics.Tm
end Silmaril.Isotope.LambdaSSA
