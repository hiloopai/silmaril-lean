module

public import Silmaril.Logic.HOLLight.Semantics.Term

@[expose] public section

/-!
# Semantic type instantiation

Type instantiation reassigns the schematic type variables and pulls free
valuations back along `(name, type) ↦ (name, substituted type)`. Distinct free
variables may therefore merge. No injectivity assumption on substitution is
used here.
-/

namespace Silmaril.Logic.HOLLight

universe u

namespace TypeSubstitution

def valuation {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u})
    (σ : Nat → Ty) : TypeValuation.{u} := fun i => (σ i).denote M.toTypeModel ρ

theorem value_eq {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u})
    (σ : Nat → Ty) (A : Ty) :
    (Value M (valuation M ρ σ) A).val = (Value M ρ (A.subst σ)).val :=
  congrArg Subtype.val (Ty.denote_subst M.toTypeModel ρ σ A).symm

def forward {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {σ : Nat → Ty} {A : Ty} (x : Value M (valuation M ρ σ) A) : Value M ρ (A.subst σ) :=
  cast (value_eq M ρ σ A) x

def backward {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {σ : Nat → Ty} {A : Ty} (x : Value M ρ (A.subst σ)) : Value M (valuation M ρ σ) A :=
  cast (value_eq M ρ σ A).symm x

theorem forward_heq {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {σ : Nat → Ty} {A : Ty} (x : Value M (valuation M ρ σ) A) :
    HEq x (forward x) := (cast_heq _ _).symm

theorem backward_heq {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {σ : Nat → Ty} {A : Ty} (x : Value M ρ (A.subst σ)) :
    HEq (backward (M := M) (ρ := ρ) (σ := σ) (A := A) x) x := cast_heq _ _

theorem map_lookup {Γ : List Ty} {i : Nat} {A : Ty} (σ : Nat → Ty)
    (h : Γ[i]? = some A) : (Γ.map (Ty.subst σ))[i]? = some (A.subst σ) := by
  simp [List.getElem?_map, h]

def freeEnv {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    (σ : Nat → Ty) (ν : FreeEnv M ρ) : FreeEnv M (valuation M ρ σ) :=
  fun n A => backward (ν n (A.subst σ))

def boundEnv {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    (σ : Nat → Ty) {Γ : List Ty} (η : BoundEnv M ρ (Γ.map (Ty.subst σ))) :
    BoundEnv M (valuation M ρ σ) Γ :=
  fun i A h => backward (η i (A.subst σ) (map_lookup σ h))

@[simp] theorem boundEnv_empty {sig : Signature} {M : Model.{u} sig}
    {ρ : TypeValuation.{u}} (σ : Nat → Ty) :
    boundEnv (M := M) (ρ := ρ) σ (Γ := []) BoundEnv.empty = BoundEnv.empty := by
  funext i A h
  nomatch h

theorem heq_apply {A B C D : Type u} (hA : A = C) (hB : B = D)
    {f : A → B} {g : C → D} (hf : HEq f g) {x : A} {y : C} (hx : HEq x y) :
    HEq (f x) (g y) := by
  cases hA
  cases hB
  cases hf
  cases hx
  rfl

theorem eq_heq {A B : Carrier.{u}} (h : A = B) : HEq (Carrier.eq A) (Carrier.eq B) := by
  cases h
  rfl

theorem choose_heq {A B : Carrier.{u}} (h : A = B) :
    HEq (Carrier.choose A) (Carrier.choose B) := by
  cases h
  rfl

theorem constant_heq {sig : Signature} (M : Model.{u} sig)
    (ρ : TypeValuation.{u}) (σ : Nat → Ty) {name : Nat} {s : Scheme}
    (lookup : sig.consts[name]? = some s) (hscoped : s.body.Scoped s.arity)
    (args : List Ty) (arity : args.length = s.arity) :
    HEq (M.constantInstance (valuation M ρ σ) lookup hscoped args arity)
      (M.constantInstance ρ lookup hscoped (args.map (Ty.subst σ))
        (by simpa using arity)) := by
  unfold Model.constantInstance
  apply (cast_heq _ _).trans
  apply HEq.trans ?_ (cast_heq _ _).symm
  have hargs : args.map (Ty.denote M.toTypeModel (valuation M ρ σ)) =
      (args.map (Ty.subst σ)).map (Ty.denote M.toTypeModel ρ) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro A _
    exact (Ty.denote_subst M.toTypeModel ρ σ A).symm
  have hc : ∀ xs ys, xs = ys →
      HEq (M.constant name s lookup xs) (M.constant name s lookup ys) := by
    intro xs ys h
    cases h
    rfl
  exact hc _ _ hargs

end TypeSubstitution

theorem ConstEval.tySubst {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {σ : Nat → Ty} (hσ : ∀ i, (σ i).WellFormed sig.tyOps)
    {c : Const} {A : Ty} {value : Value M (TypeSubstitution.valuation M ρ σ) A}
    (evaluation : ConstEval M (TypeSubstitution.valuation M ρ σ) c A value) :
    ∃ value', ConstEval M ρ (c.tySubst σ) (A.subst σ) value' ∧ HEq value value' := by
  cases evaluation with
  | @eq A wf =>
    exact ⟨_, .eq (wf.subst hσ),
      TypeSubstitution.eq_heq (Ty.denote_subst M.toTypeModel ρ σ A).symm⟩
  | @select A wf =>
    exact ⟨_, .select (wf.subst hσ),
      TypeSubstitution.choose_heq (Ty.denote_subst M.toTypeModel ρ σ A).symm⟩
  | @user name s args lookup scheme arity wellFormed =>
    have hi := Ty.subst_instantiate scheme.2 arity σ
    simp only [Const.tySubst]
    rw [hi]
    refine ⟨_, .user lookup scheme (by simpa using arity) ?_, ?_⟩
    · intro A hA
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
      exact (wellFormed B hB).subst hσ
    · exact TypeSubstitution.constant_heq M ρ σ lookup scheme.2 args arity

theorem Eval.tySubst {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {σ : Nat → Ty} (hσ : ∀ i, (σ i).WellFormed sig.tyOps)
    {ν : FreeEnv M (TypeSubstitution.valuation M ρ σ)} {ν' : FreeEnv M ρ}
    (hν : ∀ n A, HEq (ν n A) (ν' n (A.subst σ)))
    {Γ : List Ty} {η : BoundEnv M (TypeSubstitution.valuation M ρ σ) Γ}
    {t : Tm} {A : Ty} {value : Value M (TypeSubstitution.valuation M ρ σ) A}
    (evaluation : Eval M (TypeSubstitution.valuation M ρ σ) ν η t A value) :
    ∀ (η' : BoundEnv M ρ (Γ.map (Ty.subst σ))),
      (∀ i B h, HEq (η i B h) (η' i (B.subst σ) (TypeSubstitution.map_lookup σ h))) →
      ∃ value', Eval M ρ ν' η' (t.tySubst σ) (A.subst σ) value' ∧ HEq value value' := by
  induction evaluation with
  | bvar η lookup wf =>
    intro η' compatible
    exact ⟨_, .bvar η' (TypeSubstitution.map_lookup σ lookup) (wf.subst hσ),
      compatible _ _ lookup⟩
  | fvar η name wf =>
    intro η' _
    exact ⟨_, .fvar η' name (wf.subst hσ), hν name _⟩
  | const η hc =>
    intro η' _
    obtain ⟨v, hv, heq⟩ := hc.tySubst hσ
    exact ⟨v, .const η' hv, heq⟩
  | @app Γ η A B f x function argument hf hx ihf ihx =>
    intro η' compatible
    obtain ⟨f', hf', heqf⟩ := ihf η' compatible
    obtain ⟨x', hx', heqx⟩ := ihx η' compatible
    exact ⟨f' x', .app hf' hx',
      TypeSubstitution.heq_apply (TypeSubstitution.value_eq M ρ σ A)
        (TypeSubstitution.value_eq M ρ σ B) heqf heqx⟩
  | @lam Γ η A B body wf function hbody ih =>
    intro η' compatible
    refine ⟨TypeSubstitution.forward function, .lam (wf.subst hσ) ?_,
      TypeSubstitution.forward_heq function⟩
    intro y
    let x : Value M (TypeSubstitution.valuation M ρ σ) A := TypeSubstitution.backward y
    have hxy : HEq x y := TypeSubstitution.backward_heq y
    have env : ∀ i C h, HEq (η.extend x i C h)
        ((η'.extend y) i (C.subst σ) (TypeSubstitution.map_lookup σ h)) := by
      intro i C h
      cases i with
      | zero =>
        have hc : A = C := Option.some.inj h
        cases hc
        exact hxy
      | succ i => exact compatible i C h
    obtain ⟨v, hv, heq⟩ := ih x (η'.extend y) env
    have hv' : v = TypeSubstitution.forward function y :=
      eq_of_heq (heq.symm.trans (TypeSubstitution.heq_apply
        (TypeSubstitution.value_eq M ρ σ A) (TypeSubstitution.value_eq M ρ σ B)
        (TypeSubstitution.forward_heq function) hxy))
    exact hv' ▸ hv

/-- The ordinary instantiation theorem, for valuations pulled back from the
target. Pullback automatically identifies free variables merged by `σ`. -/
theorem Eval.tySubst_pullback {sig : Signature} {M : Model.{u} sig}
    {ρ : TypeValuation.{u}} {σ : Nat → Ty} (hσ : ∀ i, (σ i).WellFormed sig.tyOps)
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ (Γ.map (Ty.subst σ))}
    {t : Tm} {A : Ty} {value : Value M (TypeSubstitution.valuation M ρ σ) A}
    (evaluation : Eval M (TypeSubstitution.valuation M ρ σ)
      (TypeSubstitution.freeEnv σ ν) (TypeSubstitution.boundEnv σ η) t A value) :
    ∃ value', Eval M ρ ν η (t.tySubst σ) (A.subst σ) value' ∧ HEq value value' :=
  evaluation.tySubst hσ (fun n B => TypeSubstitution.backward_heq (ν n (B.subst σ)))
    η (fun i B h => TypeSubstitution.backward_heq
      (η i (B.subst σ) (TypeSubstitution.map_lookup σ h)))

end Silmaril.Logic.HOLLight
