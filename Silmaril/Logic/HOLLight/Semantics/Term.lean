module

public import Silmaril.Logic.HOLLight.Typing
public import Silmaril.Logic.HOLLight.Semantics.Type

@[expose] public section

/-!
# Denotation of well-typed terms

This relation is the graph of mathematical denotation, not an executable
evaluator. It quantifies over arbitrary free valuations and full function
spaces. The meanings of user constants depend only on their declared semantic
type arguments, which is essential for type-instantiation soundness.
-/

namespace Silmaril.Logic.HOLLight

universe u

structure Model (sig : Signature) extends TypeModel.{u} where
  constant : (name : Nat) → (scheme : Scheme) → sig.consts[name]? = some scheme →
    (args : List Carrier.{u}) → scheme.body.denote toTypeModel (Carrier.assignment args)

abbrev Value {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u}) (A : Ty) :=
  A.denote M.toTypeModel ρ

abbrev FreeEnv {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u}) :=
  (name : Nat) → (A : Ty) → Value M ρ A

abbrev BoundEnv {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u})
    (Γ : List Ty) := (i : Nat) → (A : Ty) → Γ[i]? = some A → Value M ρ A

namespace BoundEnv

def empty {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}} :
    BoundEnv M ρ [] := fun _ _ h => nomatch h

def extend {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {Γ : List Ty} {A : Ty} (x : Value M ρ A) (η : BoundEnv M ρ Γ) : BoundEnv M ρ (A :: Γ)
  | 0, B, h => by
      have eq : A = B := Option.some.inj h
      exact eq ▸ x
  | i + 1, B, h => η i B h

@[simp] theorem extend_zero {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {Γ : List Ty} {A : Ty} (x : Value M ρ A) (η : BoundEnv M ρ Γ) :
    extend x η 0 A rfl = x := rfl

@[simp] theorem extend_succ {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {Γ : List Ty} {A B : Ty} (x : Value M ρ A) (η : BoundEnv M ρ Γ)
    (i : Nat) (h : Γ[i]? = some B) : extend x η (i + 1) B h = η i B h := rfl

end BoundEnv

namespace Model

/-- The chosen value of a declared constant instance, transported from its scheme. -/
noncomputable def constantInstance {sig : Signature} (M : Model.{u} sig)
    (ρ : TypeValuation.{u}) {name : Nat} {s : Scheme}
    (lookup : sig.consts[name]? = some s) (hscoped : s.body.Scoped s.arity)
    (args : List Ty) (arity : args.length = s.arity) : Value M ρ (s.body.instantiate args) :=
  cast (congrArg Subtype.val (Ty.denote_instantiate M.toTypeModel ρ hscoped arity).symm)
    (M.constant name s lookup (args.map (Ty.denote M.toTypeModel ρ)))

end Model

inductive ConstEval {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u}) :
    (c : Const) → (A : Ty) → Value M ρ A → Prop where
  | eq {A : Ty} (wf : A.WellFormed sig.tyOps) :
      ConstEval M ρ (.eq A) (.arr A (.arr A .bool)) (Carrier.eq (A.denote M.toTypeModel ρ))
  | select {A : Ty} (wf : A.WellFormed sig.tyOps) :
      ConstEval M ρ (.select A) (.arr (.arr A .bool) A)
        (Carrier.choose (A.denote M.toTypeModel ρ))
  | user {name : Nat} {s : Scheme} {args : List Ty}
      (lookup : sig.consts[name]? = some s) (scheme : s.WellFormed sig.tyOps)
      (arity : args.length = s.arity) (wellFormed : ∀ A ∈ args, A.WellFormed sig.tyOps) :
      ConstEval M ρ (.user name args) (s.body.instantiate args)
        (M.constantInstance ρ lookup scheme.2 args arity)

inductive Eval {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u})
    (ν : FreeEnv M ρ) : {Γ : List Ty} → BoundEnv M ρ Γ →
    (t : Tm) → (A : Ty) → Value M ρ A → Prop where
  | bvar {Γ : List Ty} (η : BoundEnv M ρ Γ) {i : Nat} {A : Ty}
      (lookup : Γ[i]? = some A) (wf : A.WellFormed sig.tyOps) :
      Eval M ρ ν η (.bvar i) A (η i A lookup)
  | fvar {Γ : List Ty} (η : BoundEnv M ρ Γ) (name : Nat) {A : Ty}
      (wf : A.WellFormed sig.tyOps) : Eval M ρ ν η (.fvar name A) A (ν name A)
  | const {Γ : List Ty} (η : BoundEnv M ρ Γ) {c : Const} {A : Ty} {value : Value M ρ A} :
      ConstEval M ρ c A value → Eval M ρ ν η (.const c) A value
  | app {Γ : List Ty} {η : BoundEnv M ρ Γ} {A B : Ty} {f x : Tm}
      {function : Value M ρ (.arr A B)} {argument : Value M ρ A} :
      Eval M ρ ν η f (.arr A B) function → Eval M ρ ν η x A argument →
      Eval M ρ ν η (.app f x) B (function argument)
  | lam {Γ : List Ty} {η : BoundEnv M ρ Γ} {A B : Ty} {body : Tm}
      (wf : A.WellFormed sig.tyOps) {function : Value M ρ (.arr A B)} :
      (∀ x, Eval M ρ ν (η.extend x) body B (function x)) →
      Eval M ρ ν η (.lam A body) (.arr A B) function

theorem ConstEval.typing {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {c : Const} {A : Ty} {value : Value M ρ A} (h : ConstEval M ρ c A value) :
    c.HasType sig A := by
  cases h with
  | eq wf => exact .eq wf
  | select wf => exact .select wf
  | user lookup scheme arity wf => exact .user lookup scheme arity wf

theorem Const.HasType.eval_exists {sig : Signature} (M : Model.{u} sig)
    (ρ : TypeValuation.{u}) {c : Const} {A : Ty} (h : c.HasType sig A) :
    ∃ value, ConstEval M ρ c A value := by
  cases h with
  | eq wf => exact ⟨_, .eq wf⟩
  | select wf => exact ⟨_, .select wf⟩
  | user lookup scheme arity wf => exact ⟨_, .user lookup scheme arity wf⟩

theorem Eval.typing {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
    {t : Tm} {A : Ty} {value : Value M ρ A} (h : Eval M ρ ν η t A value) :
    HasType sig Γ t A := by
  induction h with
  | bvar _ lookup wf => exact .bvar lookup wf
  | fvar _ n wf => exact .fvar n wf
  | const _ h => exact .const h.typing
  | app _ _ ihf ihx => exact .app ihf ihx
  | @lam Γ η A B body wf f h ih =>
      exact .lam wf (ih (Classical.choice (A.denote M.toTypeModel ρ).property))

theorem HasType.eval_exists {sig : Signature} (M : Model.{u} sig)
    (ρ : TypeValuation.{u}) (ν : FreeEnv M ρ) {Γ : List Ty}
    {t : Tm} {A : Ty} (h : HasType sig Γ t A) (η : BoundEnv M ρ Γ) :
    ∃ value, Eval M ρ ν η t A value := by
  induction h with
  | bvar lookup wf => exact ⟨_, .bvar η lookup wf⟩
  | fvar n wf => exact ⟨_, .fvar η n wf⟩
  | const hc =>
      obtain ⟨value, hvalue⟩ := hc.eval_exists M ρ
      exact ⟨value, .const η hvalue⟩
  | app hf hx ihf ihx =>
      obtain ⟨f, hfv⟩ := ihf η
      obtain ⟨x, hxv⟩ := ihx η
      exact ⟨f x, .app hfv hxv⟩
  | lam wf hb ih =>
      classical
      exact ⟨fun x => Classical.choose (ih (η.extend x)),
        .lam wf (fun x => Classical.choose_spec (ih (η.extend x)))⟩

theorem ConstEval.heq {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {c : Const} {A B : Ty} {x : Value M ρ A} {y : Value M ρ B}
    (hx : ConstEval M ρ c A x) (hy : ConstEval M ρ c B y) : HEq x y := by
  cases hx with
  | eq wf => cases hy; rfl
  | select wf => cases hy; rfl
  | user lookup scheme arity wf =>
      cases hy with
      | user lookup' scheme' arity' wf' =>
          have same := Option.some.inj (lookup.symm.trans lookup')
          cases same
          rfl

theorem ConstEval.unique {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {c : Const} {A : Ty} {x y : Value M ρ A}
    (hx : ConstEval M ρ c A x) (hy : ConstEval M ρ c A y) : x = y :=
  eq_of_heq (hx.heq hy)

theorem Eval.unique {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
    {t : Tm} {A : Ty} {x y : Value M ρ A}
    (hx : Eval M ρ ν η t A x) (hy : Eval M ρ ν η t A y) : x = y := by
  induction hx with
  | bvar _ lookup wf => cases hy; rfl
  | fvar _ n wf => cases hy; rfl
  | const _ h => cases hy with | const _ h' => exact h.unique h'
  | @app Γ η A B f x function argument hf hx ihf ihx =>
      cases hy with
      | app hg hy =>
          have same := (Ty.arr.inj (hf.typing.unique hg.typing)).1
          cases same
          cases ihf hg
          cases ihx hy
          rfl
  | lam wf hf ih =>
      cases hy with
      | lam _ hg => exact funext (fun z => ih z (hg z))

end Silmaril.Logic.HOLLight
