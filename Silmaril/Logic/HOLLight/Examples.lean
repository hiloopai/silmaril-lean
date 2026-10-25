module

public import Silmaril.Logic.HOLLight.Kernel.Structural
public import Silmaril.Logic.HOLLight.Semantics.Substitution
public import Silmaril.Logic.HOLLight.Consistency
public import Silmaril.Logic.HOLLight.Classical.ExcludedMiddle
public meta import Silmaril.Logic.HOLLight.Type
public meta import Silmaril.Logic.HOLLight.Term
public meta import Silmaril.Logic.HOLLight.Substitution
public meta import Silmaril.Logic.HOLLight.Logic

@[expose] public section

/-!
# HOL Light syntax and model examples

These examples exercise open terms, binding, collisions between typed names,
rejected signatures, genuine polymorphic user constants, and universe lifting.
-/

namespace Silmaril.Logic.HOLLight.Examples

universe u

-- Opening beneath a lambda preserves its local binder and shifts its argument.
#guard (Tm.lam .bool (.bvar 1)).open (.bvar 0) = .lam .bool (.bvar 1)
#guard (Tm.lam .bool (.bvar 0)).open (.fvar 3 .bool) = .lam .bool (.bvar 0)
#guard (Tm.lam .bool (.fvar 3 .bool)).replaceFree (3, .bool) (.bvar 0) =
  .lam .bool (.bvar 1)

example : ¬ (Tm.bvar 0).Scope 0 := Nat.not_lt_zero 0

example : (Tm.lam .bool (.bvar 0)).Closed := Nat.zero_lt_succ 0

-- Equal numeric names with different types are initially distinct variables.
#guard (Tm.fvar 5 (.var 0)).replaceFree (5, .var 1) Tm.truth = .fvar 5 (.var 0)

-- INST_TYPE may merge them; freshness must not be transported blindly.
#guard (Tm.fvar 5 (.var 0)).tySubst (fun _ => .bool) =
  (Tm.fvar 5 (.var 1)).tySubst (fun _ => .bool)

example : (Tm.fvar 5 (.var 1)).Fresh (5, .var 0) ∧
    ¬ ((Tm.fvar 5 (.var 1)).tySubst (fun _ => .bool)).Fresh (5, .bool) := by
  simp [Tm.Fresh, Tm.freeVars, Tm.tySubst]

#guard (Tm.lam (.var 0) (.fvar 5 (.var 1))).tySubst (fun _ => .bool) =
  .lam .bool (.fvar 5 .bool)

/-- One polymorphic constant with the scheme `α → α`. -/
def identityScheme : Scheme := ⟨1, .arr (.var 0) (.var 0)⟩

def identitySignature : Signature := ⟨[], [identityScheme]⟩

theorem identitySignature_valid : identitySignature.Valid := by
  intro s hs
  have same : s = identityScheme := by simpa [identitySignature] using hs
  subst s
  simp [identityScheme, Scheme.WellFormed, Ty.WellFormed, Ty.Scoped]

example : ¬ (Ty.app 0 [.bool, .bool]).WellFormed [1] := by
  simp [Ty.WellFormed]

example : ¬ (Ty.app 0 [.bool]).WellFormed [] := by
  simp [Ty.WellFormed]

example (A : Ty) : ¬ (Const.user 0 []).HasType identitySignature A := by
  intro h
  cases h with
  | user lookup _ arity _ =>
    have same := Option.some.inj lookup
    cases same
    cases arity

-- A one-parameter scheme cannot secretly depend on parameter 1.
example : ¬ (Scheme.mk 1 (.var 1)).WellFormed [] := by
  simp [Scheme.WellFormed, Ty.WellFormed, Ty.Scoped]

theorem identityConstant_typed :
    (Const.user 0 [.bool]).HasType identitySignature (.arr .bool .bool) := by
  apply Const.HasType.user (s := identityScheme) (As := [.bool]) rfl
    (identitySignature_valid.lookup (c := 0) rfl) rfl
  intro A hA
  have same : A = .bool := by simpa using hA
  subst A
  trivial

/-- Its meaning takes only the declared semantic type arguments. -/
def identityModel : Model.{u} identitySignature where
  typeOp := fun _ _ => Carrier.unit
  constant name scheme lookup args := by
    cases name with
    | zero =>
      have same := Option.some.inj lookup
      cases same
      exact fun x => x
    | succ n => simp [identitySignature] at lookup

example (args : List Carrier.{u}) :
    identityModel.constant 0 identityScheme rfl args = fun x => x := rfl

def individuals : TypeValuation.{u} := fun _ => Carrier.ind

noncomputable def defaultFreeEnv : FreeEnv identityModel.{u} individuals :=
  fun _ A => Classical.choice (A.denote identityModel.toTypeModel individuals).property

example : ∃ value, Eval identityModel.{0} individuals defaultFreeEnv BoundEnv.empty
    (.const (.user 0 [.bool])) (.arr .bool .bool) value :=
  (HasType.const identityConstant_typed).eval_exists _ _ _ _

example : ∃ value, Eval identityModel.{1} individuals defaultFreeEnv BoundEnv.empty
    (.const (.user 0 [.bool])) (.arr .bool .bool) value :=
  (HasType.const identityConstant_typed).eval_exists _ _ _ _

/-- The same schematic variable can denote any point of its assigned carrier. -/
theorem schematicVariable_at (ρ : TypeValuation.{u}) (x : ρ 0) :
    ∃ ν : FreeEnv identityModel.{u} ρ,
      Eval identityModel ρ ν BoundEnv.empty (.fvar 0 (.var 0)) (.var 0) x := by
  classical
  let ν : FreeEnv identityModel.{u} ρ :=
    fun _ A => Classical.choice (A.denote identityModel.toTypeModel ρ).property
  refine ⟨ν.update 0 (.var 0) x, ?_⟩
  have ev := Eval.fvar (M := identityModel.{u}) (ρ := ρ) (ν := ν.update 0 (.var 0) x)
    (A := .var 0) BoundEnv.empty 0 (by trivial)
  exact Eq.mp (congrArg (fun y : Value identityModel ρ (.var 0) =>
    Eval identityModel ρ (ν.update 0 (.var 0) x) BoundEnv.empty
      (.fvar 0 (.var 0)) (.var 0) y) (FreeEnv.update_self ν 0 (.var 0) x)) ev

-- One syntactic variable, two carrier assignments, and distinct supplied values.
example : ∃ ν : FreeEnv identityModel.{0} (fun _ => Carrier.bool),
    Eval identityModel (fun _ => Carrier.bool) ν BoundEnv.empty
      (.fvar 0 (.var 0)) (.var 0) (ULift.up true) :=
  schematicVariable_at _ _

example : ∃ ν : FreeEnv identityModel.{0} individuals,
    Eval identityModel individuals ν BoundEnv.empty
      (.fvar 0 (.var 0)) (.var 0) (ULift.up 37) :=
  schematicVariable_at _ _

-- Universe lifting does not force either singleton carriers or default values.
example : ∃ ν : FreeEnv identityModel.{1} (fun _ => Carrier.bool),
    Eval identityModel (fun _ => Carrier.bool) ν BoundEnv.empty
      (.fvar 0 (.var 0)) (.var 0) (ULift.up true) :=
  schematicVariable_at _ _

example : ∃ ν : FreeEnv identityModel.{1} (fun _ => Carrier.bool),
    Eval identityModel (fun _ => Carrier.bool) ν BoundEnv.empty
      (.fvar 0 (.var 0)) (.var 0) (ULift.up false) :=
  schematicVariable_at _ _

example : ∃ ν : FreeEnv identityModel.{1} individuals,
    Eval identityModel individuals ν BoundEnv.empty
      (.fvar 0 (.var 0)) (.var 0) (ULift.up 37) :=
  schematicVariable_at _ _

-- The primitive kernel types both constant instances and derived beta conversions.
example : Derives identitySignature [] ∅
    (Tm.equal (.arr .bool .bool) (.const (.user 0 [.bool])) (.const (.user 0 [.bool]))) :=
  .refl (.const identityConstant_typed)

example : Derives initialSignature [] ∅
    (Tm.equal (.arr .bool .bool)
      (.app (.lam .bool (.lam .bool (.bvar 1))) (.fvar 7 .bool))
      (.lam .bool (.fvar 7 .bool))) := by
  exact Derives.generalBeta (.lam (by trivial) (.bvar rfl (by trivial)))
    (.fvar 7 (by trivial))

example (theory : Theory) : ¬ Derives initialSignature theory ∅ (.bvar 0) := by
  intro h
  cases h.typing with
  | bvar lookup _ => cases lookup

/-- Soundness has a concrete model witness at every universe level. -/
theorem standard_model_exists :
    ∃ M : Model.{u} initialSignature, Models M classicalTheory :=
  ⟨Model.standard, standard_models_classical⟩

/-- The kernel proves truth even with an empty object theory. -/
theorem truth_without_axioms : Derives initialSignature [] ∅ Tm.truth :=
  Derives.truth

/-- Its standard classical theory does not derive falsity. -/
theorem falsity_not_derivable :
    ¬ Derives initialSignature classicalTheory ∅ Tm.falsity :=
  classical_consistent

/-- Classical reasoning is an object-level derivation, with typing explicit. -/
theorem excluded_middle {p : Tm} (typing : HasType initialSignature [] p .bool) :
    Derives initialSignature classicalTheory ∅ (Tm.disj p (Tm.neg p)) :=
  Derives.excludedMiddle typing

end Silmaril.Logic.HOLLight.Examples
