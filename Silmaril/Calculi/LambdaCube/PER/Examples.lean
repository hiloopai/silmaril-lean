module

public import Silmaril.Calculi.LambdaCube.PER.ParametricityOmega
public import Silmaril.Calculi.LambdaCube.PER.Reynolds

@[expose] public section

/-! Small closed terms and concrete model witnesses for the parametricity API.
`termModel` is the quotient of closed lambda terms by βη conversion. Its `K`
and `S` combinators are distinct, so the Church-boolean example separates two
values in a concrete PER model. -/

namespace Silmaril.Calculi.LambdaCube.PERModel.Examples

universe u

/-- The System F term `ΛX. λx:X. x`. -/
def polymorphicIdentity : SystemF.Tm := .tlam (.lam (.var 0) (.var 0))

theorem polymorphicIdentity_typed :
    SystemF.Typed [] polymorphicIdentity SystemF.idTy := .tlam (.lam (.var rfl))

/-- The free theorem applies to a closed, explicitly typed inhabitant. -/
theorem polymorphicIdentity_app (M : CombAlg.{u}) (ρ : ℕ → M.D) (a : M.D) :
    M.app (polymorphicIdentity.erase.eval M ρ) a = a :=
  SystemF.free_id polymorphicIdentity_typed ρ a

/-- The Fω term `ΛF:*→*. ΛX:*. λx:F X. x`. -/
def higherKindedIdentity : SystemFOmega.Tm :=
  .tlam (.arr .star .star)
    (.tlam .star (.lam (.app (.var 1) (.var 0)) (.var 0)))

theorem higherKindedIdentity_typed :
    SystemFOmega.Typed [] [] higherKindedIdentity SystemFOmega.hkIdTy :=
  .tlam (.tlam (.lam (.app (.var rfl) (.var rfl)) (.var rfl)))

/-- A higher-kind variable may denote any relation transformer in this model. -/
theorem higherKindedIdentity_app (M : CombAlg.{u}) (ρ : ℕ → M.D) (a : M.D) :
    M.app (higherKindedIdentity.erase.eval M ρ) a = a :=
  SystemFOmega.free_hkId higherKindedIdentity_typed ρ a

/-- The closed true realizer belongs to the Church-boolean PER. -/
theorem churchTrue_mem (η : ℕ → PER termModel.D) (ρ : ℕ → termModel.D) :
    (SystemF.boolTy.interp termModel η).Dom (SystemF.tru.erase.eval termModel ρ) :=
  SystemF.tru_typed.sound η ρ ρ (fun _ _ h => by simp at h)

/-- The closed false realizer belongs to the same PER. -/
theorem churchFalse_mem (η : ℕ → PER termModel.D) (ρ : ℕ → termModel.D) :
    (SystemF.boolTy.interp termModel η).Dom (SystemF.fls.erase.eval termModel ρ) :=
  SystemF.fls_typed.sound η ρ ρ (fun _ _ h => by simp at h)

/-- Those two inhabitants are inequivalent in the concrete term model. -/
theorem churchBooleans_distinct (η : ℕ → PER termModel.D) (ρ ρ' : ℕ → termModel.D) :
    ¬ (SystemF.boolTy.interp termModel η).rel
      (SystemF.tru.erase.eval termModel ρ) (SystemF.fls.erase.eval termModel ρ') :=
  SystemF.bool_distinct termModel_k_ne_s η ρ ρ'

/-- The separate full-function-space semantic laws have no simultaneous model. -/
theorem fullSetModel_empty : IsEmpty Reynolds.SetModel.{u} := Reynolds.isEmpty_setModel

/-- A universe containing the empty and singleton sets witnesses the weaker
universe theorem: all of its members are subsingletons, and one is inhabited. -/
theorem subsingletonUniverse_inhabited : Nonempty (Reynolds.UniverseModel.boolUniverse.El true) :=
  Reynolds.UniverseModel.boolUniverse_true_nonempty

end Silmaril.Calculi.LambdaCube.PERModel.Examples
