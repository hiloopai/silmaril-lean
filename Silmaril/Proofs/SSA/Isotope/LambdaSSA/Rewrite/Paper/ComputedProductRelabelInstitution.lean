module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.InstructionMap.Institution.Defs

/-! # The typed denotation reduct square -/

public section

open Silmaril

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.InstitutionProofs
open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room Corridor)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (denoteRegion denoteSingletonRegion)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
open Paper.Extension.Singleton (ofType ofRegion denoteFunctor_map_ofRegion)
open scoped MonoidalCategory

variable {τ ε : Type} [TypeFormers τ] {P Q : InstrSig τ ε} (pe : ε)
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

local notation "S[" P "]" => singletonSeed (τ := τ) (Φ := InstrSig.Instr P) pe
local notation "JStep[" P "]" => Singleton.NormalizedSeed.step S[P]
local notation "G[" P "]" => Extension.Singleton.TypeCategory JStep[P]
local notation "H[" P "]" => Singleton.RawHom S[P]

set_option backward.isDefEq.respectTransparency false in
theorem interpret_reduct (g : P ⟶ Q) (K : CoherentRegionModel J Q) {A B : τ}
    (a : ofType JStep[P] A ⟶ ofType JStep[P] B) :
    (interpret pe J shared K).map ((guardedFunctor pe g).map a) =
      (interpret pe J shared (K.reduct g)).map a := by
  induction a using Quot.ind with
  | _ a =>
    obtain ⟨_, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion (τ := τ) (Φ := P.Instr) (A := A) (B := B) a
    change (interpret pe J shared K).map ((guardedFunctor pe g).map (ofRegion JStep[P] hr)) =
      (interpret pe J shared (K.reduct g)).map (ofRegion JStep[P] hr)
    rw [guardedMap_ofRegion, interpret_ofRegion, interpret_ofRegion]
    unfold denoteSingletonRegion
    exact congrArg (fun f =>
      J.map ((λ_ (K.types.obj A)).inv : K.types.obj A ⟶
        Semantics.Categorical.ctxObj K.types [A]) ≫ f ≫
        J.map (Semantics.Categorical.singletonLabelPayload K.types B))
      (K.denoteRegion_reduct g hr.hasType).symm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.InstitutionProofs
