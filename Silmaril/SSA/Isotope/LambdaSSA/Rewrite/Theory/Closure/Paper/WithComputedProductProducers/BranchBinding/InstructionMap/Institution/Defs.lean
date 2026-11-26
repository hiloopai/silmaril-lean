module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.InstructionMap.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Reduct.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms

/-! # Coherent models and raw and guarded equation rooms -/

@[expose] public section

open Silmaril

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding
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

noncomputable def interpret (K : CoherentRegionModel J P) : G[P] ⥤ C :=
  letI := K.instructions
  letI := K.coherent
  Extension.Singleton.denoteFunctor J K.types shared (joined_seedDenotes pe J K.types shared)

theorem interpret_ofRegion (K : CoherentRegionModel J P) {A B : τ} {r : Region P.Instr}
    (hr : ValueBranches [A] r [B]) :
    (interpret pe J shared K).map (ofRegion JStep[P] hr) =
      (letI := K.instructions; denoteSingletonRegion J K.types hr.hasType) :=
  letI := K.instructions
  letI := K.coherent
  denoteFunctor_map_ofRegion J K.types shared (joined_seedDenotes pe J K.types shared) hr

abbrev RawEquation (P : InstrSig τ ε) := Σ i : τ × τ, H[P] i.1 i.2 × H[P] i.1 i.2

abbrev GuardedEquation (P : InstrSig τ ε) := Σ i : τ × τ,
  (ofType JStep[P] i.1 ⟶ ofType JStep[P] i.2) × (ofType JStep[P] i.1 ⟶ ofType JStep[P] i.2)

noncomputable def guardedRoom (P : InstrSig τ ε) : Room.{0, 1, 1} where
  Sen := GuardedEquation pe P
  Mod := Cat.of (Discrete (CoherentRegionModel J P))
  Sat K e := (interpret pe J shared K.as).map e.2.1 = (interpret pe J shared K.as).map e.2.2

noncomputable def rawRoom (P : InstrSig τ ε) : Room.{0, 1, 1} where
  Sen := RawEquation pe P
  Mod := Cat.of (Discrete (CoherentRegionModel J P))
  Sat K e := (interpret pe J shared K.as).map (Singleton.normalizeHom S[P] e.2.1) =
    (interpret pe J shared K.as).map (Singleton.normalizeHom S[P] e.2.2)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding
