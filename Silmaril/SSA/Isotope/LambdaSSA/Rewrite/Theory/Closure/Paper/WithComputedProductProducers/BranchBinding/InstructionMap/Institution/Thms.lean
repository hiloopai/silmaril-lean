module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.InstructionMap.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductRelabelInstitution

/-! # Raw and guarded equation corridors over coherent models -/

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

theorem interpret_reduct (g : P ⟶ Q) (K : CoherentRegionModel J Q) {A B : τ}
    (a : ofType JStep[P] A ⟶ ofType JStep[P] B) :
    (interpret pe J shared K).map ((guardedFunctor pe g).map a) =
      (interpret pe J shared (K.reduct g)).map a :=
  InstitutionProofs.interpret_reduct pe J shared g K a

noncomputable def guardedCorridor (g : P ⟶ Q) : guardedRoom pe J shared P ⟶ guardedRoom pe J shared Q where
  sen e := ⟨e.1, (guardedFunctor pe g).map e.2.1, (guardedFunctor pe g).map e.2.2⟩
  mod := Discrete.functor (fun K => Discrete.mk (K.reduct g))
  sat K e := by
    change ((interpret pe J shared K.as).map ((guardedFunctor pe g).map e.2.1) =
      (interpret pe J shared K.as).map ((guardedFunctor pe g).map e.2.2)) ↔
      (interpret pe J shared (K.as.reduct g)).map e.2.1 = (interpret pe J shared (K.as.reduct g)).map e.2.2
    simp only [interpret_reduct pe J shared g K.as]
    rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def rawCorridor (g : P ⟶ Q) : rawRoom pe J shared P ⟶ rawRoom pe J shared Q where
  sen e := ⟨e.1, rawMap pe g e.2.1, rawMap pe g e.2.2⟩
  mod := Discrete.functor (fun K => Discrete.mk (K.reduct g))
  sat K e := by
    change ((interpret pe J shared K.as).map (Singleton.normalizeHom S[Q] (rawMap pe g e.2.1)) =
      (interpret pe J shared K.as).map (Singleton.normalizeHom S[Q] (rawMap pe g e.2.2))) ↔
      (interpret pe J shared (K.as.reduct g)).map (Singleton.normalizeHom S[P] e.2.1) =
        (interpret pe J shared (K.as.reduct g)).map (Singleton.normalizeHom S[P] e.2.2)
    simp only [normalize_natural pe g, interpret_reduct pe J shared g K.as]

noncomputable def normalizeCorridor (P : InstrSig τ ε) : rawRoom pe J shared P ⟶ guardedRoom pe J shared P where
  sen e := ⟨e.1, Singleton.normalizeHom S[P] e.2.1, Singleton.normalizeHom S[P] e.2.2⟩
  mod := 𝟭 _
  sat _ _ := Iff.rfl

theorem normalizeCorridor_natural (g : P ⟶ Q) :
    rawCorridor pe J shared g ≫ normalizeCorridor pe J shared Q =
      normalizeCorridor pe J shared P ≫ guardedCorridor pe J shared g := by
  apply Corridor.ext
  · funext e
    change (⟨e.1, Singleton.normalizeHom S[Q] (rawMap pe g e.2.1),
      Singleton.normalizeHom S[Q] (rawMap pe g e.2.2)⟩ : GuardedEquation pe Q) =
      ⟨e.1, (guardedFunctor pe g).map (Singleton.normalizeHom S[P] e.2.1),
        (guardedFunctor pe g).map (Singleton.normalizeHom S[P] e.2.2)⟩
    rw [normalize_natural, normalize_natural]
  · rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding
