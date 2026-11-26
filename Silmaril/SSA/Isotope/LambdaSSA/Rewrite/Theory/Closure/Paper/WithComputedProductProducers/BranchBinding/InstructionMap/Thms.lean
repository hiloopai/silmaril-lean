module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.InstructionMap.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductRelabel

/-! # Signature naturality of the computed-product singleton comparison -/

@[expose] public section

open Silmaril

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding
open CategoryTheory
open Silmaril.Isotope.Institution (InstrSig)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
open Paper.Extension.Singleton (ofType ofRegion)
open OrderedPairSingleton (Rep composeRep iterateRep)
open OrderedPairSingleton.Operations (whiskerLeftRep whiskerRightRep copairRep)

universe u

variable {τ ε : Type u} [TypeFormers τ] {P Q R : InstrSig τ ε} (pe : ε)

local notation "S[" P "]" => singletonSeed (τ := τ) (Φ := InstrSig.Instr P) pe
local notation "Raw[" P "]" => Singleton.RawTypeCategory S[P]
local notation "JStep[" P "]" => Singleton.NormalizedSeed.step S[P]
local notation "G[" P "]" => Extension.Singleton.TypeCategory JStep[P]
local notation "H[" P "]" => Singleton.RawHom S[P]

variable (g : P ⟶ Q) {A B C : τ}

theorem rawMap_id_sig (a : H[P] A B) : rawMap pe (𝟙 P) a = a :=
  RelabelProofs.rawMap_id_sig pe a

theorem rawMap_comp_sig (g' : Q ⟶ R) (a : H[P] A B) :
    rawMap pe g' (rawMap pe g a) = rawMap pe (g ≫ g') a :=
  RelabelProofs.rawMap_comp_sig pe g g' a

theorem rawMap_identity (A : τ) :
    rawMap pe g (Singleton.identity (S[P]) A) = Singleton.identity (S[Q]) A :=
  RelabelProofs.rawMap_identity pe g A

theorem rawMap_compose (a : H[P] A B) (b : H[P] B C) :
    rawMap pe g (Singleton.compose (S[P]) a b) =
      Singleton.compose (S[Q]) (rawMap pe g a) (rawMap pe g b) :=
  RelabelProofs.rawMap_compose pe g a b

theorem rawMap_whiskerLeft (X : τ) (a : H[P] A B) :
    rawMap pe g (Singleton.whiskerLeft (S[P]) X a) = Singleton.whiskerLeft (S[Q]) X (rawMap pe g a) :=
  RelabelProofs.rawMap_whiskerLeft pe g X a

theorem rawMap_whiskerRight (X : τ) (a : H[P] A B) :
    rawMap pe g (Singleton.whiskerRight (S[P]) X a) = Singleton.whiskerRight (S[Q]) X (rawMap pe g a) :=
  RelabelProofs.rawMap_whiskerRight pe g X a

theorem rawMap_exactCopair (a : H[P] A C) (b : H[P] B C) :
    rawMap pe g (Singleton.exactCopair (S[P]) a b) = Singleton.exactCopair (S[Q]) (rawMap pe g a) (rawMap pe g b) :=
  RelabelProofs.rawMap_exactCopair pe g a b

theorem rawMap_iterateSum (a : H[P] A (coprod B A)) :
    rawMap pe g (Singleton.iterateSum (S[P]) a) = Singleton.iterateSum (S[Q]) (rawMap pe g a) :=
  RelabelProofs.rawMap_iterateSum pe g a

theorem rawMap_discard (A : τ) :
    rawMap pe g (Singleton.discard (S[P]) A) = Singleton.discard (S[Q]) A :=
  RelabelProofs.rawMap_discard pe g A

theorem rawMap_diagonal (A : τ) :
    rawMap pe g (Singleton.diagonal (S[P]) A) = Singleton.diagonal (S[Q]) A :=
  RelabelProofs.rawMap_diagonal pe g A

theorem rawMap_productFst (A B : τ) :
    rawMap pe g (Singleton.productFst (S[P]) A B) = Singleton.productFst (S[Q]) A B :=
  RelabelProofs.rawMap_productFst pe g A B

theorem rawMap_productSnd (A B : τ) :
    rawMap pe g (Singleton.productSnd (S[P]) A B) = Singleton.productSnd (S[Q]) A B :=
  RelabelProofs.rawMap_productSnd pe g A B

theorem rawMap_sumInl (A B : τ) :
    rawMap pe g (Singleton.sumInl (S[P]) A B) = Singleton.sumInl (S[Q]) A B :=
  RelabelProofs.rawMap_sumInl pe g A B

theorem rawMap_sumInr (A B : τ) :
    rawMap pe g (Singleton.sumInr (S[P]) A B) = Singleton.sumInr (S[Q]) A B :=
  RelabelProofs.rawMap_sumInr pe g A B

theorem rawMap_primitive (p : P.Instr) :
    rawMap pe g (Singleton.primitive (S[P]) p) =
      cast (congrArg₂ (H[Q]) (g.source p) (g.target p)) (Singleton.primitive (S[Q]) (g.instr p)) :=
  RelabelProofs.rawMap_primitive pe g p

def rawFunctor : Raw[P] ⥤ Raw[Q] where
  obj X := ⟨X.as⟩
  map := rawMap pe g
  map_id X := rawMap_identity pe g X.as
  map_comp a b := rawMap_compose pe g a b

noncomputable def guardedFunctor : G[P] ⥤ G[Q] :=
  Singleton.toRawFunctor (S[P]) ⋙ rawFunctor pe g ⋙ Singleton.normalizeFunctor (S[Q])

theorem normalize_natural (a : H[P] A B) :
    Singleton.normalizeHom (S[Q]) (rawMap pe g a) =
      (guardedFunctor pe g).map (Singleton.normalizeHom (S[P]) a) := by
  change _ = Singleton.normalizeHom (S[Q])
    (rawMap pe g ((Singleton.homEquiv (S[P]) A B).symm ((Singleton.homEquiv (S[P]) A B) a)))
  rw [Equiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
theorem guardedMap_ofRegion {r : Region P.Instr} (hr : ValueBranches [A] r [B]) :
    (guardedFunctor pe g).map (ofRegion JStep[P] hr) =
      ofRegion JStep[Q] (hr.mapInstr (mapTypes g)) := by
  rw [← Singleton.normalize_guarded (S[P]) hr, ← normalize_natural, rawMap_rawClass]
  exact Singleton.normalize_guarded (S[Q]) (hr.mapInstr (mapTypes g))

theorem normalizeFunctor_natural :
    rawFunctor pe g ⋙ Singleton.normalizeFunctor (S[Q]) =
      Singleton.normalizeFunctor (S[P]) ⋙ guardedFunctor pe g :=
  Functor.hext (fun _ => rfl) (fun _ _ a => heq_of_eq (normalize_natural pe g a))

set_option backward.isDefEq.respectTransparency false in
theorem guardedMap_iterateSum (a : ofType JStep[P] A ⟶ ofType JStep[P] (coprod B A)) :
    (guardedFunctor pe g).map (Extension.Singleton.iterateSum JStep[P] a) =
      Extension.Singleton.iterateSum JStep[Q] ((guardedFunctor pe g).map a) := by
  obtain ⟨a, rfl⟩ := Singleton.normalizeHom_surjective (S[P]) a
  rw [← Singleton.normalize_iterateSum, ← normalize_natural, rawMap_iterateSum,
    Singleton.normalize_iterateSum, normalize_natural]

set_option backward.isDefEq.respectTransparency false in
theorem guardedMap_whiskerLeft (X : τ) (a : ofType JStep[P] A ⟶ ofType JStep[P] B) :
    (guardedFunctor pe g).map (Extension.Singleton.whiskerLeft JStep[P] (ofType JStep[P] X) a) =
      Extension.Singleton.whiskerLeft JStep[Q] (ofType JStep[Q] X) ((guardedFunctor pe g).map a) := by
  obtain ⟨a, rfl⟩ := Singleton.normalizeHom_surjective S[P] a
  rw [← Singleton.normalize_whiskerLeft, ← normalize_natural, rawMap_whiskerLeft,
    Singleton.normalize_whiskerLeft, normalize_natural]

set_option backward.isDefEq.respectTransparency false in
theorem guardedMap_whiskerRight (X : τ) (a : ofType JStep[P] A ⟶ ofType JStep[P] B) :
    (guardedFunctor pe g).map (Extension.Singleton.whiskerRight JStep[P] a (ofType JStep[P] X)) =
      Extension.Singleton.whiskerRight JStep[Q] ((guardedFunctor pe g).map a) (ofType JStep[Q] X) := by
  obtain ⟨a, rfl⟩ := Singleton.normalizeHom_surjective S[P] a
  rw [← Singleton.normalize_whiskerRight, ← normalize_natural, rawMap_whiskerRight,
    Singleton.normalize_whiskerRight, normalize_natural]

set_option backward.isDefEq.respectTransparency false in
theorem guardedMap_exactCopair (a : ofType JStep[P] A ⟶ ofType JStep[P] C)
    (b : ofType JStep[P] B ⟶ ofType JStep[P] C) :
    (guardedFunctor pe g).map (Extension.Singleton.ValueCoproducts.exactCopair JStep[P] a b) =
      Extension.Singleton.ValueCoproducts.exactCopair JStep[Q]
        ((guardedFunctor pe g).map a) ((guardedFunctor pe g).map b) := by
  obtain ⟨a, rfl⟩ := Singleton.normalizeHom_surjective S[P] a
  obtain ⟨b, rfl⟩ := Singleton.normalizeHom_surjective S[P] b
  rw [← Singleton.normalize_exactCopair, ← normalize_natural, rawMap_exactCopair,
    Singleton.normalize_exactCopair, normalize_natural, normalize_natural]

def rawHomFunctor (A B : τ) : InstrSig τ ε ⥤ Type u where
  obj P := H[P] A B
  map g := ↾(rawMap pe g)
  map_id _ := ConcreteCategory.hom_ext _ _ (fun a => rawMap_id_sig pe a)
  map_comp g h := ConcreteCategory.hom_ext _ _ (fun a => (rawMap_comp_sig pe g h a).symm)

set_option backward.isDefEq.respectTransparency false in
noncomputable def guardedHomFunctor (A B : τ) : InstrSig τ ε ⥤ Type u where
  obj P := ofType JStep[P] A ⟶ ofType JStep[P] B
  map g := ↾((guardedFunctor pe g).map)
  map_id P := ConcreteCategory.hom_ext _ _ fun a => by
    obtain ⟨a, rfl⟩ := Singleton.normalizeHom_surjective S[P] a
    change (guardedFunctor pe (𝟙 P)).map (Singleton.normalizeHom S[P] a) = Singleton.normalizeHom S[P] a
    rw [← normalize_natural, rawMap_id_sig]
  map_comp g h := ConcreteCategory.hom_ext _ _ fun a => by
    obtain ⟨a, rfl⟩ := Singleton.normalizeHom_surjective S[_] a
    change (guardedFunctor pe (g ≫ h)).map (Singleton.normalizeHom S[_] a) =
      (guardedFunctor pe h).map ((guardedFunctor pe g).map (Singleton.normalizeHom S[_] a))
    exact (normalize_natural pe (g ≫ h) a).symm.trans
      ((congrArg (Singleton.normalizeHom S[_]) (rawMap_comp_sig pe g h a).symm).trans
        ((normalize_natural pe h (rawMap pe g a)).trans
          (congrArg (guardedFunctor pe h).map (normalize_natural pe g a))))

set_option backward.isDefEq.respectTransparency false in
noncomputable def homNaturalIso (A B : τ) : rawHomFunctor pe A B ≅ guardedHomFunctor pe A B :=
  NatIso.ofComponents (fun P => (Singleton.homEquiv S[P] A B).toIso)
    (fun g => ConcreteCategory.hom_ext _ _ (normalize_natural pe g))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding
