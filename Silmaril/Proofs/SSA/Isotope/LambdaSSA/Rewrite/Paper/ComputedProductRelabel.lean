module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.InstructionMap.Defs

/-! # Relabelling the literal singleton operations -/

public section

open Silmaril

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.RelabelProofs
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
  Quotient.inductionOn a (fun r => congrArg (Quotient.mk _) (Subtype.ext (r.val.mapInstr_id)))

theorem rawMap_comp_sig (g' : Q ⟶ R) (a : H[P] A B) :
    rawMap pe g' (rawMap pe g a) = rawMap pe (g ≫ g') a :=
  Quotient.inductionOn a (fun r =>
    congrArg (Quotient.mk _) (Subtype.ext (r.val.mapInstr_comp g.instr g'.instr)))

theorem rawMap_identity (A : τ) :
    rawMap pe g (Singleton.identity (S[P]) A) = Singleton.identity (S[Q]) A := rfl

theorem rawMap_compose (a : H[P] A B) (b : H[P] B C) :
    rawMap pe g (Singleton.compose (S[P]) a b) =
      Singleton.compose (S[Q]) (rawMap pe g a) (rawMap pe g b) := by
  refine Quotient.inductionOn₂ a b (fun r s => congrArg (Quotient.mk _) (Subtype.ext ?_))
  change (compLSubst (fun _ => r.val.bindBranchArguments) (fun _ => s.val) 0).mapInstr g.instr =
    compLSubst (fun _ => (r.val.mapInstr g.instr).bindBranchArguments) (fun _ => s.val.mapInstr g.instr) 0
  simp only [compLSubst, mapInstr_lsubst, mapInstr_liftLSubstVars, mapInstr_bindBranchArguments]

theorem rawMap_whiskerLeft (X : τ) (a : H[P] A B) :
    rawMap pe g (Singleton.whiskerLeft (S[P]) X a) = Singleton.whiskerLeft (S[Q]) X (rawMap pe g a) := by
  refine Quotient.inductionOn a (fun r => congrArg (Quotient.mk _) (Subtype.ext ?_))
  change (CfgEta.TypeCategory.whiskerLeftRegion r.val.bindBranchArguments).mapInstr g.instr =
    CfgEta.TypeCategory.whiskerLeftRegion (r.val.mapInstr g.instr).bindBranchArguments
  simp only [CfgEta.TypeCategory.whiskerLeftRegion, CfgEta.TypeCategory.whiskerLeftBody, Region.mapInstr,
    Tm.mapInstr, mapInstr_lsubst, mapInstr_renameVars, mapInstr_bindBranchArguments]

theorem rawMap_whiskerRight (X : τ) (a : H[P] A B) :
    rawMap pe g (Singleton.whiskerRight (S[P]) X a) = Singleton.whiskerRight (S[Q]) X (rawMap pe g a) := by
  refine Quotient.inductionOn a (fun r => congrArg (Quotient.mk _) (Subtype.ext ?_))
  change (CfgEta.TypeCategory.whiskerRightRegion r.val.bindBranchArguments).mapInstr g.instr =
    CfgEta.TypeCategory.whiskerRightRegion (r.val.mapInstr g.instr).bindBranchArguments
  simp only [CfgEta.TypeCategory.whiskerRightRegion, CfgEta.TypeCategory.whiskerRightBody, Region.mapInstr,
    Tm.mapInstr, mapInstr_lsubst, mapInstr_renameVars, mapInstr_bindBranchArguments]

theorem rawMap_exactCopair (a : H[P] A C) (b : H[P] B C) :
    rawMap pe g (Singleton.exactCopair (S[P]) a b) = Singleton.exactCopair (S[Q]) (rawMap pe g a) (rawMap pe g b) := by
  refine Quotient.inductionOn₂ a b (fun r s => congrArg (Quotient.mk _) (Subtype.ext ?_))
  simp only [mapRep, copairRep, Region.mapInstr, Tm.mapInstr, mapInstr_renameVars]

theorem rawMap_iterateSum (a : H[P] A (coprod B A)) :
    rawMap pe g (Singleton.iterateSum (S[P]) a) = Singleton.iterateSum (S[Q]) (rawMap pe g a) := by
  refine Quotient.inductionOn a (fun r => congrArg (Quotient.mk _) (Subtype.ext ?_))
  simp only [mapRep, iterateRep, mapInstr_iterateRegion, mapInstr_bindBranchArguments]

theorem rawMap_discard (A : τ) :
    rawMap pe g (Singleton.discard (S[P]) A) = Singleton.discard (S[Q]) A := rfl

theorem rawMap_diagonal (A : τ) :
    rawMap pe g (Singleton.diagonal (S[P]) A) = Singleton.diagonal (S[Q]) A := rfl

theorem rawMap_productFst (A B : τ) :
    rawMap pe g (Singleton.productFst (S[P]) A B) = Singleton.productFst (S[Q]) A B := rfl

theorem rawMap_productSnd (A B : τ) :
    rawMap pe g (Singleton.productSnd (S[P]) A B) = Singleton.productSnd (S[Q]) A B := rfl

theorem rawMap_sumInl (A B : τ) :
    rawMap pe g (Singleton.sumInl (S[P]) A B) = Singleton.sumInl (S[Q]) A B := rfl

theorem rawMap_sumInr (A B : τ) :
    rawMap pe g (Singleton.sumInr (S[P]) A B) = Singleton.sumInr (S[Q]) A B := rfl

private theorem cast_rawClass {X X' Y Y' : τ} {r : Region Q.Instr} (hx : X = X') (hy : Y = Y')
    (hr : HasType [X] r [Y]) (hr' : HasType [X'] r [Y']) :
    cast (congrArg₂ (H[Q]) hx hy) (Singleton.rawClass (S[Q]) hr) = Singleton.rawClass (S[Q]) hr' := by
  cases hx
  cases hy
  rfl

theorem rawMap_primitive (p : P.Instr) :
    rawMap pe g (Singleton.primitive (S[P]) p) =
      cast (congrArg₂ (H[Q]) (g.source p) (g.target p)) (Singleton.primitive (S[Q]) (g.instr p)) :=
  (cast_rawClass pe (g.source p) (g.target p)
    (.br (ℓ := 0) rfl (.op (f := g.instr p) (.var (i := 0) rfl)))
    ((Tm.HasType.op (f := p) (.var (i := 0) rfl) |> fun ha => HasType.br (ℓ := 0) rfl ha).mapInstr
      g.instr (mapTypes g))).symm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.RelabelProofs
