module

public import Silmaril.SSA.Isotope.Institution.LetCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.InstructionMap.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductRelabelSeed

/-! # Literal maps on raw computed-product representatives -/

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

omit [TypeFormers τ] in
theorem mapTypes : InstructionMap.PreservesTypes (τ := τ) g.instr := ⟨g.source, g.target⟩

def mapRep (r : Rep (Φ := P.Instr) A B) : Rep (Φ := Q.Instr) A B :=
  ⟨r.val.mapInstr g.instr, r.property.mapInstr g.instr (mapTypes g)⟩

theorem mapRawRel (r s : Rep (Φ := P.Instr) A B)
    (h : Extension.Eqv (S[P]).rawStep [A] r.val s.val [B]) :
    Extension.Eqv (S[Q]).rawStep [A] (mapRep g r).val (mapRep g s).val [B] :=
  RelabelSeedProofs.mapRawRel pe g r s h

def rawMap (a : H[P] A B) : H[Q] A B :=
  Quotient.map (mapRep g) (mapRawRel pe g) a

theorem rawMap_rawClass {r : Region P.Instr} (hr : HasType [A] r [B]) :
    rawMap pe g (Singleton.rawClass (S[P]) hr) =
      Singleton.rawClass (S[Q]) (hr.mapInstr g.instr (mapTypes g)) := rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding
