module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.InstructionMap.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.Example.Thms

/-! # A many-to-one relabelling of the effectful product producer -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.RelabellingExample

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Silmaril.Isotope.Institution (InstrSig)
open Paper.WithComputedCallReturns.Example (Atom Payload)
open Paper.WithProductDestructureReturns.Example.Computed (Packet packet_typed)
open Paper.SingletonReification.BinaryLet (returnPair_typed)
open Paper.RetainedLet.Generation.Example (Op)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding

/-- The Bool tag distinguishes primitive names with the same profile. -/
def tagged : InstrSig (Ty Atom) (ULift.{1} Bool) where
  Instr := ULift.{1} (Op × Bool)
  hasTy := ⟨fun p => instrSrc p.down.1, fun p => instrTrg p.down.1⟩
  hasEff := ⟨fun p => ⟨instrEff p.down.1⟩⟩

def plain : InstrSig (Ty Atom) (ULift.{1} Bool) where
  Instr := ULift.{1} Op
  hasTy := ⟨fun p => instrSrc p.down, fun p => instrTrg p.down⟩
  hasEff := ⟨fun p => ⟨instrEff p.down⟩⟩

def forgetTag : tagged ⟶ plain := ⟨fun p => ⟨p.down.1⟩, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem forgetTag_noninjective : ¬ Function.Injective forgetTag.instr := fun h =>
  Bool.noConfusion (congrArg (fun p : tagged.Instr => p.down.2)
    (h (a₁ := ⟨(Op.produce, false)⟩) (a₂ := ⟨(Op.produce, true)⟩) rfl) : false = true)

theorem taggedPacket_typed :
    Tm.HasType [Payload] (.pair (.var 0) (.op ⟨(Op.produce, true)⟩ (.var 0)) : Tm tagged.Instr) Packet :=
  .pair (.var (i := 0) rfl) (.op (.var (i := 0) rfl))

theorem plainPacket_typed : Tm.HasType [Payload]
    (.pair (.var 0) (.op ⟨Op.produce⟩ (.var 0)) : Tm plain.Instr) Packet :=
  Tm.HasType.mapInstr (Ψ := plain.Instr) (fun p => ⟨p⟩) ⟨fun _ => rfl, fun _ => rfl⟩ packet_typed

local notation "Src" => singletonSeed (τ := Ty Atom) (Φ := tagged.Instr) (ULift.up false)
local notation "Trg" => singletonSeed (τ := Ty Atom) (Φ := plain.Instr) (ULift.up false)

/-- The raw producer rewrites in the tagged signature and its relabelled bare
endpoint is the exact original primitive witness. -/
theorem forgetTag_raw_producer :
    rawMap (ULift.up false) forgetTag (Singleton.rawClass Src (returnPair_typed taggedPacket_typed).hasType) =
      Singleton.rawClass Trg (.br (ℓ := 0) rfl plainPacket_typed) :=
  (congrArg (rawMap (ULift.up false) forgetTag) (raw_class_producer_eq (ULift.up false) taggedPacket_typed)).trans
    (rawMap_rawClass (ULift.up false) forgetTag (.br (ℓ := 0) rfl taggedPacket_typed))

/-- The same fixture computes the guarded once-only arrow after relabelling. -/
theorem forgetTag_guarded_producer :
    (guardedFunctor (ULift.up false) forgetTag).map
      (Singleton.normalizeHom Src (Singleton.rawClass Src (returnPair_typed taggedPacket_typed).hasType)) =
    Extension.Singleton.ofRegion (Trg).step (Paper.RetainedLet.returnOnce_typed plainPacket_typed) :=
  (normalize_natural (ULift.up false) forgetTag _).symm.trans
    (congrArg (Singleton.normalizeHom Trg) forgetTag_raw_producer)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.RelabellingExample
