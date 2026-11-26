module

public import Silmaril.SSA.Isotope.Institution.LetCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.InstructionMap.Thms
import Silmaril.Raw.SSA.Isotope.LambdaSSA.PureEmbedding

/-! # Transport the computed-product seed and its literal raw relation -/

public section

open Silmaril

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.RelabelSeedProofs
section Seed

universe u v w e e'

open Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion)
open Paper.RetainedLet (returnOnce unpackBody unpackTerm)
open Paper.UnaryReturn.Beta.Constructors (pairSequence)
open Paper.SingletonReification.BinaryLet (returnPair)

variable {τ : Type w} [TypeFormers τ] {Φ : Type u} {Ψ : Type v} [HasTy Φ τ] [HasTy Ψ τ]
  {f : Φ → Ψ} (types : InstructionMap.PreservesTypes (τ := τ) f)
  {ε : Type e} {ε' : Type e'} [HasEff Φ ε] [HasEff Ψ ε'] {pe : ε} {qe : ε'}
  (pure : ∀ p, IsPure pe p → IsPure qe (f p))
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

include types pure in
theorem joinedStep_mapInstr (h : JoinedStep pe Γ r s L) :
    JoinedStep qe Γ (r.mapInstr f) (s.mapInstr f) L := by
  rcases h with ((((((h | h) | (h | h)) | h) | h) | h) | h)
  · cases h with
    | fst A B => exact .inl (.inl (.inl (.inl (.inl (.inl (.fst A B))))))
    | snd A B => exact .inl (.inl (.inl (.inl (.inl (.inl (.snd A B))))))
  · cases h
    exact .inl (.inl (.inl (.inl (.inl (.inr .unit)))))
  · cases h with
    | fuse ha hb =>
      exact .inl (.inl (.inl (.inl (.inr (.inl (.fuse (ha.mapInstr f types) (hb.mapInstr f types)))))))
  · cases h with
    | split ha hb pa pb =>
      refine .inl (.inl (.inl (.inl (.inr (.inr ?_)))))
      simpa only [mapInstr_returnRegion, Region.mapInstr, Tm.mapInstr, Tm.mapInstr_rename, mapInstr_renameVars] using
        WithCaseReturns.Step.split (ha.mapInstr f types) (hb.mapInstr f types)
          (pa.mapInstr f pure) (pb.mapInstr f pure)
  · cases h with
    | seq ha hb =>
      refine .inl (.inl (.inl (.inr ?_)))
      simpa only [returnOnce, pairSequence, Region.mapInstr, Tm.mapInstr, Tm.mapInstr_rename] using
        WithPairReturns.Step.seq (ha.mapInstr f types) (hb.mapInstr f types)
  · cases h with
    | seq p ha =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      have hsrc := (ha.mapInstr f types)
      rw [← types.source p] at hsrc
      simpa only [types.target, mapInstr_returnRegion, Tm.mapInstr] using
        WithComputedCallReturns.Step.seq (f p) hsrc
  · cases h with
    | unpack hb =>
      apply Or.inl
      apply Or.inr
      simpa only [unpackBody, unpackTerm, mapInstr_returnRegion, Region.mapInstr, Tm.mapInstr,
        mapInstr_renameVars, Tm.mapInstr_rename] using
        WithProductDestructureReturns.Step.unpack (hb.mapInstr f types)
  · cases h with
    | producer ha => exact .inr (.producer (ha.mapInstr f types))


end Seed

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

omit [TypeFormers τ] in
private theorem mapPure (p : P.Instr) (hp : IsPure pe p) : IsPure pe (g.instr p) :=
  (g.effect p).trans hp

theorem mapRawRel (r s : Rep (Φ := P.Instr) A B)
    (h : Extension.Eqv (S[P]).rawStep [A] r.val s.val [B]) :
    Extension.Eqv (S[Q]).rawStep [A] (r.val.mapInstr g.instr) (s.val.mapInstr g.instr) [B] := by
  apply ((S[Q]).eqv_iff_normalized (r.property.mapInstr g.instr (mapTypes g))
    (s.property.mapInstr g.instr (mapTypes g))).2
  have e : Extension.Eqv (JoinedStep (Φ := P.Instr) pe) [A] r.val.bindBranchArguments s.val.bindBranchArguments [B] :=
    (raw_eqv_iff_normalized pe r.property s.property).1 h
  change Extension.Eqv (JoinedStep (Φ := Q.Instr) pe) [A]
    (r.val.mapInstr g.instr).bindBranchArguments (s.val.mapInstr g.instr).bindBranchArguments [B]
  simpa only [mapInstr_bindBranchArguments] using
    e.mapInstr (Target := JoinedStep (Φ := Q.Instr) pe) (mapTypes g)
      (fun h => joinedStep_mapInstr (mapTypes g) (mapPure pe g) h)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.RelabelSeedProofs
