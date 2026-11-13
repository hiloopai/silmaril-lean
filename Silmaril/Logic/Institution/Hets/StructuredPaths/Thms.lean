module

public import Silmaril.Logic.Institution.Hets.StructuredPaths.Defs
public import Silmaril.Proofs.Logic.Institution.Hets.StructuredPaths

@[expose] public section
namespace Silmaril.Logic.Institution.Hets.StructuredPaths
open CategoryTheory Silmaril.Logic.Institution
universe u₀ v₀ u v w m₁ m₂

variable (L : LogicGraph.{u₀,v₀,u,v,w,m₁,m₂}) {a b : L.Idx}

/-- A translated specification is satisfied exactly by models whose actual
path reduct satisfies the source specification. No model-expansion assumption. -/
theorem models_translate (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat L.indexed) (L.sigOf a S))
    (M : ((IndexedCoInst.flat L.indexed).obj (target L p S)).Mod) :
    M ∈ (translate L p S SP).models ↔
      ((IndexedCoInst.flat L.indexed).map (lift L p S)).mod.obj M ∈ SP.models := Iff.rfl

/-- Sentence satisfaction along the path is the shared institution law. -/
theorem satisfaction (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (M : ((IndexedCoInst.flat L.indexed).obj (target L p S)).Mod)
    (φ : ((IndexedCoInst.flat L.indexed).obj (L.sigOf a S)).Sen) :
    ((IndexedCoInst.flat L.indexed).obj (target L p S)).Sat M
      (((IndexedCoInst.flat L.indexed).map (lift L p S)).sen φ) ↔
    ((IndexedCoInst.flat L.indexed).obj (L.sigOf a S)).Sat
      (((IndexedCoInst.flat L.indexed).map (lift L p S)).mod.obj M) φ :=
  ((IndexedCoInst.flat L.indexed).map (lift L p S)).sat M φ

/-- Translation preserves structured entailment along every path. -/
theorem entails_translate (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat L.indexed) (L.sigOf a S))
    (φ : ((IndexedCoInst.flat L.indexed).obj (L.sigOf a S)).Sen)
    (h : SP.Entails φ) :
    (translate L p S SP).Entails (((IndexedCoInst.flat L.indexed).map (lift L p S)).sen φ) :=
  StrSpec.Entails.translate (lift L p S) h

/-- If every source model expands along the path, structured entailment is
also reflected. This applies to arbitrary structured source specifications. -/
theorem entails_iff (p : Quiver.Path a b) (hp : L.PathModelExpansive p)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat L.indexed) (L.sigOf a S))
    (φ : ((IndexedCoInst.flat L.indexed).obj (L.sigOf a S)).Sen) :
    SP.Entails φ ↔
      (translate L p S SP).Entails (((IndexedCoInst.flat L.indexed).map (lift L p S)).sen φ) :=
  StrSpec.entails_translate_iff (lift L p S)
    (Silmaril.Proofs.Logic.Institution.Hets.StructuredPaths.corridor_modelExpansive L p hp S) SP φ

/-- Refinement of structured specifications is preserved and reflected by
paths with model expansion. -/
theorem refines_iff (p : Quiver.Path a b) (hp : L.PathModelExpansive p)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (SP SQ : StrSpec (IndexedCoInst.flat L.indexed) (L.sigOf a S)) :
    SP.Refines SQ ↔ (translate L p S SP).Refines (translate L p S SQ) :=
  StrSpec.refines_translate_iff (lift L p S)
    (Silmaril.Proofs.Logic.Institution.Hets.StructuredPaths.corridor_modelExpansive L p hp S) SP SQ

/-- Model existence is preserved and reflected under the same coverage
hypothesis, so translating a satisfiable specification remains nonvacuous. -/
theorem models_nonempty_iff (p : Quiver.Path a b) (hp : L.PathModelExpansive p)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat L.indexed) (L.sigOf a S)) :
    SP.models.Nonempty ↔ (translate L p S SP).models.Nonempty := by
  constructor
  · rintro ⟨M, member⟩
    obtain ⟨N, rfl⟩ :=
      Silmaril.Proofs.Logic.Institution.Hets.StructuredPaths.corridor_modelExpansive L p hp S M
    exact ⟨N, member⟩
  · rintro ⟨M, member⟩
    exact ⟨((IndexedCoInst.flat L.indexed).map (lift L p S)).mod.obj M, member⟩

/-- Translate then hide recovers the exact source model class. -/
theorem models_hide_translate (p : Quiver.Path a b) (hp : L.PathModelExpansive p)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat L.indexed) (L.sigOf a S)) :
    (hide L p S (translate L p S SP)).models = SP.models :=
  StrSpec.models_hide_translate (lift L p S)
    (Silmaril.Proofs.Logic.Institution.Hets.StructuredPaths.corridor_modelExpansive L p hp S) SP

end Silmaril.Logic.Institution.Hets.StructuredPaths
