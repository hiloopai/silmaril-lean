module

public import Silmaril.SSA.Peggy.Bridge.IR.Thms

/-! # Compare the induced models with the canonical IR institutions -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.IR

open CategoryTheory
open Dialect (FixedSortSignature)
open PEG.Bridge (TotalModel Opcode)
open Silmaril.Inst (Plain Comorphism Institution)
open Silmaril.Logic.Institution (Room Corridor)
open Silmaril.SSA.RVSDG.MLIR

set_option backward.isDefEq.respectTransparency false

/-- Use Mathlib's discrete model categories. This retains the sentences,
models, reducts and satisfaction of the plain presentation, at the model
hom universe of the canonical IR rooms. -/
def mathlibDiscrete {Sign : Type 1} [Category.{0} Sign] (P : Plain.{1,0,0,1} Sign) :
    Institution.{1,0,0,1,1} :=
  Institution.ofFunctor {
    obj S := ⟨P.Sen S, Cat.of (Discrete (P.Mod S)), fun m e => P.Sat m.as e⟩
    map f := ⟨P.map f, Discrete.functor (fun m => Discrete.mk (P.reduct f m)),
      fun m e => P.sat_map f m.as e⟩
    map_id S := Room.hom_ext (funext (P.map_id S))
      (CategoryTheory.Functor.ext (fun (m : Discrete (P.Mod S)) => congrArg Discrete.mk (P.reduct_id S m.as)))
    map_comp {_ _ U} f g := Room.hom_ext (funext (P.map_comp f g))
      (CategoryTheory.Functor.ext (fun (m : Discrete (P.Mod U)) => congrArg Discrete.mk (P.reduct_comp f g m.as))) }

/-- Carry a plain comorphism into the same discrete model convention as
the canonical IR comparisons. Its signature and sentence maps are retained. -/
def mathlibDiscreteComorphism {Sign Sign' : Type 1} [Category.{0} Sign] [Category.{0} Sign']
    {P : Plain.{1,0,0,1} Sign} {Q : Plain.{1,0,0,1} Sign'} (f : Comorphism P.toInst Q.toInst) :
    Comorphism (mathlibDiscrete P) (mathlibDiscrete Q) :=
  Comorphism.ofTranslation (A := mathlibDiscrete P) (B := mathlibDiscrete Q) f.Φ
    (fun S => (f.ρ.app S).sen)
    (fun S => Discrete.functor (fun m => Discrete.mk ((f.ρ.app S).mod.obj m)))
    (fun S m e => (f.ρ.app S).sat m.as e)
    (fun h e => congrFun (congrArg Corridor.sen (f.ρ.naturality h)) e)
    (fun {S T} h => CategoryTheory.Functor.ext (fun (m : Discrete (Q.Mod (f.Φ.obj T))) =>
      congrArg (fun (c : P.room S ⟶ Q.room (f.Φ.obj T)) => Discrete.mk (c.mod.obj m.as))
        (f.ρ.naturality h)))

abbrev canonicalRVSDG (Data : Type) :=
  Institution.ofFunctor (rvsdgSignature Data ⋙
    (RVSDG.Institution.inst.{0,0,0} (PEG.Ty Data) PUnit).I)

abbrev canonicalMLIR (Data : Type) :=
  Institution.ofFunctor (mlirSignature Data ⋙ Silmaril.MLIR.Institution.institution (withRegions := false))

/-- The canonical RVSDG sentences and changes of signature with just the
induced models. This ambient room also allows non-value boundaries. -/
def rvsdgAllPlain (Data : Type) : Plain.{1,0,0,1} (FixedSortSignature.{0,0} Data) where
  Sen S := ((canonicalRVSDG Data).I.obj S).Sen
  map f := ((canonicalRVSDG Data).I.map f).sen
  map_id S e := congrFun (congrArg Corridor.sen ((canonicalRVSDG Data).I.map_id S)) e
  map_comp f g e := congrFun (congrArg Corridor.sen ((canonicalRVSDG Data).I.map_comp f g)) e
  Mod S := TotalModel S.ops
  reduct := reduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := e.Holds m.toRVSDG
  sat_map f m e :=
    (RVSDG.Institution.Equation.satisfaction (mapOpcode (FixedSortSignature.opcodeMap f)) e m.toRVSDG).trans
      (Iff.of_eq (congrArg e.Holds (rvsdg_reduct f m)))

/-- Restrict the canonical RVSDG models along the induced model family.
The original equation is unchanged and a chosen model expands to its
actual numbered RVSDG interpretation. -/
def restrictRVSDGModels (Data : Type) :
    Comorphism (canonicalRVSDG Data) (mathlibDiscrete (rvsdgAllPlain Data)) :=
  Comorphism.ofTranslationId (Sign := FixedSortSignature.{0,0} Data) (I := (canonicalRVSDG Data).I)
    (J := (mathlibDiscrete (rvsdgAllPlain Data)).I) (fun _ e => e)
    (fun S => Discrete.functor (fun m : TotalModel S.ops => Discrete.mk m.toRVSDG))
    (fun _ _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun {_ T} f => CategoryTheory.Functor.ext (fun (m : Discrete (TotalModel T.ops)) =>
      congrArg Discrete.mk (rvsdg_reduct f m.as)))

/-- Include the value-boundary equations in the canonical RVSDG equations
on the same induced models. -/
def includeRVSDGValues (Data : Type) :
    Comorphism (mathlibDiscrete (rvsdgPlain Data)) (mathlibDiscrete (rvsdgAllPlain Data)) :=
  Comorphism.ofTranslationId (Sign := FixedSortSignature.{0,0} Data) (I := (mathlibDiscrete (rvsdgPlain Data)).I)
    (J := (mathlibDiscrete (rvsdgAllPlain Data)).I) (fun _ e => Regionless.ValueEquation.toRVSDG e)
    (fun _ => 𝟭 _) (fun _ _ _ => Iff.rfl)
    (fun f e => Regionless.ValueEquation.toRVSDG_map e (mapOpcode (FixedSortSignature.opcodeMap f)))
    (fun _ => rfl)

/-- Restrict the canonical regionless MLIR models along the induced model
family. The sentence is the original canonical equation. -/
def restrictMLIRModels (Data : Type) :
    Comorphism (canonicalMLIR Data) (mathlibDiscrete (mlirPlain Data)) :=
  Comorphism.ofTranslationId (Sign := FixedSortSignature.{0,0} Data) (I := (canonicalMLIR Data).I)
    (J := (mathlibDiscrete (mlirPlain Data)).I) (fun _ e => e)
    (fun S => Discrete.functor (fun m : TotalModel S.ops => Discrete.mk m.toMLIR))
    (fun _ _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun {_ T} f => CategoryTheory.Functor.ext (fun (m : Discrete (TotalModel T.ops)) =>
      congrArg Discrete.mk (mlir_reduct f m.as)))

end Silmaril.SSA.Peggy.Bridge.IR
