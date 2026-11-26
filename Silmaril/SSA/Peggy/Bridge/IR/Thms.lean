module

public import Silmaril.SSA.Peggy.Bridge.IR.Defs
public import Silmaril.SSA.PEG.Bridge.MLIR.Thms
public import Silmaril.SSA.RVSDG.MLIR.Regionless.Thms
public import Silmaril.Logic.Institution.Borrowing
import Silmaril.Proofs.SSA.Peggy.Bridge.IR.Naturality
import Silmaril.Proofs.SSA.Peggy.Bridge.IR.Satisfaction

/-! # Bundled comorphisms for the ordered Peggy value fragment -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.IR

open CategoryTheory
open Dialect (FixedSortSignature)
open PEG.Bridge
open Silmaril.Inst (Plain Comorphism)
open Silmaril.Logic.Institution (Inst)
open Silmaril.SSA.RVSDG.MLIR

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {S T : FixedSortSignature.{0,0} Data}

theorem translateEquation_map (f : S ⟶ T) (e : PEG.Bridge.Equation S.ops) :
    (mapPEG f e).toRVSDG = e.toRVSDG.map (mapOpcode (FixedSortSignature.opcodeMap f)) :=
  Proofs.translateEquation_map f e

theorem translate_regionless_map (f : S ⟶ T) (e : Regionless.ValueEquation (Opcode S.ops)) :
    Regionless.translateEquation (profileMap T.ops) (e.map (mapOpcode (FixedSortSignature.opcodeMap f))) =
      (Regionless.translateEquation (profileMap S.ops) e).map ((mlirSignature Data).map f) :=
  Proofs.translate_regionless_map f e

theorem peg_rvsdg_satisfaction (e : PEG.Bridge.Equation S.ops) (m : TotalModel S.ops) :
    e.toRVSDG.toRVSDG.Holds m.toRVSDG ↔ (toPeggy e).Holds (toTotalPrimitive m).val :=
  Proofs.peg_rvsdg_satisfaction e m

theorem rvsdg_mlir_satisfaction (e : Regionless.ValueEquation (Opcode S.ops)) (m : TotalModel S.ops) :
    (Regionless.translateEquation (profileMap S.ops) e).Holds m.toMLIR ↔ e.toRVSDG.Holds m.toRVSDG :=
  Proofs.rvsdg_mlir_satisfaction e m

theorem mapPEG_id (e : PEG.Bridge.Equation S.ops) : mapPEG (𝟙 S) e = e :=
  Proofs.mapPEG_id e

theorem mapPEG_comp {U : FixedSortSignature.{0,0} Data} (f : S ⟶ T) (g : T ⟶ U)
    (e : PEG.Bridge.Equation S.ops) : mapPEG (f ≫ g) e = mapPEG g (mapPEG f e) :=
  Proofs.mapPEG_comp f g e

theorem toPeggy_map (f : S ⟶ T) (e : PEG.Bridge.Equation S.ops) :
    toPeggy (mapPEG f e) = (toPeggy e).map f :=
  Proofs.toPeggy_map f e

theorem toTotalPrimitive_reduct (f : S ⟶ T) (m : TotalModel T.ops) :
    toTotalPrimitive (reduct f m) = Equational.totalPrimitiveReduct f (toTotalPrimitive m) :=
  Proofs.toTotalPrimitive_reduct f m

theorem recover_total (m : Equational.TotalPrimitiveModel S) :
    toTotalPrimitive (fromTotalPrimitive m) = m :=
  Proofs.recover_total m

theorem rvsdg_reduct (f : S ⟶ T) (m : TotalModel T.ops) :
    RVSDG.Institution.reduct (mapOpcode (FixedSortSignature.opcodeMap f)) m.toRVSDG =
      (reduct f m).toRVSDG :=
  Proofs.rvsdg_reduct f m

theorem mlir_reduct (f : S ⟶ T) (m : TotalModel T.ops) :
    m.toMLIR.reduct (mapSymbol f) = (reduct f m).toMLIR :=
  Proofs.mlir_reduct f m

theorem rvsdg_value_map_id (e : Regionless.ValueEquation (Opcode S.ops)) :
    e.map (mapOpcode (FixedSortSignature.opcodeMap (𝟙 S))) = e :=
  Proofs.rvsdg_value_map_id e

theorem rvsdg_value_map_comp {U : FixedSortSignature.{0,0} Data} (f : S ⟶ T) (g : T ⟶ U)
    (e : Regionless.ValueEquation (Opcode S.ops)) :
    e.map (mapOpcode (FixedSortSignature.opcodeMap (f ≫ g))) =
      (e.map (mapOpcode (FixedSortSignature.opcodeMap f))).map (mapOpcode (FixedSortSignature.opcodeMap g)) :=
  Proofs.rvsdg_value_map_comp f g e

/-- Restrict actual Peggy sentences to the ordered, empty-loop fragment and
retain the total-primitive models and satisfaction of the upstream institution. -/
def pegPlain (Data : Type) : Plain.{1,0,0,1} (FixedSortSignature.{0,0} Data) where
  Sen S := PEG.Bridge.Equation S.ops
  map := mapPEG
  map_id _ := mapPEG_id
  map_comp := mapPEG_comp
  Mod := Equational.TotalPrimitiveModel
  reduct := Equational.totalPrimitiveReduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := (toPeggy e).Holds m.val
  sat_map f m e :=
    (Iff.of_eq (congrArg (fun sentence : Dialect.Equation _ => sentence.Holds m.val) (toPeggy_map f e))).trans
      (Dialect.Equation.holds_map f m.val (toPeggy e))

/-- Regard any total-primitive model as an ordinary Peggy model. -/
def restrictPeggyModels (Data : Type) :
    Comorphism (Silmaril.SSA.Peggy.Institution.inst.{0,0,0} Data) (Equational.totalPrimitiveInst Data) :=
  Comorphism.ofPlain (P := Silmaril.SSA.Peggy.Institution.plain.{0,0,0} Data)
    (Q := Equational.totalPrimitivePlain Data) (𝟭 _) (fun _ e => e) (fun _ m => m.val)
    (fun _ _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Forget the sentence restriction into the actual total-primitive Peggy
institution. The model translation is the identity on that model type. -/
def includePeggy (Data : Type) : Comorphism (pegPlain Data).toInst (Equational.totalPrimitiveInst Data) :=
  Comorphism.ofPlain (P := pegPlain Data) (Q := Equational.totalPrimitivePlain Data)
    (𝟭 _) (fun _ e => toPeggy e) (fun _ m => m) (fun _ _ _ => Iff.rfl)
    toPeggy_map (fun _ _ => rfl)

/-- The RVSDG value equation family in the induced models. Satisfaction uses
the canonical numbered graph equations. -/
def rvsdgPlain (Data : Type) : Plain.{1,0,0,1} (FixedSortSignature.{0,0} Data) where
  Sen S := Regionless.ValueEquation (Opcode S.ops)
  map f e := e.map (mapOpcode (FixedSortSignature.opcodeMap f))
  map_id _ := rvsdg_value_map_id
  map_comp := rvsdg_value_map_comp
  Mod S := TotalModel S.ops
  reduct := reduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := e.toRVSDG.Holds m.toRVSDG
  sat_map f m e := by
    rw [Regionless.ValueEquation.toRVSDG_map, ← rvsdg_reduct f m]
    exact RVSDG.Institution.Equation.satisfaction _ _ _

/-- Canonical regionless MLIR equations at the generated signatures, with
models presented by their total PEG interpretations. -/
def mlirPlain (Data : Type) : Plain.{1,0,0,1} (FixedSortSignature.{0,0} Data) where
  Sen S := Silmaril.MLIR.Institution.Equation (PEG.Bridge.signature S.ops)
  map f e := e.map ((mlirSignature Data).map f)
  map_id S e :=
    (congrArg (fun h : (mlirSignature Data).obj S ⟶ (mlirSignature Data).obj S => e.map h)
      ((mlirSignature Data).map_id S)).trans e.map_id
  map_comp f g e :=
    (congrArg (fun h => e.map h) ((mlirSignature Data).map_comp f g)).trans (e.map_comp _ _)
  Mod S := TotalModel S.ops
  reduct := reduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := e.Holds m.toMLIR
  sat_map f m e :=
    (Silmaril.MLIR.Institution.satisfaction (mapSymbol f) m.toMLIR e).trans
      (Iff.of_eq (congrArg e.Holds (mlir_reduct f m)))

/-- PEG sentences compile to numbered RVSDG equations. A target model pulls
back to its guarded total-primitive PEG interpretation. -/
def peggyToRVSDG (Data : Type) : Comorphism (pegPlain Data).toInst (rvsdgPlain Data).toInst :=
  Comorphism.ofPlain (P := pegPlain Data) (Q := rvsdgPlain Data)
    (𝟭 _) (fun _ e => PEG.Bridge.Equation.toRVSDG e) (fun _ m => toTotalPrimitive m)
    (fun _ m e => peg_rvsdg_satisfaction e m) translateEquation_map
    (fun f m => (toTotalPrimitive_reduct f m).symm)

/-- Reuse the RVSDG–MLIR regionless profile translation. On the chosen model
presentations the model map is identity, since the real MLIR profile pullback
equals the induced RVSDG model. -/
def rvsdgToMLIR (Data : Type) : Comorphism (rvsdgPlain Data).toInst (mlirPlain Data).toInst :=
  Comorphism.ofPlain (P := rvsdgPlain Data) (Q := mlirPlain Data)
    (𝟭 _) (fun S => Regionless.translateEquation (profileMap S.ops)) (fun _ m => m)
    (fun _ m e => rvsdg_mlir_satisfaction e m) translate_regionless_map (fun _ _ => rfl)

def peggyToMLIR (Data : Type) : Comorphism (pegPlain Data).toInst (mlirPlain Data).toInst :=
  Inst.CoHom.comp (peggyToRVSDG Data) (rvsdgToMLIR Data)

/-- Every total Peggy model has an induced regionless MLIR expansion. -/
theorem peggyToMLIR_modelExpansive (Data : Type) : (peggyToMLIR Data).ModelExpansive :=
  fun _ m => ⟨fromTotalPrimitive m, recover_total m⟩

end Silmaril.SSA.Peggy.Bridge.IR
