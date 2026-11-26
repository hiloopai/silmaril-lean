module

public import Silmaril.SSA.Peggy.Bridge.IR.Defs
public import Silmaril.SSA.PEG.Bridge.MLIR.Thms
public import Silmaril.SSA.RVSDG.MLIR.Regionless.Thms

public section

namespace Silmaril.SSA.Peggy.Bridge.IR.Proofs

open CategoryTheory
open Dialect (FixedSortSignature)
open PEG.Bridge
open Silmaril.SSA.RVSDG.MLIR

variable {Data : Type} {S T U : FixedSortSignature.{0,0} Data}

theorem toPeggy_map (f : S ⟶ T) (e : PEG.Bridge.Equation S.ops) :
    toPeggy (mapPEG f e) = (toPeggy e).map f := rfl

theorem toTotalPrimitive_reduct (f : S ⟶ T) (m : TotalModel T.ops) :
    toTotalPrimitive (reduct f m) = Equational.totalPrimitiveReduct f (toTotalPrimitive m) := rfl

theorem recover_total (m : Equational.TotalPrimitiveModel S) :
    toTotalPrimitive (fromTotalPrimitive m) = m := by
  apply Subtype.ext
  apply congrArg (PEG.Interpretation.mk m.val.carrier)
  funext ins out op args
  exact Option.some_get (m.property op args)

theorem rvsdg_reduct (f : S ⟶ T) (m : TotalModel T.ops) :
    RVSDG.Institution.reduct (mapOpcode (FixedSortSignature.opcodeMap f)) m.toRVSDG =
      (reduct f m).toRVSDG := by
  apply congrArg (RVSDG.Model.mk (Op := Opcode S.ops) m.toPEG.Value (fun _ => PEmpty))
  funext ins outs op args
  cases op with
  | apply op =>
    cases op with
    | primitive => rfl
    | copy =>
      cases args with | cons x tail => cases tail; rfl
    | select =>
      cases args with | cons flag tail =>
      cases tail with | cons x tail =>
      cases tail with | cons y tail => cases tail; rfl

theorem mlir_reduct (f : S ⟶ T) (m : TotalModel T.ops) :
    m.toMLIR.reduct (mapSymbol f) = (reduct f m).toMLIR := by
  apply congrArg (Silmaril.MLIR.Institution.Model.mk (S := PEG.Bridge.signature S.ops) m.toPEG.Value)
  funext arity profile op args regions
  cases op with
  | apply op => cases op <;> rfl

theorem rvsdg_value_map_id (e : Regionless.ValueEquation (Opcode S.ops)) :
    e.map (mapOpcode (FixedSortSignature.opcodeMap (𝟙 S))) = e := by
  have identity : @mapOpcode _ S.ops S.ops (fun op => op) = fun {_ _} op => op := by
    funext _ _ op
    cases op with | apply op => cases op <;> rfl
  cases e
  simp only [FixedSortSignature.opcodeMap_id, identity, Regionless.ValueEquation.map,
    RVSDG.Institution.mapGraph_id]

theorem rvsdg_value_map_comp (f : S ⟶ T) (g : T ⟶ U) (e : Regionless.ValueEquation (Opcode S.ops)) :
    e.map (mapOpcode (FixedSortSignature.opcodeMap (f ≫ g))) =
      (e.map (mapOpcode (FixedSortSignature.opcodeMap f))).map
        (mapOpcode (FixedSortSignature.opcodeMap g)) := by
  let op (f : S ⟶ T) := @mapOpcode _ S.ops T.ops (FixedSortSignature.opcodeMap f)
  have compose :
      @mapOpcode _ S.ops U.ops (FixedSortSignature.opcodeMap (f ≫ g)) =
        fun {_ _} x => mapOpcode (FixedSortSignature.opcodeMap g) (op f x) := by
    funext _ _ x
    cases x with | apply x => cases x <;> rfl
  cases e
  simp only [compose, Regionless.ValueEquation.map, RVSDG.Institution.mapGraph_comp]
  rfl

theorem peg_holds (e : PEG.Bridge.Equation S.ops) (m : TotalModel S.ops) :
    (toPeggy e).Holds m.toPEG ↔ e.Holds m := Iff.rfl

theorem peg_rvsdg_satisfaction (e : PEG.Bridge.Equation S.ops) (m : TotalModel S.ops) :
    e.toRVSDG.toRVSDG.Holds m.toRVSDG ↔ (toPeggy e).Holds (toTotalPrimitive m).val :=
  (e.rvsdg_satisfaction m).trans (peg_holds e m).symm

theorem rvsdg_mlir_satisfaction (e : Regionless.ValueEquation (Opcode S.ops)) (m : TotalModel S.ops) :
    (Regionless.translateEquation (profileMap S.ops) e).Holds m.toMLIR ↔
      e.toRVSDG.Holds m.toRVSDG := by
  rw [Regionless.satisfaction, PEG.Bridge.pullback_toMLIR]

end Silmaril.SSA.Peggy.Bridge.IR.Proofs
