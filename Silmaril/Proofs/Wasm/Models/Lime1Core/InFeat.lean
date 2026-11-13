module

public import Silmaril.Proofs.Wasm.Models.Lime1Core.Host
public import Silmaril.Wasm.Models.Syntax.Thms

/-!
# The Core image of Lime1 code is in `lime1`

* `instr_inFeat`, `expr_inFeat`: the Core image of a Lime1 instruction (sequence) is in `lime1`;
* `storeIn_image`: every Wasm function of the Core image of a Lime1 store has a body in `lime1`
  (`Rt.StoreIn lime1`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Lime1Core

open Silmaril.Wasm Silmaril.Wasm.Models

@[simp] theorem lime1_intNum : lime1.has .intNum = true := by decide
@[simp] theorem lime1_floatNum : lime1.has .floatNum = true := by decide
@[simp] theorem lime1_control : lime1.has .control = true := by decide
@[simp] theorem lime1_directCall : lime1.has .directCall = true := by decide
@[simp] theorem lime1_memory : lime1.has .memory = true := by decide
@[simp] theorem lime1_table : lime1.has .table = true := by decide
@[simp] theorem lime1_callIndirect : lime1.has .callIndirect = true := by decide
@[simp] theorem lime1_globals : lime1.has .globals = true := by decide
@[simp] theorem lime1_mutGlobal : lime1.has .mutGlobal = true := by decide
@[simp] theorem lime1_signExt : lime1.has .signExt = true := by decide
@[simp] theorem lime1_satConv : lime1.has .satConv = true := by decide
@[simp] theorem lime1_multiValue : lime1.has .multiValue = true := by decide
@[simp] theorem lime1_bulkMemoryOpt : lime1.has .bulkMemoryOpt = true := by decide
@[simp] theorem lime1_extConst : lime1.has .extConst = true := by decide
@[simp] theorem lime1_refTypes : lime1.has .refTypes = false := by decide

theorem blockType_lime1 (t : Silmaril.Wasm.Lime1.BlockType) :
    BlockType.inFeatB lime1 t.toCore = true := by
  cases t with
  | value v => cases v <;> rfl
  | _ => simp [Silmaril.Wasm.Lime1.BlockType.toCore, BlockType.inFeatB]

theorem convert_lime1 (op : Silmaril.Wasm.ConvertOp) : ConvertOp.inFeatB lime1 op = true := by
  cases op <;> simp [ConvertOp.inFeatB]

theorem intUnOp_lime1 (op : Silmaril.Wasm.Lime1.IntUnOp) :
    IntUnOp.inFeatB lime1 op.toCore = true := by
  cases op <;> simp [IntUnOp.inFeatB, Silmaril.Wasm.Lime1.IntUnOp.toCore]

mutual

/-- **The Core image of a Lime1 instruction is in `lime1`.** -/
theorem instr_inFeat : (i : Silmaril.Wasm.Lime1.Instr) →
    Instr.inFeatB lime1 (Silmaril.Wasm.Lime1.Instr.toCore i) = true
  | .block t body => by
    simp [Silmaril.Wasm.Lime1.Instr.toCore, Instr.inFeatB, Instr.headB, blockType_lime1,
      expr_inFeat body]
  | .loop t body => by
    simp [Silmaril.Wasm.Lime1.Instr.toCore, Instr.inFeatB, Instr.headB, blockType_lime1,
      expr_inFeat body]
  | .if_ t l r => by
    simp [Silmaril.Wasm.Lime1.Instr.toCore, Instr.inFeatB, Instr.headB, blockType_lime1,
      expr_inFeat l, expr_inFeat r]
  | .convert op => by
    simp [Silmaril.Wasm.Lime1.Instr.toCore, Instr.inFeatB, Instr.headB, convert_lime1]
  | .intUnOp t op => by
    simp [Silmaril.Wasm.Lime1.Instr.toCore, Instr.inFeatB, Instr.headB, intUnOp_lime1]
  | .nop | .unreachable | .drop | .select | .br _ | .brIf _ | .brTable _ _ | .call _
  | .callIndirect _ | .return_ | .localGet _ | .localSet _ | .localTee _ | .globalGet _
  | .globalSet _ | .intLoad _ _ _ | .floatLoad _ _ | .intStore _ _ _ | .floatStore _ _
  | .memorySize | .memoryGrow | .memoryFill | .memoryCopy | .intConst _ _ | .floatConst _ _
  | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ | .floatUnOp _ _ | .floatBinOp _ _
  | .floatRelOp _ _ => by
    simp only [Silmaril.Wasm.Lime1.Instr.toCore, Instr.inFeatB, Instr.headB, memIdxB, tblIdxB]
    decide

/-- The Core image of a Lime1 instruction sequence is in `lime1`. -/
theorem expr_inFeat : (e : List Silmaril.Wasm.Lime1.Instr) →
    Instr.insInFeatB lime1 (Silmaril.Wasm.Lime1.Expr.toCore e) = true
  | [] => rfl
  | i :: e => by
    simp [Silmaril.Wasm.Lime1.Expr.toCore, Instr.insInFeatB, instr_inFeat i, expr_inFeat e]

end

/-- **The Core image of a Lime1 store is in `lime1`.** -/
theorem storeIn_image {H : Type} (s : Silmaril.Wasm.Models.V10.LStore H) :
    Rt.StoreIn lime1 s.toCore := by
  intro a ci fn ha hc
  simp only [Silmaril.Wasm.Execution.Runtime.Store.toCore, List.getElem?_map,
    Option.map_eq_some_iff] at ha
  obtain ⟨fi, -, rfl⟩ := ha
  cases fi with
  | wasm t m c =>
    cases hc
    exact expr_inFeat _
  | host t h => cases hc

end Silmaril.Proofs.Wasm.Models.Lime1Core
