module

public import Silmaril.Proofs.Wasm.Models.Lime1Mvp.Lime1

/-!
# Wasm 1.0 code lands in the `v10` profile, through Lime1

The 1.0 model `v10own` runs 1.0 code through its Lime1 image (`Func.toLime`), and the Lime1
code reaches Core through `Lime1.Instr.toCore`. The image of 1.0 code is in the MVP profile
`v10`, not only in `lime1`:

* `blockType_v10`, `intUnOp_v10`, `convert_v10`: the 1.0 immediates land in `v10` (no
  multi-value block types, no sign-extension operators, no saturating conversions);
* **`instr_inFeat_v10`**, **`expr_inFeat_v10`**: the Core image of a 1.0 instruction
  (sequence) is in `v10`; `lime_expr_inFeat_v10`: so is the Core image of its Lime1 image (the
  two agree, `Expr.toLime_toCore`);
* **`storeIn_v10`**: every Wasm function of the Core image of the Lime1 image of a 1.0 store
  has a body in `v10` (`Rt.StoreIn v10`), the runtime restriction the component engine uses
  (`lime1RT`, `core3LRG_sem_eq_of_inFeat` are stated for `lime1`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Lime1Mvp

open Silmaril.Wasm Silmaril.Wasm.Models

@[simp] theorem v10_intNum : v10.has .intNum = true := by decide
@[simp] theorem v10_floatNum : v10.has .floatNum = true := by decide
@[simp] theorem v10_control : v10.has .control = true := by decide
@[simp] theorem v10_directCall : v10.has .directCall = true := by decide
@[simp] theorem v10_memory : v10.has .memory = true := by decide
@[simp] theorem v10_table : v10.has .table = true := by decide
@[simp] theorem v10_callIndirect : v10.has .callIndirect = true := by decide
@[simp] theorem v10_globals : v10.has .globals = true := by decide
@[simp] theorem v10_mutGlobal : v10.has .mutGlobal = true := by decide
@[simp] theorem v10_signExt : v10.has .signExt = false := by decide
@[simp] theorem v10_satConv : v10.has .satConv = false := by decide
@[simp] theorem v10_multiValue : v10.has .multiValue = false := by decide
@[simp] theorem v10_refTypes : v10.has .refTypes = false := by decide

theorem blockType_v10 (t : Silmaril.Wasm.V1.BlockType) :
    BlockType.inFeatB v10 t.toCore = true := by
  cases t with
  | none => rfl
  | some v => cases v <;> rfl

theorem convert_v10 (op : Silmaril.Wasm.V1.ConvertOp) :
    ConvertOp.inFeatB v10 op.toCore = true := by
  cases op <;> rfl

theorem intUnOp_v10 (op : Silmaril.Wasm.V1.IntUnOp) :
    IntUnOp.inFeatB v10 op.toCore = true := by
  cases op <;> rfl

mutual

/-- **The Core image of a 1.0 instruction is in `v10`.** -/
theorem instr_inFeat_v10 : (i : Silmaril.Wasm.V1.Instr) →
    Instr.inFeatB v10 i.toCore = true
  | .block t body => by
    simp [Silmaril.Wasm.V1.Instr.toCore, Instr.inFeatB, Instr.headB, blockType_v10,
      expr_inFeat_v10 body]
  | .loop t body => by
    simp [Silmaril.Wasm.V1.Instr.toCore, Instr.inFeatB, Instr.headB, blockType_v10,
      expr_inFeat_v10 body]
  | .if_ t l r => by
    simp [Silmaril.Wasm.V1.Instr.toCore, Instr.inFeatB, Instr.headB, blockType_v10,
      expr_inFeat_v10 l, expr_inFeat_v10 r]
  | .convert op => by
    simp [Silmaril.Wasm.V1.Instr.toCore, Instr.inFeatB, Instr.headB, convert_v10]
  | .intUnOp t op => by
    simp [Silmaril.Wasm.V1.Instr.toCore, Instr.inFeatB, Instr.headB, intUnOp_v10]
  | .nop | .unreachable | .drop | .select | .br _ | .brIf _ | .brTable _ _ | .call _
  | .callIndirect _ | .return_ | .localGet _ | .localSet _ | .localTee _ | .globalGet _
  | .globalSet _ | .intLoad _ _ _ | .floatLoad _ _ | .intStore _ _ _ | .floatStore _ _
  | .memorySize | .memoryGrow | .intConst _ _ | .floatConst _ _
  | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ | .floatUnOp _ _ | .floatBinOp _ _
  | .floatRelOp _ _ => by
    simp only [Silmaril.Wasm.V1.Instr.toCore, Instr.inFeatB, Instr.headB, memIdxB, tblIdxB]
    decide

/-- The Core image of a 1.0 instruction sequence is in `v10`. -/
theorem expr_inFeat_v10 : (e : List Silmaril.Wasm.V1.Instr) →
    Instr.insInFeatB v10 (Silmaril.Wasm.V1.Expr.toCore e) = true
  | [] => rfl
  | i :: e => by
    simp [Silmaril.Wasm.V1.Expr.toCore, Instr.insInFeatB, instr_inFeat_v10 i, expr_inFeat_v10 e]

end

/-- Through Lime1: the Core image of the Lime1 image of 1.0 code is in `v10`. -/
theorem lime_expr_inFeat_v10 (e : List Silmaril.Wasm.V1.Instr) :
    Instr.insInFeatB v10 (Silmaril.Wasm.Lime1.Expr.toCore (Silmaril.Wasm.V1.Expr.toLime e)) =
      true := by
  rw [Silmaril.Wasm.V1.Expr.toLime_toCore]
  exact expr_inFeat_v10 e

/-- **The Core image of the Lime1 image of a 1.0 store is in `v10`.** -/
theorem storeIn_v10 {H : Type} (s : Silmaril.Wasm.Models.V10.OStore H) :
    Rt.StoreIn v10 (s.mapCode Silmaril.Wasm.V1.Func.toLime).toCore := by
  intro a ci fn ha hc
  have ha' : ((s.mapCode Silmaril.Wasm.V1.Func.toLime).funcs[a]?).map
      Silmaril.Wasm.Execution.Runtime.FuncInst.toCore = some ci := by
    simpa only [Silmaril.Wasm.Execution.Runtime.Store.toCore, List.getElem?_map] using ha
  rw [Silmaril.Wasm.Execution.Runtime.Store.mapCode_funcs_getElem?, Option.map_map,
    Option.map_eq_some_iff] at ha'
  obtain ⟨fi, -, rfl⟩ := ha'
  cases fi with
  | wasm t m c =>
    cases hc
    exact lime_expr_inFeat_v10 c.body
  | host t h => cases hc

end Silmaril.Proofs.Wasm.Models.Lime1Mvp
