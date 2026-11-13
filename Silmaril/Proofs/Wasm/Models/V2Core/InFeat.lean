module

public import Silmaril.Proofs.Wasm.Models.V2Core.Host
public import Silmaril.Wasm.Models.Syntax.Thms

/-!
# The Core image of 2.0 code is in `v20`

* `has_v20`: the capabilities of `v20` the image uses;
* `instr_inFeat`, `expr_inFeat`: the Core image of a 2.0 instruction (sequence) is in `v20`
  (`Instr.inFeatB v20`);
* `storeIn_image`: every Wasm function of the Core image of a 2.0 store has a body in `v20`
  (`Rt.StoreIn v20`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core

/-- The capabilities of `v20` the 2.0 image uses. -/
theorem has_v20 : ∀ c ∈ mvpCaps ++ caps20, v20.has c = true := by decide

@[simp] theorem v20_intNum : v20.has .intNum = true := by decide
@[simp] theorem v20_floatNum : v20.has .floatNum = true := by decide
@[simp] theorem v20_control : v20.has .control = true := by decide
@[simp] theorem v20_directCall : v20.has .directCall = true := by decide
@[simp] theorem v20_memory : v20.has .memory = true := by decide
@[simp] theorem v20_table : v20.has .table = true := by decide
@[simp] theorem v20_callIndirect : v20.has .callIndirect = true := by decide
@[simp] theorem v20_globals : v20.has .globals = true := by decide
@[simp] theorem v20_mutGlobal : v20.has .mutGlobal = true := by decide
@[simp] theorem v20_signExt : v20.has .signExt = true := by decide
@[simp] theorem v20_satConv : v20.has .satConv = true := by decide
@[simp] theorem v20_multiValue : v20.has .multiValue = true := by decide
@[simp] theorem v20_refTypes : v20.has .refTypes = true := by decide
@[simp] theorem v20_bulkMemory : v20.has .bulkMemory = true := by decide
@[simp] theorem v20_bulkMemoryOpt : v20.has .bulkMemoryOpt = true := by decide
@[simp] theorem v20_simd : v20.has .simd = true := by decide

theorem valType_v20 (t : Silmaril.Wasm.V2.ValType) : ValType.inFeatB v20 t.toCore = true := by
  rcases t with (_ | _) | _ | (_ | _) <;>
    simp [Silmaril.Wasm.V2.ValType.toCore, Silmaril.Wasm.V2.RefType.toCore, ValType.inFeatB,
      RefType.inFeatB, HeapType.inFeatB, AbsHeapType.inFeatB]

theorem blockType_v20 (t : Silmaril.Wasm.V2.BlockType) :
    BlockType.inFeatB v20 t.toCore = true := by
  rcases t with (_ | t) | _
  · rfl
  · exact valType_v20 t
  · simp [Silmaril.Wasm.V2.BlockType.toCore, BlockType.inFeatB]

theorem convert_v20 (op : Silmaril.Wasm.ConvertOp) : ConvertOp.inFeatB v20 op = true := by
  cases op <;> simp [ConvertOp.inFeatB]

theorem refNull_v20 (t : Silmaril.Wasm.V2.RefType) :
    HeapType.inFeatB v20 t.toCoreHeap = true := by
  cases t <;> decide

theorem memIdx_v20 : memIdxB v20 ⟨0⟩ = true := by decide

theorem tblIdx_v20 (x : Silmaril.Wasm.TableIdx) : tblIdxB v20 x = true := by
  simp [tblIdxB, v20_table, v20_refTypes]

/-- The image of a 2.0 vector operator is not relaxed. -/
theorem vecB_v20 {i : Instr} (h : Instr.isRelaxed i = false) : vecB v20 i = true := by
  simp [vecB, h]

theorem intUnOp_v20 (op : IntUnOp) : IntUnOp.inFeatB v20 op = true := by
  cases op <;> simp [IntUnOp.inFeatB]

@[simp] theorem relaxed_vecIntBinOp (s : Silmaril.Wasm.IntShape)
    (op : Silmaril.Wasm.V2.VecIntBinOp) :
    Instr.isRelaxed (.vecIntBinOp s op.toCore) = false := by
  cases op <;> rfl

@[simp] theorem relaxed_vecFloatBinOp (s : Silmaril.Wasm.FloatShape)
    (op : Silmaril.Wasm.V2.VecFloatBinOp) :
    Instr.isRelaxed (.vecFloatBinOp s op.toCore) = false := by
  cases op <;> rfl

@[simp] theorem relaxed_vecExtBinOp (s t : Silmaril.Wasm.IntShape)
    (op : Silmaril.Wasm.V2.VecExtBinOp) :
    Instr.isRelaxed (.vecExtBinOp s t op.toCore) = false := by
  cases op <;> rfl

@[simp] theorem relaxed_vecConvert (s t : Silmaril.Wasm.Shape)
    (op : Silmaril.Wasm.V2.VecCvtOp) :
    Instr.isRelaxed (.vecConvert s t op.toCore) = false := by
  cases op <;> rfl

theorem select_v20 (types : Option (List Silmaril.Wasm.V2.ValType)) :
    Instr.inFeatB v20 (.select (types.map Silmaril.Wasm.V2.ResultType.toCore)) = true := by
  cases types <;>
    simp [Instr.inFeatB, Instr.headB, Silmaril.Wasm.V2.ResultType.toCore, valType_v20]

/-- A 2.0 instruction without bodies. -/
def isFlat : Silmaril.Wasm.V2.Instr → Bool
  | .block _ _ | .loop _ _ | .if_ _ _ _ => false
  | _ => true

set_option linter.unusedTactic false in
/-- The Core image of a 2.0 instruction without bodies is in `v20`. -/
theorem flat_inFeat (i : Silmaril.Wasm.V2.Instr) {c : Instr}
    (h : Silmaril.Wasm.V2.Instr.toCore i = some c) (hf : isFlat i = true) :
    Instr.inFeatB v20 c = true := by
  cases i <;> simp only [isFlat, Bool.false_eq_true] at hf <;>
    simp only [Silmaril.Wasm.V2.Instr.toCore, Option.some.injEq] at h <;>
    first
    | exact h ▸ select_v20 _
    | (subst h
       simp [Instr.inFeatB, Instr.headB, vecB, intUnOp_v20, refNull_v20, tblIdx_v20, memIdxB]
       try exact Or.inl rfl)
    | (obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.mp h
       simp [Instr.inFeatB, Instr.headB, convert_v20])

theorem block_inFeat (t : Silmaril.Wasm.V2.BlockType) {cb : List Instr}
    (hb : Instr.insInFeatB v20 cb = true) : Instr.inFeatB v20 (.block t.toCore cb) = true := by
  simp [Instr.inFeatB, Instr.headB, blockType_v20, hb]

theorem loop_inFeat (t : Silmaril.Wasm.V2.BlockType) {cb : List Instr}
    (hb : Instr.insInFeatB v20 cb = true) : Instr.inFeatB v20 (.loop t.toCore cb) = true := by
  simp [Instr.inFeatB, Instr.headB, blockType_v20, hb]

theorem if_inFeat (t : Silmaril.Wasm.V2.BlockType) {cl cr : List Instr}
    (hl : Instr.insInFeatB v20 cl = true) (hr : Instr.insInFeatB v20 cr = true) :
    Instr.inFeatB v20 (.if_ t.toCore cl cr) = true := by
  simp [Instr.inFeatB, Instr.headB, blockType_v20, hl, hr]

mutual

/-- **The Core image of a 2.0 instruction is in `v20`.** -/
theorem instr_inFeat : (i : Silmaril.Wasm.V2.Instr) → ∀ {c : Instr},
    Silmaril.Wasm.V2.Instr.toCore i = some c → Instr.inFeatB v20 c = true := by
  intro i c h
  cases i with
  | block t body =>
    obtain ⟨cb, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact block_inFeat t (expr_inFeat body hb)
  | loop t body =>
    obtain ⟨cb, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact loop_inFeat t (expr_inFeat body hb)
  | if_ t l r =>
    obtain ⟨cl, hl, cr, hr, rfl⟩ : ∃ cl, Silmaril.Wasm.V2.Expr.toCore l = some cl ∧
        ∃ cr, Silmaril.Wasm.V2.Expr.toCore r = some cr ∧ .if_ t.toCore cl cr = c := by
      simpa [Silmaril.Wasm.V2.Instr.toCore, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] using h
    exact if_inFeat t (expr_inFeat l hl) (expr_inFeat r hr)
  | _ => exact flat_inFeat _ h rfl

/-- The Core image of a 2.0 instruction sequence is in `v20`. -/
theorem expr_inFeat : (e : List Silmaril.Wasm.V2.Instr) → ∀ {cs : List Instr},
    Silmaril.Wasm.V2.Expr.toCore e = some cs → Instr.insInFeatB v20 cs = true := by
  intro e cs h
  cases e with
  | nil =>
    cases h
    rfl
  | cons i e =>
    simp only [Silmaril.Wasm.V2.Expr.toCore, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨c, hc, cs', hcs', rfl⟩ := h
    simp [Instr.insInFeatB, instr_inFeat i hc, expr_inFeat e hcs']

end

/-- The Core image of a 2.0 function instance has a body in `v20`. -/
theorem funcInst_inFeat {H : Type} {fi : Silmaril.Wasm.V2.Execution.FuncInst H}
    {ci : Silmaril.Wasm.Execution.Core.FuncInst H}
    (h : Silmaril.Wasm.V2.Execution.FuncInst.toCore fi = some ci) {fn : Func}
    (hc : ci.code = .wasm fn) : Instr.insInFeatB v20 fn.body = true := by
  unfold Silmaril.Wasm.V2.Execution.FuncInst.toCore at h
  split at h
  · obtain ⟨c, hc', rfl⟩ := Option.map_eq_some_iff.mp h
    cases hc
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hc'
    exact expr_inFeat _ hb
  · cases h
    cases hc

/-- **The Core image of a 2.0 store is in `v20`.** -/
theorem storeIn_image {H : Type} {s : VStore H} {X : CStore H}
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) : Rt.StoreIn v20 X := by
  intro a ci fn ha hc
  obtain ⟨fs, hfs, rfl⟩ := toCore_eq_some.mp hX
  have hget := Silmaril.Wasm.V2.Execution.ToCoreSim.mapM_funcInst_getElem hfs a
  have ha' : fs[a]? = some ci := ha
  rw [ha'] at hget
  cases hfi : s.funcs[a]? with
  | none =>
    rw [hfi] at hget
    cases hget
  | some fi =>
    rw [hfi] at hget
    exact funcInst_inFeat hget.symm hc

end Silmaril.Proofs.Wasm.Models.V2Core
