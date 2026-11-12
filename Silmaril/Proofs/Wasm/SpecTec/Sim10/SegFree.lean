module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstIter10

/-!
# Core 3.0 instruction typing does not read the segments of segment-free code

`segFree i`: the Core instruction `i` contains no segment instruction (`table.init`, `elem.drop`,
`memory.init`, `data.drop`, `array.new_data`, `array.new_elem`, `array.init_data`,
`array.init_elem`) at any depth. **`segs_InstrOk`**, **`segs_InstrsOk`**: typing of
segment-free code survives replacing the context's `DATAS` and `ELEMS` by anything; the proof
follows silmaril-lean's `InstrOk.mono`. **`segs_FuncOk`**: the same for a function. The image of
Lime1 code is segment-free (`segFreeL_toCore`).

This is the weakening that `Task.storeOkErase10` needs (`InstErase10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.SegFree

open Silmaril.Wasm Silmaril.Wasm.Validation

/-- `C` with its segment types replaced. -/
abbrev withSegs (C : Context) (D : List Unit) (E : List CRefType) : Context :=
  { C with datas := D, elems := E }

mutual
/-- No segment instruction, at any depth. -/
def segFree : Instr → Bool
  | .block _ b => segFreeL b
  | .loop _ b => segFreeL b
  | .if_ _ b₁ b₂ => segFreeL b₁ && segFreeL b₂
  | .tryTable _ _ b => segFreeL b
  | .tableInit _ _ | .elemDrop _ | .memoryInit _ _ | .dataDrop _ | .arrayNewData _ _
  | .arrayNewElem _ _ | .arrayInitData _ _ | .arrayInitElem _ _ => false
  | _ => true
/-- No segment instruction in a sequence. -/
def segFreeL : List Instr → Bool
  | [] => true
  | i :: is => segFree i && segFreeL is
end

theorem segFreeL_append {is₁ is₂ : List Instr} :
    segFreeL (is₁ ++ is₂) = (segFreeL is₁ && segFreeL is₂) := by
  induction is₁ with
  | nil => simp [segFreeL]
  | cons i is ih => simp [segFreeL, ih, Bool.and_assoc]

theorem segFreeL_left {is₁ is₂ : List Instr} (h : segFreeL (is₁ ++ is₂) = true) :
    segFreeL is₁ = true := by
  rw [segFreeL_append, Bool.and_eq_true] at h
  exact h.1

theorem segFreeL_right {is₁ is₂ : List Instr} (h : segFreeL (is₁ ++ is₂) = true) :
    segFreeL is₂ = true := by
  rw [segFreeL_append, Bool.and_eq_true] at h
  exact h.2

theorem segFree_of_cons {i : Instr} {is : List Instr} (h : segFreeL (i :: is) = true) :
    segFree i = true := by
  simp only [segFreeL, Bool.and_eq_true] at h
  exact h.1

theorem segFreeL_of_cons {i : Instr} {is : List Instr} (h : segFreeL (i :: is) = true) :
    segFreeL is = true := by
  simp only [segFreeL, Bool.and_eq_true] at h
  exact h.2

theorem withLocals_segs (D : List Unit) (E : List CRefType) :
    ∀ (C : Context) (xs : List Nat) (lts : List LocalType),
      (withSegs C D E).withLocals xs lts = withSegs (C.withLocals xs lts) D E
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | C, x :: xs, lt :: lts => withLocals_segs D E (C.setLocal x lt) xs lts

theorem initLocals_segs (C : Context) (D : List Unit) (E : List CRefType) (xs : List Nat) :
    (withSegs C D E).initLocals xs = withSegs (C.initLocals xs) D E :=
  withLocals_segs D E C xs _

section Families

variable {C : Context} {i : Instr} {it : InstrType} {D : List Unit} {E : List CRefType}

theorem segs_ParametricInstrOk (h : ParametricInstrOk C i it) :
    ParametricInstrOk (withSegs C D E) i it := by
  cases h <;> (constructor; all_goals assumption)

theorem segs_NumericInstrOk (h : NumericInstrOk C i it) : NumericInstrOk (withSegs C D E) i it := by
  cases h <;> (constructor; all_goals assumption)

theorem segs_VectorInstrOk (h : VectorInstrOk C i it) : VectorInstrOk (withSegs C D E) i it := by
  cases h <;> constructor <;> assumption

theorem segs_VariableInstrOk (h : VariableInstrOk C i it) :
    VariableInstrOk (withSegs C D E) i it := by
  cases h <;> constructor <;> assumption

theorem segs_MemoryInstrOk (h : MemoryInstrOk C i it) (hsf : segFree i = true) :
    MemoryInstrOk (withSegs C D E) i it := by
  cases h <;> first | (constructor <;> assumption) | simp [segFree] at hsf

theorem segs_TableInstrOk (h : TableInstrOk C i it) (hsf : segFree i = true) :
    TableInstrOk (withSegs C D E) i it := by
  cases h <;> first | (constructor <;> assumption) | simp [segFree] at hsf

theorem segs_RefInstrOk (h : RefInstrOk C i it) (hsf : segFree i = true) :
    RefInstrOk (withSegs C D E) i it := by
  cases h <;> first | (constructor <;> assumption) | simp [segFree] at hsf

theorem segs_BlockTypeOk {bt : BlockType} {t₁ t₂ : List CValType} (h : BlockTypeOk C bt t₁ t₂) :
    BlockTypeOk (withSegs C D E) bt t₁ t₂ := by
  cases h <;> constructor <;> assumption

theorem segs_CatchOk {c : Catch} (h : CatchOk C c) : CatchOk (withSegs C D E) c := by
  cases h <;> constructor <;> assumption

end Families

mutual

/-- **Typing of segment-free code does not read the segments.** -/
theorem segs_InstrOk {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    (D : List Unit) (E : List CRefType) (hsf : segFree i = true) :
    InstrOk (withSegs C D E) i it :=
  match i, h, hsf with
  | _, .parametric h, _ => .parametric (segs_ParametricInstrOk h)
  | _, .numeric h, _ => .numeric (segs_NumericInstrOk h)
  | _, .vector h, _ => .vector (segs_VectorInstrOk h)
  | _, .variable h, _ => .variable (segs_VariableInstrOk h)
  | _, .memory h, hsf => .memory (segs_MemoryInstrOk h hsf)
  | _, .table h, hsf => .table (segs_TableInstrOk h hsf)
  | _, .reference h, hsf => .reference (segs_RefInstrOk h hsf)
  | _, .block hbt hb, hsf => .block (segs_BlockTypeOk hbt) (segs_InstrsOk hb D E hsf)
  | _, .loop hbt hb, hsf => .loop (segs_BlockTypeOk hbt) (segs_InstrsOk hb D E hsf)
  | _, .if_ hbt h₁ h₂, hsf =>
      .if_ (segs_BlockTypeOk hbt) (segs_InstrsOk h₁ D E (Bool.and_eq_true _ _ ▸ hsf).1)
        (segs_InstrsOk h₂ D E (Bool.and_eq_true _ _ ▸ hsf).2)
  | _, .br hl hok, _ => .br hl hok
  | _, .brIf hl, _ => .brIf hl
  | _, .brTable hls hl' hok, _ => .brTable hls hl' hok
  | _, .brOnNull hl hh, _ => .brOnNull hl hh
  | _, .brOnNonNull hl, _ => .brOnNonNull hl
  | _, .brOnCast hl h₁ h₂ h₂₁ h₂l, _ => .brOnCast hl h₁ h₂ h₂₁ h₂l
  | _, .brOnCastFail hl h₁ h₂ h₂₁ hdl, _ => .brOnCastFail hl h₁ h₂ h₂₁ hdl
  | _, .call hf he, _ => .call hf he
  | _, .callRef hd he, _ => .callRef hd he
  | _, .callIndirect ht hs hd he, _ => .callIndirect ht hs hd he
  | _, .return_ hret hok, _ => .return_ hret hok
  | _, .returnCall hf he hret hs hok, _ => .returnCall hf he hret hs hok
  | _, .returnCallRef hd he hret hs hok, _ => .returnCallRef hd he hret hs hok
  | _, .returnCallIndirect ht hs hd he hret hrs hok, _ =>
      .returnCallIndirect ht hs hd he hret hrs hok
  | _, .throw hx he hok, _ => .throw hx he hok
  | _, .throwRef hok, _ => .throwRef hok
  | _, .tryTable hbt hb hc, hsf =>
      .tryTable (segs_BlockTypeOk hbt) (segs_InstrsOk hb D E hsf) (fun c hc' => segs_CatchOk (hc c hc'))

/-- **Typing of segment-free sequences does not read the segments.** -/
theorem segs_InstrsOk {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it)
    (D : List Unit) (E : List CRefType) (hsf : segFreeL is = true) :
    InstrsOk (withSegs C D E) is it :=
  match is, h, hsf with
  | _, .nil, _ => .nil
  | _, .instr h, hsf => .instr (segs_InstrOk h D E (segFree_of_cons hsf))
  | _, .seq (xs₁ := xs₁) h₁ hx h₂, hsf =>
      .seq (segs_InstrsOk h₁ D E (segFreeL_left hsf)) hx
        (by rw [initLocals_segs]; exact segs_InstrsOk h₂ D E (segFreeL_right hsf))
  | _, .cons (xs₁ := xs₁) hi hx hs, hsf =>
      .cons (segs_InstrOk hi D E (segFree_of_cons hsf)) hx
        (by rw [initLocals_segs]; exact segs_InstrsOk hs D E (segFreeL_of_cons hsf))
  | _, .sub h hs hok, hsf => .sub (segs_InstrsOk h D E hsf) hs hok
  | _, .frame h hok, hsf => .frame (segs_InstrsOk h D E hsf) hok

end

theorem segs_LocalOk {C : Context} {t : ValType} {lt : LocalType} {D : List Unit}
    {E : List CRefType} (h : LocalOk C t lt) : LocalOk (withSegs C D E) t lt := by
  cases h <;> constructor <;> assumption

/-- **Function typing of segment-free code does not read the segments.** -/
theorem segs_FuncOk {C : Context} {f : Func} {d : DefType} (h : FuncOk C f d) (D : List Unit)
    (E : List CRefType) (hsf : segFreeL f.body = true) : FuncOk (withSegs C D E) f d := by
  cases h with
  | mk hd he hl hb => exact .mk hd he (hl.imp fun _ _ h => segs_LocalOk h) (segs_InstrsOk hb D E hsf)

/-! ## The image of Lime1 code is segment-free -/

mutual
theorem segFree_toCore : ∀ i : Lime1.Instr, segFree i.toCore = true
  | .block _ b => segFreeL_toCore b
  | .loop _ b => segFreeL_toCore b
  | .if_ _ b₁ b₂ => by
    simp only [Lime1.Instr.toCore, segFree, segFreeL_toCore b₁, segFreeL_toCore b₂, Bool.and_self]
  | .nop | .unreachable | .drop | .select | .br _ | .brIf _ | .brTable _ _ | .call _
  | .callIndirect _ | .return_ | .localGet _ | .localSet _ | .localTee _ | .globalGet _
  | .globalSet _ | .intLoad _ _ _ | .floatLoad _ _ | .intStore _ _ _ | .floatStore _ _
  | .memorySize | .memoryGrow | .memoryFill | .memoryCopy | .intConst _ _ | .floatConst _ _
  | .intUnOp _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ | .floatUnOp _ _
  | .floatBinOp _ _ | .floatRelOp _ _ | .convert _ => rfl
theorem segFreeL_toCore : ∀ es : Lime1.Expr, segFreeL (Lime1.Expr.toCore es) = true
  | [] => rfl
  | i :: is => by
    simp only [Lime1.Expr.toCore, segFreeL, segFree_toCore i, segFreeL_toCore is, Bool.and_self]
end

end Silmaril.Wasm.SpecTec.Sim10.SegFree
