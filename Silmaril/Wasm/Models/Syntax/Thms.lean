module

public import Silmaril.Wasm.Models.Syntax.Defs
public import Silmaril.Wasm.Models.Features.Thms

/-!
# Feature-restricted syntax: monotonicity and subterms

* `*.inFeatB_mono`: a larger feature set admits more (types, instructions, modules);
* `inFeatB_block` etc.: `Instr.InFeat S` is closed under subterms (the bodies of `block`,
  `loop`, `if` and `try_table`);
* `Instr.InFeat` and `Module.InFeat` are decidable (`Defs`, by construction).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm FeatureSet

variable {S T : FeatureSet}

theorem absHeap_mono (h : S ≤ T) (t : AbsHeapType) (hs : AbsHeapType.inFeatB S t = true) :
    AbsHeapType.inFeatB T t = true := by
  have := le_iff.mp h
  cases t <;> simp_all [AbsHeapType.inFeatB]

theorem heap_mono (h : S ≤ T) (t : HeapType) (hs : HeapType.inFeatB S t = true) :
    HeapType.inFeatB T t = true := by
  have := le_iff.mp h
  cases t <;> simp_all [HeapType.inFeatB, absHeap_mono h]

theorem refType_mono (h : S ≤ T) (t : RefType) (hs : RefType.inFeatB S t = true) :
    RefType.inFeatB T t = true := by
  have := le_iff.mp h
  simp only [RefType.inFeatB, Bool.and_eq_true, Bool.or_eq_true] at hs ⊢
  exact ⟨⟨this _ hs.1.1, heap_mono h _ hs.1.2⟩, hs.2.imp id (this _)⟩

theorem valType_mono (h : S ≤ T) (t : ValType) (hs : ValType.inFeatB S t = true) :
    ValType.inFeatB T t = true := by
  have := le_iff.mp h
  rcases t with ⟨_ | _⟩ | _ | _ <;> simp_all [ValType.inFeatB, refType_mono h]

theorem blockType_mono (h : S ≤ T) (t : BlockType) (hs : BlockType.inFeatB S t = true) :
    BlockType.inFeatB T t = true := by
  have := le_iff.mp h
  cases t <;> simp_all [BlockType.inFeatB, valType_mono h]

theorem memIdx_mono (h : S ≤ T) (x : MemIdx) (hs : memIdxB S x = true) :
    memIdxB T x = true := by
  have := le_iff.mp h
  simp only [memIdxB, Bool.and_eq_true, Bool.or_eq_true] at hs ⊢
  exact ⟨⟨this _ hs.1.1, this _ hs.1.2⟩, hs.2.imp id (this _)⟩

theorem tblIdx_mono (h : S ≤ T) (x : TableIdx) (hs : tblIdxB S x = true) :
    tblIdxB T x = true := by
  have := le_iff.mp h
  simp only [tblIdxB, Bool.and_eq_true, Bool.or_eq_true] at hs ⊢
  exact ⟨this _ hs.1, hs.2.imp id (this _)⟩

theorem convert_mono (h : S ≤ T) (op : ConvertOp) (hs : ConvertOp.inFeatB S op = true) :
    ConvertOp.inFeatB T op = true := by
  have := le_iff.mp h
  cases op <;> simp_all [ConvertOp.inFeatB]

theorem intUnOp_mono (h : S ≤ T) (op : IntUnOp) (hs : IntUnOp.inFeatB S op = true) :
    IntUnOp.inFeatB T op = true := by
  have := le_iff.mp h
  cases op <;> simp_all [IntUnOp.inFeatB]

theorem vecB_mono (h : S ≤ T) (i : Instr) (hs : vecB S i = true) : vecB T i = true := by
  have := le_iff.mp h
  simp only [vecB, Bool.and_eq_true, Bool.or_eq_true] at hs ⊢
  exact ⟨this _ hs.1, hs.2.imp id (this _)⟩

theorem headB_mono (h : S ≤ T) (i : Instr) (hs : Instr.headB S i = true) :
    Instr.headB T i = true := by
  have := le_iff.mp h
  cases i
  case select ts =>
    cases ts <;> simp_all [Instr.headB, valType_mono h]
  all_goals simp_all [Instr.headB, blockType_mono h, memIdx_mono h, tblIdx_mono h,
    convert_mono h, refType_mono h, heap_mono h, intUnOp_mono h, vecB_mono h]

/-- **Monotonicity**: an instruction of `S` is an instruction of every larger feature set. -/
theorem inFeatB_mono (h : S ≤ T) (i : Instr) (hs : Instr.inFeatB S i = true) :
    Instr.inFeatB T i = true := by
  revert hs
  induction i using Instr.rec
    (motive_2 := fun l => Instr.insInFeatB S l = true → Instr.insInFeatB T l = true)
  all_goals simp_all [Instr.inFeatB, Instr.insInFeatB, headB_mono h]

theorem insInFeatB_iff {is : List Instr} :
    Instr.insInFeatB S is = true ↔ ∀ i ∈ is, Instr.inFeatB S i = true := by
  induction is with
  | nil => simp [Instr.insInFeatB]
  | cons i is ih => simp [Instr.insInFeatB, ih]

theorem insInFeatB_mono (h : S ≤ T) (is : List Instr) (hs : Instr.insInFeatB S is = true) :
    Instr.insInFeatB T is = true :=
  insInFeatB_iff.mpr fun i hi => inFeatB_mono h i (insInFeatB_iff.mp hs i hi)

theorem inFeat_mono (h : S ≤ T) {i : Instr} (hs : Instr.InFeat S i) : Instr.InFeat T i :=
  inFeatB_mono h i hs

/-! ## Subterms -/

/-- `Instr.inFeatB` is the head check and the check of every body. -/
theorem inFeatB_eq (i : Instr) :
    Instr.inFeatB S i = (Instr.headB S i && i.bodies.all (Instr.insInFeatB S)) := by
  cases i <;> simp [Instr.inFeatB, Instr.bodies, Instr.headB, Bool.and_assoc]

/-- **Closed under subterms**: the bodies of an instruction of `S` are of `S`. -/
theorem body_inFeat {i : Instr} (hi : Instr.InFeat S i) {b : Expr} (hb : b ∈ i.bodies) :
    ∀ j ∈ b, Instr.InFeat S j := by
  have h : (Instr.headB S i && i.bodies.all (Instr.insInFeatB S)) = true := (inFeatB_eq i) ▸ hi
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact insInFeatB_iff.mp (h.2 b hb)

/-! ## Modules -/

theorem bor_mono' {a b a' b' : Bool} (h₁ : a = true → a' = true) (h₂ : b = true → b' = true)
    (h : (a || b) = true) : (a' || b') = true := by
  cases a <;> cases b <;> simp_all

theorem band_mono' {a b a' b' : Bool} (h₁ : a = true → a' = true) (h₂ : b = true → b' = true)
    (h : (a && b) = true) : (a' && b') = true := by
  cases a <;> cases b <;> simp_all

/-- A Boolean disjunction `p || S.has c` is monotone in `S`. -/
theorem or_has_mono (h : S ≤ T) {p : Bool} {c : Cap} (hs : (p || S.has c) = true) :
    (p || T.has c) = true := by
  simp only [Bool.or_eq_true] at hs ⊢
  exact hs.imp id (has_of_le h)

theorem all_mono {α : Type} {f g : α → Bool} (hfg : ∀ a, f a = true → g a = true) {l : List α}
    (hs : l.all f = true) : l.all g = true := by
  simp only [List.all_eq_true] at hs ⊢
  exact fun a ha => hfg a (hs a ha)

theorem funcType_mono (h : S ≤ T) (t : FuncType) (hs : FuncType.inFeatB S t = true) :
    FuncType.inFeatB T t = true := by
  simp only [FuncType.inFeatB, Bool.and_eq_true] at hs ⊢
  exact ⟨⟨all_mono (valType_mono h) hs.1.1, all_mono (valType_mono h) hs.1.2⟩,
    or_has_mono h hs.2⟩

theorem fieldType_mono (h : S ≤ T) (t : FieldType) (hs : FieldType.inFeatB S t = true) :
    FieldType.inFeatB T t = true := by
  simp only [FieldType.inFeatB, Bool.and_eq_true] at hs ⊢
  refine ⟨?_, or_has_mono h hs.2⟩
  cases hst : t.storage <;> simp_all [StorageType.inFeatB, valType_mono h]

theorem subType_mono (h : S ≤ T) (t : SubType) (hs : SubType.inFeatB S t = true) :
    SubType.inFeatB T t = true := by
  simp only [SubType.inFeatB, Bool.and_eq_true] at hs ⊢
  refine ⟨or_has_mono h hs.1, ?_⟩
  have hc := has_of_le h (c := .gcImm)
  cases hb : t.body <;> simp_all [funcType_mono h, fieldType_mono h, all_mono (fieldType_mono h)]

theorem recType_mono (h : S ≤ T) (t : RecType) (hs : RecType.inFeatB S t = true) :
    RecType.inFeatB T t = true := by
  simp only [RecType.inFeatB, Bool.and_eq_true] at hs ⊢
  exact ⟨or_has_mono h hs.1, all_mono (subType_mono h) hs.2⟩

theorem constExpr_mono (h : S ≤ T) (e : Expr) (hs : constExprB S e = true) :
    constExprB T e = true := by
  simp only [constExprB, Bool.and_eq_true] at hs ⊢
  exact ⟨insInFeatB_mono h e hs.1, or_has_mono h hs.2⟩

theorem globalType_mono (h : S ≤ T) (t : GlobalType) (hs : GlobalType.inFeatB S t = true) :
    GlobalType.inFeatB T t = true := by
  simp only [GlobalType.inFeatB, Bool.and_eq_true] at hs ⊢
  exact ⟨⟨has_of_le h hs.1.1, valType_mono h _ hs.1.2⟩, or_has_mono h hs.2⟩

theorem memoryType_mono (h : S ≤ T) (t : MemoryType) (hs : MemoryType.inFeatB S t = true) :
    MemoryType.inFeatB T t = true := by
  simp only [MemoryType.inFeatB, Bool.and_eq_true] at hs ⊢
  exact ⟨has_of_le h hs.1, or_has_mono h hs.2⟩

theorem tableType_mono (h : S ≤ T) (t : TableType) (hs : TableType.inFeatB S t = true) :
    TableType.inFeatB T t = true := by
  simp only [TableType.inFeatB, Bool.and_eq_true, Bool.or_eq_true] at hs ⊢
  exact ⟨⟨has_of_le h hs.1.1, hs.1.2.imp id (has_of_le h)⟩, hs.2.imp id (refType_mono h _)⟩

theorem externType_mono (h : S ≤ T) (t : ExternType) (hs : ExternType.inFeatB S t = true) :
    ExternType.inFeatB T t = true := by
  cases t <;> simp_all [ExternType.inFeatB, has_of_le h, globalType_mono h, memoryType_mono h,
    tableType_mono h]

theorem global_mono (h : S ≤ T) (g : Global) (hs : Global.inFeatB S g = true) :
    Global.inFeatB T g = true :=
  band_mono' (globalType_mono h _) (constExpr_mono h _) hs

theorem table_mono (h : S ≤ T) (t : Table) (hs : Table.inFeatB S t = true) :
    Table.inFeatB T t = true :=
  band_mono' (tableType_mono h _) (constExpr_mono h _) hs

theorem func_mono (h : S ≤ T) (f : Func) (hs : Func.inFeatB S f = true) :
    Func.inFeatB T f = true :=
  band_mono' (all_mono (valType_mono h)) (insInFeatB_mono h _) hs

theorem elemMode_mono (h : S ≤ T) (md : ElemMode) (hs : ElemMode.inFeatB S md = true) :
    ElemMode.inFeatB T md = true := by
  cases md <;> simp_all [ElemMode.inFeatB, constExpr_mono h, has_of_le h]

theorem elem_mono (h : S ≤ T) (e : Elem) (hs : Elem.inFeatB S e = true) :
    Elem.inFeatB T e = true :=
  band_mono' (band_mono' (bor_mono' id (refType_mono h _)) (all_mono (constExpr_mono h)))
    (elemMode_mono h _) hs

theorem dataMode_mono (h : S ≤ T) (md : DataMode) (hs : DataMode.inFeatB S md = true) :
    DataMode.inFeatB T md = true := by
  cases md <;> simp_all [DataMode.inFeatB, constExpr_mono h, has_of_le h, memIdx_mono h]

theorem data_mono (h : S ≤ T) (d : Data) (hs : Data.inFeatB S d = true) :
    Data.inFeatB T d = true :=
  dataMode_mono h d.mode hs

/-- **Monotonicity of modules**: a module of `S` is a module of every larger feature set. -/
theorem module_mono (h : S ≤ T) (m : Module) (hs : Module.InFeat S m) : Module.InFeat T m :=
  band_mono' (band_mono' (band_mono' (band_mono' (band_mono' (band_mono' (band_mono'
    (band_mono' (band_mono' (band_mono' (all_mono (recType_mono h))
    (all_mono fun _ => externType_mono h _)) (bor_mono' id (has_of_le h)))
    (all_mono (global_mono h))) (all_mono (memoryType_mono h))) (all_mono (table_mono h)))
    (all_mono (func_mono h))) (all_mono (elem_mono h))) (all_mono (data_mono h)))
    (bor_mono' id (has_of_le h))) (bor_mono' id (has_of_le h)) hs

theorem validIn_mono (h : S ≤ T) {m : Module} (hs : ValidIn S m) : ValidIn T m :=
  ⟨hs.1, module_mono h m hs.2⟩

end Silmaril.Wasm.Models
