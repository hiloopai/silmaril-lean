module

public import Silmaril.Wasm.Binaryen.Typing

@[expose] public section

/-! # The first profile (`BProfile`)

i32/i64 and f32/f64 scalar numerics, locals, globals, direct `call`/`return`,
`block`/`loop`/`if`/`br`/`br_if`/`br_table`, `drop`/`select`/`nop`/`unreachable`,
scalar loads/stores, `memory.size`/`memory.grow`, bulk memory
(`memory.fill`/`memory.copy`/`memory.init`/`data.drop`) and scalar conversions
(including trapping and saturating float truncation and bit reinterpretation).
Defined memories, memory and global imports, and constant-offset data segments are
allowed. The base profile (`BModule.inProfileBase`) excludes tables; the pipeline
profile (`BModule.inProfile`) also admits funcref tables, element segments and
`call_indirect`, reference instructions, tag definitions/imports/exports and `throw`.
Excluded: exception handlers (the GC slice, `GcProfile.lean`, admits `try_table` and
`throw_ref`), tail calls, and SIMD outside full v128 loads/stores, vector constants,
i32x4 splat/add/sub/mul/shr/extract_lane, signed i64x2 extmul and i8x16.shuffle.
The base profile keeps vectors as stack intermediates; the pipeline profile also
admits `v128` signatures, locals, globals and block types.

The memory-free linking fragment uses `Link.GC.inProfile`
(`Silmaril/Wasm/Link/GC.lean`); operational rewrite proofs impose their
own applicability checks.
The memory extension is supported by the Core lowering and the RUME simulation;
consumers with a smaller fragment must still enforce their own profile checks.
-/

namespace Silmaril.Wasm.Binaryen

/-- Value types of the profile. -/
def profileValType : ValType → Bool
  | .num _ => true
  | _ => false

/-- Value types accepted by pipeline signatures, locals and globals: scalar numerics,
`v128`, and nullable abstract `funcref`/`externref`. The base profile remains scalar. -/
def sigValType : ValType → Bool
  | .num _ | .vec .v128 | .ref ⟨true, .abstract .func⟩ | .ref ⟨true, .abstract .extern⟩ => true
  | _ => false

theorem sigValType_of_profileValType {t : ValType} (h : profileValType t = true) :
    sigValType t = true := by
  cases t <;> simp_all [profileValType, sigValType]

/-- Block types of the profile (`typeIdx` blocks are allowed; their types are
checked by validation). -/
def profileBlockType : BlockType → Bool
  | .empty | .typeIdx _ => true
  | .value t => profileValType t

/-- Flat instructions of the profile. -/
def profileInstr : Instr → Bool
  | .nop | .unreachable | .drop | .select none | .br _ | .brIf _ | .brTable _ _ | .call _
  | .return_ | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _
  | .intLoad .. | .intStore .. | .floatLoad .. | .floatStore .. | .memorySize _ | .memoryGrow _
  | .memoryFill _ | .memoryCopy .. | .memoryInit .. | .dataDrop _
  | .intConst _ _ | .intUnOp _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _
  | .floatConst .. | .floatUnOp .. | .floatBinOp .. | .floatRelOp .. | .convert _
  | .vecLoad .full _ _ | .vecStore _ _ | .vecSplat (.int .i32x4)
  | .vecIntBinOp .i32x4 .add | .vecIntBinOp .i32x4 .sub | .vecIntBinOp .i32x4 .mul
  | .vecIntBinOp .i32x4 (.min .signed)
  | .vecExtractLane (.int .i32x4) none _
  | .vecShiftOp .i32x4 (.shr _) | .vecExtBinOp .i32x4 .i64x2 (.extmul _ .signed)
  | .vecShuffle _ => true
  | _ => false

mutual
/-- A tree in the profile (structured, profile instructions and block types). -/
def BExpr.inProfile : BExpr → Bool
  | .op i args => profileInstr i && BExpr.inProfileList args
  | .block bt b => profileBlockType bt && BExpr.inProfileList b
  | .loop bt b => profileBlockType bt && BExpr.inProfileList b
  | .if_ bt c t e => profileBlockType bt && BExpr.inProfileList c && BExpr.inProfileList t &&
      BExpr.inProfileList e
  | .tryTable .. => false
/-- `inProfile` on a list. -/
def BExpr.inProfileList : List BExpr → Bool
  | [] => true
  | e :: es => BExpr.inProfile e && BExpr.inProfileList es
end

/-- A data segment offset of the profile: one `i32.const`. -/
def profileOffset : Expr → Bool
  | [.intConst .i32 _] => true
  | _ => false

theorem profileOffset_sound {off : Expr} (h : profileOffset off = true) :
    ∃ c, off = [.intConst .i32 c] := by
  unfold profileOffset at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- Data segments of the profile: passive, or active at a constant integer offset (no
global or function references, so renaming leaves the segment unchanged), with a
length that fits the `i32.const` instantiation emits. -/
def profileData (d : Data) : Bool :=
  decide (d.bytes.size < 2 ^ 32) && match d.mode with
    | .passive => true
    | .active _ off => profileOffset off

/-- The base profile: no tables, elements or indirect calls. -/
def BModule.inProfileBase (m : BModule) : Bool :=
  m.base.tables.isEmpty && m.base.tags.isEmpty &&
  m.base.data.all profileData && decide (m.base.data.length ≤ 2 ^ 32) &&
  m.base.elems.isEmpty &&
  m.base.imports.all (fun i => match i.type with
    | .func _ | .memory _ => true | .global gt => profileValType gt.value | _ => false) &&
  m.base.globals.all (fun g => profileValType g.type.value &&
    BExpr.inProfileList (liftInstrs g.init)) &&
  m.funcs.all (fun f => f.locals.all profileValType && BExpr.inProfileList f.body) &&
  m.base.exports.all (fun e => match e.index with | .func _ | .global _ | .memory _ => true | _ => false)

/-- Core instructions of the profile, recursively. -/
def instrInProfile : Instr → Prop
  | .block bt body | .loop bt body =>
      profileBlockType bt = true ∧ ∀ i ∈ body.attach, instrInProfile i.val
  | .if_ bt b₁ b₂ => profileBlockType bt = true ∧ (∀ i ∈ b₁.attach, instrInProfile i.val) ∧
      ∀ i ∈ b₂.attach, instrInProfile i.val
  | i => profileInstr i = true
termination_by i => sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- A data segment of the profile, as a property. -/
def DataInProfile (d : Data) : Prop :=
  d.bytes.size < 2 ^ 32 ∧ ∀ x off, d.mode = .active x off → ∃ c, off = [.intConst .i32 c]

theorem profileData_sound {d : Data} (h : profileData d = true) : DataInProfile d := by
  obtain ⟨bytes, mode⟩ := d
  simp only [profileData, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun x off hm => ?_⟩
  cases hm
  exact profileOffset_sound h.2

/-- A function or memory import: the imports RUME re-indexes around. -/
def FuncOrMemImport (i : Import) : Prop :=
  (∃ t, i.type = .func t) ∨ ∃ mt, i.type = .memory mt

/-- An import of the profile: a function, a memory, or a global of profile value type. -/
def ImportInProfile (i : Import) : Prop :=
  FuncOrMemImport i ∨ ∃ gt, i.type = .global gt ∧ profileValType gt.value = true

/-- **The profile, as a property of the lowered module.** -/
structure InProfile (m : BModule) : Prop where
  tables : m.lower.tables = []
  tags : m.lower.tags = []
  data : ∀ d ∈ m.lower.data, DataInProfile d
  dataLen : m.lower.data.length ≤ 2 ^ 32
  elems : m.lower.elems = []
  imports : ∀ i ∈ m.lower.imports, ImportInProfile i
  code : ∀ f ∈ m.lower.funcs, ∀ i ∈ f.body, instrInProfile i
  locals : ∀ f ∈ m.lower.funcs, ∀ t ∈ f.locals, profileValType t = true
  globals : ∀ g ∈ m.lower.globals, profileValType g.type.value = true ∧
    ∀ i ∈ g.init, instrInProfile i

theorem instrInProfile_of_flat {i : Instr} (h : profileInstr i = true) : instrInProfile i := by
  rw [instrInProfile.eq_def]
  split <;> first | exact h | simp [profileInstr] at h

mutual
/-- Every instruction of the lowering of a profile tree is in the profile. -/
theorem inProfile_lower : ∀ e : BExpr, e.inProfile = true → ∀ i ∈ e.lower, instrInProfile i
  | .op i args, h, j, hj => by
    simp only [BExpr.inProfile, Bool.and_eq_true] at h
    rw [BExpr.lower_op, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact inProfileList_lower args h.2 j hj
    · exact instrInProfile_of_flat h.1
  | .block bt b, h, j, hj => by
    simp only [BExpr.inProfile, Bool.and_eq_true] at h
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    rw [instrInProfile.eq_def]
    show profileBlockType bt = true ∧ ∀ i ∈ (BExpr.lowerList b).attach, instrInProfile i.val
    exact ⟨h.1, fun i _ => inProfileList_lower b h.2 i.val i.property⟩
  | .loop bt b, h, j, hj => by
    simp only [BExpr.inProfile, Bool.and_eq_true] at h
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    rw [instrInProfile.eq_def]
    show profileBlockType bt = true ∧ ∀ i ∈ (BExpr.lowerList b).attach, instrInProfile i.val
    exact ⟨h.1, fun i _ => inProfileList_lower b h.2 i.val i.property⟩
  | .if_ bt c t e, h, j, hj => by
    simp only [BExpr.inProfile, Bool.and_eq_true, and_assoc] at h
    obtain ⟨hbt, hc, ht, he⟩ := h
    simp only [BExpr.lower, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact inProfileList_lower c hc j hj
    · rw [instrInProfile.eq_def]
      show profileBlockType bt = true ∧
        (∀ i ∈ (BExpr.lowerList t).attach, instrInProfile i.val) ∧
        ∀ i ∈ (BExpr.lowerList e).attach, instrInProfile i.val
      exact ⟨hbt, fun i _ => inProfileList_lower t ht i.val i.property,
        fun i _ => inProfileList_lower e he i.val i.property⟩
  | .tryTable .., h, _, _ => by simp [BExpr.inProfile] at h
/-- `inProfile_lower` on a list. -/
theorem inProfileList_lower : ∀ es : List BExpr, BExpr.inProfileList es = true →
    ∀ i ∈ BExpr.lowerList es, instrInProfile i
  | [], _, j, hj => by simp at hj
  | e :: es, h, j, hj => by
    simp only [BExpr.inProfileList, Bool.and_eq_true] at h
    rw [BExpr.lowerList_cons, List.mem_append] at hj
    rcases hj with hj | hj
    · exact inProfile_lower e h.1 j hj
    · exact inProfileList_lower es h.2 j hj
end

/-- The executable base check is sound. -/
theorem BModule.inProfileBase_sound {m : BModule} (h : m.inProfileBase = true) : InProfile m := by
  simp only [BModule.inProfileBase, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true,
    and_assoc] at h
  obtain ⟨htab, htag, hdata, hdlen, helem, himp, hglob, hfun, -⟩ := h
  refine ⟨htab, htag, fun d hd => profileData_sound (hdata d hd), of_decide_eq_true hdlen, helem,
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := himp i hi
    unfold ImportInProfile FuncOrMemImport
    revert this
    generalize i.type = t
    cases t <;> simp
  · intro f hf i hi
    simp only [BModule.lower, List.mem_map] at hf
    obtain ⟨bf, hbf, rfl⟩ := hf
    exact inProfileList_lower _ (hfun bf hbf).2 i hi
  · intro f hf t ht
    simp only [BModule.lower, List.mem_map] at hf
    obtain ⟨bf, hbf, rfl⟩ := hf
    exact (hfun bf hbf).1 t ht
  · intro g hg
    refine ⟨(hglob g hg).1, fun i hi => ?_⟩
    have := inProfileList_lower _ (hglob g hg).2 i
    rw [lowerList_liftInstrs] at this
    exact this hi

/-- Without imported globals, every import of a profile module is a function or a memory. -/
theorem InProfile.funcOrMemImports {m : BModule} (h : InProfile m)
    (hg : m.numImportedGlobals = 0) : ∀ i ∈ m.base.imports, FuncOrMemImport i := by
  intro i hi
  rcases h.imports i hi with hf | ⟨gt, hgt, -⟩
  · exact hf
  · simp only [BModule.numImportedGlobals, List.length_eq_zero_iff, List.filter_eq_nil_iff] at hg
    have := hg i hi
    simp [hgt] at this

/-! ## The pipeline profile: funcref tables, element segments, `call_indirect`

The stages proved for every valid module (DCE, RemoveUnusedNames, inlining) need no
profile; RUME is the identity outside the base profile (`rume`, `Pass/RUME.lean`). So
the pipeline admits what the certified encoder writes: the base profile plus defined
`i32` or `i64` funcref tables with the default (null) initializer, function-index segments
and nullable funcref expression segments with a constant integer offset (or passive or
declarative), the table instructions, `elem.drop`, `call_indirect`,
`ref.null`/`ref.is_null`/`ref.func` in function bodies and global initializers,
`funcref`/`externref` globals and global imports, table imports and exports, tags
and `throw`.
RUME runs only on the base profile, which has none of these. -/

/-- Flat instructions of the pipeline profile: the base ones, `call_indirect`, and the
reference instructions `ref.null func`, `ref.null extern`, `ref.is_null`,
`ref.func`, table access/bulk instructions, the stack-polymorphic `throw`, plus vector
constants, i32x4 splats and vector stores. -/
def profileInstrT (i : Instr) : Bool :=
  profileInstr i || match i with
    | .callIndirect .. | .refNull (.abstract .func) | .refNull (.abstract .extern) | .refIsNull
    | .refFunc _ | .tableGet _ | .tableSet _ | .tableInit .. | .elemDrop _
    | .tableCopy .. | .tableGrow _ | .tableSize _ | .tableFill _ | .throw _
    | .vecConst _ | .vecSplat (.int .i32x4) | .vecStore .. => true
    | _ => false

/-- Block types of the pipeline, including vector values. -/
def profileBlockTypeT (bt : BlockType) : Bool :=
  match bt with
  | .value (.vec .v128) => true
  | _ => profileBlockType bt

mutual
/-- A tree in the pipeline profile. -/
def BExpr.inProfileT : BExpr → Bool
  | .op i args => profileInstrT i && BExpr.inProfileListT args
  | .block bt b => profileBlockTypeT bt && BExpr.inProfileListT b
  | .loop bt b => profileBlockTypeT bt && BExpr.inProfileListT b
  | .if_ bt c t e => profileBlockTypeT bt && BExpr.inProfileListT c && BExpr.inProfileListT t &&
      BExpr.inProfileListT e
  | .tryTable .. => false
/-- `inProfileT` on a list. -/
def BExpr.inProfileListT : List BExpr → Bool
  | [] => true
  | e :: es => BExpr.inProfileT e && BExpr.inProfileListT es
end

/-- The table type `funcref` (nullable abstract `func`). -/
def funcRef : RefType := ⟨true, .abstract .func⟩

/-- The element type of function-index segments, `(ref func)`. -/
def funcRefNonNull : RefType := ⟨false, .abstract .func⟩

/-- A funcref table type with either address width. -/
def profileTableType (tt : TableType) : Bool := tt.element == funcRef

/-- A defined funcref table with the default initializer. -/
def profileTable (t : Table) : Bool :=
  profileTableType t.type &&
    match t.init with
    | [.refNull (.abstract .func)] => true
    | _ => false

/-- A function-index or nullable funcref expression segment, passive, declarative, or
active with an `i32.const` or `i64.const` offset. Nullable segments may also contain
`ref.null func`. -/
def profileElem (e : Elem) : Bool :=
  (e.type == funcRefNonNull || e.type == funcRef) &&
    e.init.all (fun x => match x with
      | [.refFunc _] => true
      | [.refNull (.abstract .func)] => e.type == funcRef
      | _ => false) &&
    match e.mode with
    | .active _ [.intConst _ _] => true
    | .active .. => false
    | .passive | .declarative => true

/-- Pipeline locals may hold temporary vectors; the pipeline profile's `sigValType`
locals include them. The base profile retains its original scalar locals. -/
def profileLocalType : ValType → Bool
  | .vec .v128 => true
  | t => profileValType t

/-- A tag indexes a function type with profile parameters and no results. -/
def profileTagType (m : Module) (t : TagType) : Bool :=
  match m.typeDefinitions[t.toNat]? with
  | some ⟨_, _, .func ft⟩ => ft.results.isEmpty && ft.params.all sigValType
  | _ => false

/-- **The executable profile check of a module** (the pipeline's, `profileOk`). -/
def BModule.inProfile (m : BModule) : Bool :=
  m.base.tags.all (profileTagType m.base) && m.base.data.all profileData &&
  decide (m.base.data.length ≤ 2 ^ 32) &&
  m.base.tables.all profileTable && m.base.elems.all profileElem &&
  m.base.imports.all (fun i => match i.type with
    | .func _ | .memory _ => true
    | .global gt => sigValType gt.value
    | .table tt => profileTableType tt
    | .tag t => profileTagType m.base t) &&
  m.base.globals.all (fun g => sigValType g.type.value &&
    BExpr.inProfileListT (liftInstrs g.init)) &&
  m.funcs.all (fun f => f.locals.all sigValType && BExpr.inProfileListT f.body) &&
  m.base.exports.all (fun e => match e.index with
    | .func _ | .global _ | .memory _ | .table _ | .tag _ => true)

end Silmaril.Wasm.Binaryen
