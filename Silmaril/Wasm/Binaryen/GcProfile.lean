module

public import Silmaril.Wasm.Binaryen.Profile
public import Silmaril.Wasm.Binaryen.ConstExprProfile

@[expose] public section

/-! # The GC slice of the profile (`BModule.inGcProfile`)

The pipeline profile of `Profile.lean` (`BModule.inProfile`: memory, data segments,
funcref tables and element segments, `call_indirect`, `ref.func`, imports) widened by
reference value types (abstract and concrete heap types, nullable or not) in locals,
globals, global imports, block types, function types and typed `select`, and by the
reference and GC instructions that need no element or data segment: `ref.null` (any heap
type), `ref.is_null`, `ref.eq`, `ref.as_non_null`, `ref.test`, `ref.cast`,
`struct.new(_default)`, `struct.get(_s/_u)`, `struct.set`, `array.new(_default/_fixed)`,
`array.get(_s/_u)`, `array.set`, `array.len`, `ref.i31`, `i31.get_s/u`,
`any.convert_extern` and `extern.convert_any`; typed reference calls and direct/reference
tail calls (`call_ref`, `return_call`, `return_call_indirect`, `return_call_ref`), `br_on_null` and
`br_on_non_null`; and exception handling: tags with
GC-slice payloads (`gcTagType`), `throw`, `throw_ref` and `try_table` with any catch
clauses (validation checks their tags and labels). Struct and array type definitions with
these field types are allowed in the type section (`typesInGcProfile`,
`Exe/Pipeline.lean`).

Also in the slice: the cast branches `br_on_cast` and `br_on_cast_fail`, and the array
instructions on segments and ranges, `array.new_data`, `array.new_elem`, `array.fill`,
`array.copy`, `array.init_data` and `array.init_elem` (validation checks their segment
indices and element types).

This is the executable profile check of the pipeline (`profileOk`). Inlining is proved
for function types with numeric, `funcref` and `externref` parameters and results
(`typesInProfile`) and is the identity elsewhere; RUME is the identity outside the base
profile (`Pass/RUME.lean`); the other proved stages need only validity.
-/

namespace Silmaril.Wasm.Binaryen

/-- Value types of the GC slice: numbers, `v128` (as in the pipeline profile) and
references. -/
def gcValType : ValType → Bool
  | .num _ | .vec _ | .ref _ => true

/-- Block types of the GC slice. -/
def gcBlockType : BlockType → Bool
  | .empty | .typeIdx _ => true
  | .value t => gcValType t

/-- The reference and GC instructions added by the slice, and every SIMD and relaxed-SIMD
instruction (the `0xFD` opcode space), which the proved stages treat like any other
valid instruction and folding leaves unfolded (`arityIn` has no entry for most). -/
def gcExtraInstr : Instr → Bool
  | .select (some ts) => ts.all gcValType
  | .refNull _ | .refIsNull | .refEq | .refAsNonNull | .refTest _ | .refCast _
  | .structNew _ | .structNewDefault _ | .structGet .. | .structSet ..
  | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed .. | .arrayGet .. | .arraySet _ | .arrayLen
  | .anyConvertExtern | .externConvertAny | .refI31 | .i31Get _ | .throwRef => true
  | .vecLoad .. | .vecLoadLane .. | .vecStore .. | .vecStoreLane .. | .vecConst _
  | .vecUnOp _ | .vecBinOp _ | .vecTernOp _ | .vecTestOp _ | .vecIntUnOp .. | .vecFloatUnOp ..
  | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp .. | .vecFloatTernOp .. | .vecAllTrue _
  | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle _
  | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp .. | .vecExtTernOp .. | .vecNarrow ..
  | .vecConvert .. | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane .. => true
  -- cast branches, and the array instructions on segments and ranges
  | .brOnCast .. | .brOnCastFail .. | .arrayNewData .. | .arrayNewElem .. | .arrayFill _
  | .arrayCopy .. | .arrayInitData .. | .arrayInitElem .. => true
  -- typed reference calls, tail calls and nullable-reference branches
  | .callRef _ | .returnCall _ | .returnCallIndirect .. | .returnCallRef _
  | .brOnNull _ | .brOnNonNull _ => true
  | _ => false

/-- Flat instructions of the GC slice. -/
def gcInstr (i : Instr) : Bool := profileInstrT i || gcExtraInstr i

mutual
/-- A tree in the GC slice. -/
def BExpr.inGcProfile : BExpr → Bool
  | .op i args => gcInstr i && BExpr.inGcProfileList args
  | .block bt b => gcBlockType bt && BExpr.inGcProfileList b
  | .loop bt b => gcBlockType bt && BExpr.inGcProfileList b
  | .if_ bt c t e => gcBlockType bt && BExpr.inGcProfileList c && BExpr.inGcProfileList t &&
      BExpr.inGcProfileList e
  | .tryTable bt _ b => gcBlockType bt && BExpr.inGcProfileList b
/-- `inGcProfile` on a list. -/
def BExpr.inGcProfileList : List BExpr → Bool
  | [] => true
  | e :: es => BExpr.inGcProfile e && BExpr.inGcProfileList es
end

/-- A tag of the GC slice indexes a function type with GC-slice parameters and no
results. -/
def gcTagType (m : Module) (t : TagType) : Bool :=
  match m.typeDefinitions[t.toNat]? with
  | some ⟨_, _, .func ft⟩ => ft.results.isEmpty && ft.params.all gcValType
  | _ => false

/-- A defined table of the GC slice: any reference type with a GC-slice
initializer. Core validation checks constant-expression typing, including the
nullability and referenced functions/globals of explicit initializers. -/
def gcTable (t : Table) : Bool :=
  BExpr.inGcProfileList (liftInstrs t.init)

/-- Element entries may also read immutable globals. Active offsets use integer
constant expressions; Core validation checks their types and global indices. -/
def gcElem (e : Elem) : Bool :=
  e.init.all (fun x => match x with
    | [.refFunc _] | [.refNull _] | [.globalGet _] => true
    | _ => false) &&
    match e.mode with
    | .active _ off => gcOffset off
    | .passive | .declarative => true

/-- The executable GC-slice check of a module: `BModule.inProfile` (tables, element
segments, data segments, memory, table, global and tag imports, tags) with the GC value
types in locals, globals and global imports, tables and element segments of any
reference type (`gcTable`, `gcElem`), and the GC instructions in code. -/
def BModule.inGcProfile (m : BModule) : Bool :=
  m.base.tags.all (gcTagType m.base) && m.base.data.all gcData &&
  decide (m.base.data.length ≤ 2 ^ 32) &&
  m.base.tables.all gcTable && m.base.elems.all gcElem &&
  m.base.imports.all (fun i => match i.type with
    | .func _ | .memory _ => true
    | .global gt => gcValType gt.value
    | .table _ => true
    | .tag t => gcTagType m.base t) &&
  m.base.globals.all (fun g => gcValType g.type.value &&
    BExpr.inGcProfileList (liftInstrs g.init)) &&
  m.funcs.all (fun f => f.locals.all gcValType && BExpr.inGcProfileList f.body) &&
  m.base.exports.all (fun e => match e.index with
    | .func _ | .global _ | .memory _ | .table _ | .tag _ => true)

/-! ## The pipeline profile is included -/

theorem gcValType_of_profile {t : ValType} (h : profileValType t = true) : gcValType t = true := by
  cases t <;> simp_all [profileValType, gcValType]

theorem gcValType_of_sig {t : ValType} (h : sigValType t = true) : gcValType t = true := by
  cases t <;> simp_all [sigValType, gcValType]

theorem gcBlockType_of_profile {bt : BlockType} (h : profileBlockType bt = true) :
    gcBlockType bt = true := by
  cases bt <;> simp_all [profileBlockType, gcBlockType, gcValType_of_profile]

theorem gcBlockType_of_profileT {bt : BlockType} (h : profileBlockTypeT bt = true) :
    gcBlockType bt = true := by
  unfold profileBlockTypeT at h
  split at h
  · simp [gcBlockType, gcValType]
  · exact gcBlockType_of_profile h

theorem gcInstr_of_profileT {i : Instr} (h : profileInstrT i = true) : gcInstr i = true := by
  simp [gcInstr, h]

mutual
theorem BExpr.inGcProfile_of_inProfileT : ∀ e : BExpr, e.inProfileT = true → e.inGcProfile = true
  | .op i args, h => by
    simp only [BExpr.inProfileT, BExpr.inGcProfile, Bool.and_eq_true] at h ⊢
    exact ⟨gcInstr_of_profileT h.1, BExpr.inGcProfileList_of_inProfileListT args h.2⟩
  | .block bt b, h => by
    simp only [BExpr.inProfileT, BExpr.inGcProfile, Bool.and_eq_true] at h ⊢
    exact ⟨gcBlockType_of_profileT h.1, BExpr.inGcProfileList_of_inProfileListT b h.2⟩
  | .loop bt b, h => by
    simp only [BExpr.inProfileT, BExpr.inGcProfile, Bool.and_eq_true] at h ⊢
    exact ⟨gcBlockType_of_profileT h.1, BExpr.inGcProfileList_of_inProfileListT b h.2⟩
  | .if_ bt c t e, h => by
    simp only [BExpr.inProfileT, BExpr.inGcProfile, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨gcBlockType_of_profileT h.1.1.1, BExpr.inGcProfileList_of_inProfileListT c h.1.1.2⟩,
      BExpr.inGcProfileList_of_inProfileListT t h.1.2⟩,
      BExpr.inGcProfileList_of_inProfileListT e h.2⟩
  | .tryTable .., h => by simp [BExpr.inProfileT] at h
theorem BExpr.inGcProfileList_of_inProfileListT :
    ∀ es : List BExpr, BExpr.inProfileListT es = true → BExpr.inGcProfileList es = true
  | [], _ => rfl
  | e :: es, h => by
    simp only [BExpr.inProfileListT, BExpr.inGcProfileList, Bool.and_eq_true] at h ⊢
    exact ⟨BExpr.inGcProfile_of_inProfileT e h.1, BExpr.inGcProfileList_of_inProfileListT es h.2⟩
end

theorem gcTagType_of_profile {m : Module} {t : TagType} (h : profileTagType m t = true) :
    gcTagType m t = true := by
  cases hd : m.typeDefinitions[t.toNat]? with
  | none => simp [profileTagType, hd] at h
  | some st =>
    obtain ⟨fin, sup, body⟩ := st
    cases body with
    | func ft =>
      simp only [profileTagType, gcTagType, hd, Bool.and_eq_true, List.all_eq_true] at h ⊢
      exact ⟨h.1, fun x hx => gcValType_of_sig (h.2 x hx)⟩
    | _ => simp [profileTagType, hd] at h

theorem gcTable_of_profile {t : Table} (h : profileTable t = true) : gcTable t = true := by
  rcases t with ⟨tt, init⟩
  simp only [profileTable, profileTableType, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨he, hi⟩ := h
  split at hi
  · simp [gcTable, liftInstrs, liftInstr, BExpr.inGcProfileList, BExpr.inGcProfile,
      gcInstr, gcExtraInstr]
  · cases hi

theorem gcElem_of_profile {e : Elem} (h : profileElem e = true) : gcElem e = true := by
  simp only [profileElem, gcElem, Bool.and_eq_true, List.all_eq_true] at h ⊢
  constructor
  · intro x hx
    have := h.1.2 x hx
    split at this <;> simp_all
  · have hm := h.2
    split at hm <;> simp_all [gcOffset]

/-- A module of the pipeline profile is in the GC slice. -/
theorem BModule.inGcProfile_of_inProfile {m : BModule} (h : m.inProfile = true) :
    m.inGcProfile = true := by
  simp only [BModule.inProfile, BModule.inGcProfile, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨htag, hdata⟩, hdlen⟩, htab⟩, helem⟩, himp⟩, hglob⟩, hfun⟩, hexp⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨fun t ht => gcTagType_of_profile (htag t ht),
    fun d hd => gcData_of_profile (hdata d hd)⟩, hdlen⟩,
    fun t ht => gcTable_of_profile (htab t ht)⟩, fun e he => gcElem_of_profile (helem e he)⟩,
    fun i hi => ?_⟩, fun g hg => ?_⟩, fun f hf => ?_⟩, hexp⟩
  · have := himp i hi
    revert this
    split <;> simp_all [gcValType_of_sig, gcTagType_of_profile]
  · exact ⟨gcValType_of_sig (hglob g hg).1,
      BExpr.inGcProfileList_of_inProfileListT _ (hglob g hg).2⟩
  · exact ⟨fun t ht => gcValType_of_sig ((hfun f hf).1 t ht),
      BExpr.inGcProfileList_of_inProfileListT _ (hfun f hf).2⟩

end Silmaril.Wasm.Binaryen
