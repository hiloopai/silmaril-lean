module

public import Silmaril.Wasm.Binaryen.Profile

@[expose] public section

/-! # The scalar profile supported by the native interpreter

i32/i64 integer numerics, locals, globals, direct `call`/`return`,
`block`/`loop`/`if`/`br`/`br_if`/`br_table`, `drop`/`select`/`nop`/`unreachable`.
Excluded: memory, tables, references, exceptions, tail calls, floats, SIMD.

This is the restricted integer, memory-free profile. It is deliberately
independent of the optimizer profile: native `run` has no float, conversion,
memory or indirect-call cases. Adequacy requires this smaller profile.
-/

namespace Silmaril.Wasm.Binaryen

/-- Value types of the profile. -/
def nativeValType : ValType → Bool
  | .num (.int _) => true
  | _ => false

/-- Block types of the profile (`typeIdx` blocks are allowed; their types are
checked by validation). -/
def nativeBlockType : BlockType → Bool
  | .empty | .typeIdx _ => true
  | .value t => nativeValType t

/-- Flat instructions of the profile. -/
def nativeInstr : Instr → Bool
  | .nop | .unreachable | .drop | .select none | .br _ | .brIf _ | .brTable _ _ | .call _
  | .return_ | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _
  | .intConst _ _ | .intUnOp _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ => true
  | _ => false

mutual
/-- A tree in the profile (structured, profile instructions and block types). -/
def BExpr.inNativeProfile : BExpr → Bool
  | .op i args => nativeInstr i && BExpr.inNativeProfileList args
  | .block bt b => nativeBlockType bt && BExpr.inNativeProfileList b
  | .loop bt b => nativeBlockType bt && BExpr.inNativeProfileList b
  | .if_ bt c t e => nativeBlockType bt && BExpr.inNativeProfileList c && BExpr.inNativeProfileList t &&
      BExpr.inNativeProfileList e
  | .tryTable .. => false
/-- `inNativeProfile` on a list. -/
def BExpr.inNativeProfileList : List BExpr → Bool
  | [] => true
  | e :: es => BExpr.inNativeProfile e && BExpr.inNativeProfileList es
end

/-- The executable profile check of a module. -/
def BModule.inNativeProfile (m : BModule) : Bool :=
  m.base.memories.isEmpty && m.base.tables.isEmpty && m.base.tags.isEmpty &&
  m.base.data.isEmpty && m.base.elems.isEmpty &&
  m.base.imports.all (fun i => match i.type with | .func _ => true | _ => false) &&
  m.base.globals.all (fun g => nativeValType g.type.value &&
    BExpr.inNativeProfileList (liftInstrs g.init)) &&
  m.funcs.all (fun f => f.locals.all nativeValType && BExpr.inNativeProfileList f.body) &&
  m.base.exports.all (fun e => match e.index with | .func _ | .global _ => true | _ => false)

/-- Core instructions of the profile, recursively. -/
def instrInNativeProfile : Instr → Prop
  | .block bt body | .loop bt body =>
      nativeBlockType bt = true ∧ ∀ i ∈ body.attach, instrInNativeProfile i.val
  | .if_ bt b₁ b₂ => nativeBlockType bt = true ∧ (∀ i ∈ b₁.attach, instrInNativeProfile i.val) ∧
      ∀ i ∈ b₂.attach, instrInNativeProfile i.val
  | i => nativeInstr i = true
termination_by i => sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- **The profile, as a property of the lowered module.** -/
structure InNativeProfile (m : BModule) : Prop where
  memories : m.lower.memories = []
  tables : m.lower.tables = []
  tags : m.lower.tags = []
  data : m.lower.data = []
  elems : m.lower.elems = []
  imports : ∀ i ∈ m.lower.imports, ∃ t, i.type = .func t
  code : ∀ f ∈ m.lower.funcs, ∀ i ∈ f.body, instrInNativeProfile i
  locals : ∀ f ∈ m.lower.funcs, ∀ t ∈ f.locals, nativeValType t = true
  globals : ∀ g ∈ m.lower.globals, nativeValType g.type.value = true ∧
    ∀ i ∈ g.init, instrInNativeProfile i

theorem instrInNativeProfile_of_flat {i : Instr} (h : nativeInstr i = true) : instrInNativeProfile i := by
  rw [instrInNativeProfile.eq_def]
  split <;> first | exact h | simp [nativeInstr] at h

mutual
/-- Every instruction of the lowering of a profile tree is in the profile. -/
theorem inNativeProfile_lower : ∀ e : BExpr, e.inNativeProfile = true → ∀ i ∈ e.lower, instrInNativeProfile i
  | .op i args, h, j, hj => by
    simp only [BExpr.inNativeProfile, Bool.and_eq_true] at h
    rw [BExpr.lower_op, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact inNativeProfileList_lower args h.2 j hj
    · exact instrInNativeProfile_of_flat h.1
  | .block bt b, h, j, hj => by
    simp only [BExpr.inNativeProfile, Bool.and_eq_true] at h
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    rw [instrInNativeProfile.eq_def]
    show nativeBlockType bt = true ∧ ∀ i ∈ (BExpr.lowerList b).attach, instrInNativeProfile i.val
    exact ⟨h.1, fun i _ => inNativeProfileList_lower b h.2 i.val i.property⟩
  | .loop bt b, h, j, hj => by
    simp only [BExpr.inNativeProfile, Bool.and_eq_true] at h
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    rw [instrInNativeProfile.eq_def]
    show nativeBlockType bt = true ∧ ∀ i ∈ (BExpr.lowerList b).attach, instrInNativeProfile i.val
    exact ⟨h.1, fun i _ => inNativeProfileList_lower b h.2 i.val i.property⟩
  | .if_ bt c t e, h, j, hj => by
    simp only [BExpr.inNativeProfile, Bool.and_eq_true, and_assoc] at h
    obtain ⟨hbt, hc, ht, he⟩ := h
    simp only [BExpr.lower, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact inNativeProfileList_lower c hc j hj
    · rw [instrInNativeProfile.eq_def]
      show nativeBlockType bt = true ∧
        (∀ i ∈ (BExpr.lowerList t).attach, instrInNativeProfile i.val) ∧
        ∀ i ∈ (BExpr.lowerList e).attach, instrInNativeProfile i.val
      exact ⟨hbt, fun i _ => inNativeProfileList_lower t ht i.val i.property,
        fun i _ => inNativeProfileList_lower e he i.val i.property⟩
  | .tryTable .., h, _, _ => by simp [BExpr.inNativeProfile] at h
/-- `inNativeProfile_lower` on a list. -/
theorem inNativeProfileList_lower : ∀ es : List BExpr, BExpr.inNativeProfileList es = true →
    ∀ i ∈ BExpr.lowerList es, instrInNativeProfile i
  | [], _, j, hj => by simp at hj
  | e :: es, h, j, hj => by
    simp only [BExpr.inNativeProfileList, Bool.and_eq_true] at h
    rw [BExpr.lowerList_cons, List.mem_append] at hj
    rcases hj with hj | hj
    · exact inNativeProfile_lower e h.1 j hj
    · exact inNativeProfileList_lower es h.2 j hj
end

/-- The executable check is sound. -/
theorem BModule.inNativeProfile_sound {m : BModule} (h : m.inNativeProfile = true) : InNativeProfile m := by
  simp only [BModule.inNativeProfile, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true,
    and_assoc] at h
  obtain ⟨hmem, htab, htag, hdata, helem, himp, hglob, hfun, -⟩ := h
  refine ⟨hmem, htab, htag, hdata, helem, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := himp i hi
    revert this
    generalize i.type = t
    cases t <;> simp
  · intro f hf i hi
    simp only [BModule.lower, List.mem_map] at hf
    obtain ⟨bf, hbf, rfl⟩ := hf
    exact inNativeProfileList_lower _ (hfun bf hbf).2 i hi
  · intro f hf t ht
    simp only [BModule.lower, List.mem_map] at hf
    obtain ⟨bf, hbf, rfl⟩ := hf
    exact (hfun bf hbf).1 t ht
  · intro g hg
    refine ⟨(hglob g hg).1, fun i hi => ?_⟩
    have := inNativeProfileList_lower _ (hglob g hg).2 i
    rw [lowerList_liftInstrs] at this
    exact this hi

end Silmaril.Wasm.Binaryen
