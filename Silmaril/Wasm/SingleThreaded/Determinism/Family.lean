module

public import Silmaril.Wasm.SingleThreaded.Determinism.Vals

@[expose] public section

/-! # Determinism toolkit: the reduction families

Every family rule has a left-hand side `vals args ++ [e]` with `e` a non-value
instruction of that family (`famOf e`). This separates the families from each
other and from the control rules of `Step`.
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- Which reduction family handles an instruction. -/
inductive Fam where
  | parametric | numeric | vector | variable | table | memory | reference | aggregate | control
  deriving DecidableEq

/-- The family of the instruction `e`. -/
def famOf : Admin → Fam
  | .plain i =>
    match i with
    | .nop | .unreachable | .drop | .select _ => .parametric
    | .intUnOp .. | .intBinOp .. | .intTestOp .. | .intRelOp .. | .floatUnOp ..
    | .floatBinOp .. | .floatRelOp .. | .convert _ => .numeric
    | .vecUnOp _ | .vecBinOp _ | .vecTernOp _ | .vecTestOp _ | .vecIntUnOp .. | .vecFloatUnOp ..
    | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp .. | .vecFloatTernOp .. | .vecAllTrue _
    | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle _
    | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp .. | .vecExtTernOp .. | .vecNarrow ..
    | .vecConvert .. | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane .. => .vector
    | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _ => .variable
    | .tableGet _ | .tableSet _ | .tableSize _ | .tableGrow _ | .tableFill _ | .tableCopy ..
    | .tableInit .. | .elemDrop _ => .table
    | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. | .vecLoad .. | .vecLoadLane ..
    | .vecStore .. | .vecStoreLane .. | .memorySize _ | .memoryGrow _ | .memoryFill _
    | .memoryCopy .. | .memoryInit .. | .dataDrop _ => .memory
    | .refNull _ | .refIsNull | .refAsNonNull | .refEq | .refTest _ | .refCast _ | .refFunc _
    | .refI31 | .i31Get _ | .externConvertAny | .anyConvertExtern => .reference
    | .structNew _ | .structNewDefault _ | .structGet .. | .structSet .. | .arrayNew _
    | .arrayNewDefault _ | .arrayNewFixed .. | .arrayNewData .. | .arrayNewElem .. | .arrayGet ..
    | .arraySet _ | .arrayLen | .arrayFill _ | .arrayCopy .. | .arrayInitData ..
    | .arrayInitElem .. => .aggregate
    | _ => .control
  | _ => .control

theorem eq_vals_of_all {m : List Admin} (h : ∀ x ∈ m, x.val? ≠ none) :
    m = vals (m.filterMap Admin.val?) := by
  induction m with
  | nil => rfl
  | cons a m ih =>
    have ha := h a (by simp)
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ha
    rw [List.filterMap_cons, hv]
    simp only [vals_cons]
    rw [← val?_eq_some.mp hv]
    exact congrArg _ (ih fun x hx => h x (by simp [hx]))

/-- The shape of a family left-hand side. -/
def FamShape (k : Fam) (code : List Admin) : Prop :=
  ∃ args e, code = vals args ++ [e] ∧ e.val? = none ∧ famOf e = k

theorem famShape_of (k : Fam) (l : List Admin) (hne : l ≠ [])
    (hv : ∀ x ∈ l.dropLast, x.val? ≠ none) (he : (l.getLast hne).val? = none)
    (hk : famOf (l.getLast hne) = k) : FamShape k l := by
  refine ⟨l.dropLast.filterMap Admin.val?, l.getLast hne, ?_, he, hk⟩
  rw [← eq_vals_of_all hv]
  exact (List.dropLast_append_getLast hne).symm

theorem famShape_vals (k : Fam) (vs : List Val) (e : Admin) (he : e.val? = none)
    (hk : famOf e = k) : FamShape k (vals vs ++ [e]) := ⟨vs, e, rfl, he, hk⟩

@[simp] theorem val?_intConst (t : IntType) (b : BitVec t.width) :
    (Admin.plain (.intConst t b)).val? = some (.num ⟨.int t, b⟩) := rfl
@[simp] theorem val?_floatConst (t : FloatType) (b : BitVec t.width) :
    (Admin.plain (.floatConst t b)).val? = some (.num ⟨.float t, b⟩) := rfl
@[simp] theorem val?_vecConst (b : BitVec 128) :
    (Admin.plain (.vecConst b)).val? = some (.vec b) := rfl
@[simp] theorem val?_ref (r : Ref) : (Admin.ref r).val? = some (.ref r) := rfl
@[simp] theorem val?_constI32 (b : BitVec 32) : (constI32 b).val? = some (.i32 b) := rfl

/-- Discharge `famShape_of` on a literal left-hand side. -/
macro "fam_shape" : tactic =>
  `(tactic| first
    | exact famShape_vals _ _ _ rfl rfl
    | exact famShape_of _ _ (by simp) (by simp) rfl rfl)

variable {H : Type}

theorem ParametricStep.shape {l l' : List Admin} (h : ParametricStep l l') :
    FamShape .parametric l := by
  cases h <;> fam_shape

theorem NumericStep.shape {P : Profile} {l l' : List Admin} (h : NumericStep P l l') :
    FamShape .numeric l := by
  cases h <;> fam_shape

theorem VectorStep.shape {P : Profile} {l l' : List Admin} (h : VectorStep P l l') :
    FamShape .vector l := by
  cases h <;> fam_shape

theorem VariableStep.shape {s : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : VariableStep ⟨s, f, l⟩ c') : FamShape .variable l := by
  cases h <;> fam_shape

theorem TableStep.shape {P : Profile} {s : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : TableStep P ⟨s, f, l⟩ c') : FamShape .table l := by
  cases h <;> fam_shape

theorem MemoryStep.shape {P : Profile} {s : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : MemoryStep P ⟨s, f, l⟩ c') : FamShape .memory l := by
  cases h <;> fam_shape

theorem RefStep.shape {s : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : RefStep ⟨s, f, l⟩ c') : FamShape .reference l := by
  cases h <;> fam_shape

theorem AggregateStep.shape {s : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : AggregateStep ⟨s, f, l⟩ c') : FamShape .aggregate l := by
  cases h <;> fam_shape

end Silmaril.Wasm.SingleThreaded.Det
