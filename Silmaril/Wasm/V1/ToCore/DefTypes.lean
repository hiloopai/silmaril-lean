module

public import Silmaril.Wasm.V1.ToCore.Types
public import Silmaril.Wasm.Validation.Subtyping.Properties

@[expose] public section

/-! # V1 function types as Core 3.0 defined types

A V1 function type becomes the singleton, final, parent-free recursive group
`V1.FuncType.toCoreRec`; its defined type is projection `0` of that group. It has
no type indices, so rolling at any index and closing leave it unchanged, and it
expands to the V1 signature. On this image `Deftype_sub` is equality, which is
what the V1/Lime1 `call_indirect` simulation needs.
-/

namespace Silmaril.Wasm.V1

open Silmaril.Wasm.Validation

/-- The Core semantic value type of a V1 (numeric) value type. -/
abbrev ValType.toC (t : ValType) : CValType := .num t

@[simp] theorem liftVal_toCore (t : ValType) : liftVal (ValType.toCore t) = t.toC := rfl

/-- The Core defined type of a V1 function type. -/
def FuncType.toDefType (t : FuncType) : DefType := .defn (liftRec t.toCoreRec) 0

theorem subst_ofList_num (σ : Subst) (ts : List NumType) :
    (Ty.ofList (ts.map Ty.num)).subst σ = Ty.ofList (ts.map Ty.num) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Ty.subst, ih]

theorem liftResult_toCore (ts : List ValType) :
    liftResult (ts.map ValType.toCore) = Ty.ofList (ts.map Ty.num) := by
  simp [liftResult, Function.comp_def]

/-- The expansion of a V1 function type's defined type is its signature. -/
theorem FuncType.toDefType_expand (t : FuncType) :
    t.toDefType.expand? =
      some (.func (Ty.ofList (t.params.map Ty.num)) (Ty.ofList (t.results.map Ty.num))) := by
  simp [toDefType, DefType.expand?, unrolldt, unrollrt, liftRec, toCoreRec, liftSub, liftComp,
    FuncType.toCore, liftResult_toCore, Ty.subst, subst_ofList_num, Ty.subs, Ty.body, Ty.length]

theorem freeIdx_ofList_num (ts : List NumType) : (Ty.ofList (ts.map Ty.num)).freeIdx = [] := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Ty.freeIdx, ih]

theorem FuncType.toDefType_closed (t : FuncType) : t.toDefType.Closed := by
  simp [toDefType, Ty.Closed, Ty.freeIdx, liftRec, toCoreRec, liftSub, liftComp,
    FuncType.toCore, liftResult_toCore, freeIdx_ofList_num]

/-- Rolling the V1 group at any index gives exactly its defined type. -/
theorem FuncType.rolldt_toCoreRec (x : Nat) (t : FuncType) :
    rolldt x (liftRec t.toCoreRec) = [t.toDefType] := by
  simp [rolldt, rollrt, toDefType, liftRec, toCoreRec, liftSub, liftComp, FuncType.toCore,
    liftResult_toCore, Ty.subst, subst_ofList_num, Ty.subs, Ty.length]

/-- A V1 function type's defined type unrolls to a final, parent-free sub type. -/
theorem FuncType.toDefType_unroll (t : FuncType) :
    unrolldt t.toDefType =
      some (.sub true .nil
        (.func (Ty.ofList (t.params.map Ty.num)) (Ty.ofList (t.results.map Ty.num)))) := by
  simp [toDefType, unrolldt, unrollrt, liftRec, toCoreRec, liftSub, liftComp,
    FuncType.toCore, liftResult_toCore, Ty.subst, subst_ofList_num, Ty.subs, Ty.length]

theorem ofList_map_num_injective : Function.Injective (fun ts : List NumType =>
    Ty.ofList (ts.map Ty.num)) := by
  intro a b h
  have h' := congrArg Ty.toList h
  simp only [Ty.toList_ofList] at h'
  exact List.map_injective_iff.mpr (fun x y hxy => by cases hxy; rfl) h'

/-- The Core defined type determines the V1 function type. -/
theorem FuncType.toDefType_injective : Function.Injective FuncType.toDefType := by
  intro t₁ t₂ h
  have := congrArg DefType.expand? h
  rw [toDefType_expand, toDefType_expand] at this
  simp only [Option.some.injEq, Ty.func.injEq] at this
  obtain ⟨hp, hr⟩ := this
  cases t₁; cases t₂
  simp only [FuncType.mk.injEq]
  exact ⟨ofList_map_num_injective hp, ofList_map_num_injective hr⟩

/-- On V1 images, defined-type subtyping is equality. -/
theorem FuncType.toDefType_sub_iff (Δ : TypeCtx) (t₁ t₂ : FuncType) :
    Sub Δ t₁.toDefType t₂.toDefType ↔ t₁ = t₂ := by
  rw [Sub.def_iff_of_noSupers (by
    intro fin sups ct h
    rw [toDefType_unroll] at h
    simp only [Option.some.injEq, Ty.sub.injEq] at h
    exact h.2.1.symm)]
  simp only [Ty.clos, Ty.substAll_closed (toDefType_closed _)]
  exact toDefType_injective.eq_iff

end Silmaril.Wasm.V1
