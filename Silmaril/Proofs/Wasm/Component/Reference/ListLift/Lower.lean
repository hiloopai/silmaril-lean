module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.StoreList

/-!
# Accepting runs of the lowering of `ListLift` values

The reference lowering of the fragment's values in a lowering context of the caller
(`LowerCx`), on an accepting path, is the Core-level relation of
`Silmaril.Wasm.Component.Reference.ListLift` on the renamed core stores:

* `layout_toClosed`: the canonical-ABI layout of `t.toClosed` (32-bit pointers) is
  `LTy.layout t` (so `store_list_into_range` asks the allocator for the alignment `t.align`);
* `spec_store_s32`, `spec_store_u32`, `spec_store_s64`, `spec_store_list`: the canonical ABI
  `store` of an `s32` or `u32` element (one `memWrite?` of its `le32` bytes), of an `s64` (its
  `le64` bytes) and of a nested list (`store_list_into_range`, then the `(ptr, len)` pair);
  `spec_storeTuple`: `store_record` of the fields of a tuple or record (`LFields`; a record's
  `storeFields` is the `storeTuple` of its field types, `storeFields_eq`); `spec_store` combines
  them by recursion on the value;
* `spec_lowerFlatTypes`, `spec_lowerParams`: the flat lowering of the parameters (`LParams`),
  which are `s32`s and lists (`LTy.topLevel`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {prof : ProfileKind}

/-! ## Values -/

theorem toRefList_eq_map : ∀ vs : List LVal, LVal.toRefList vs = vs.map LVal.toRef
  | [] => rfl
  | v :: vs => by
    simp only [LVal.toRefList, List.map_cons, toRefList_eq_map vs]

theorem checkList_mem {t : LTy} : ∀ {vs : List LVal}, LTy.checkList t vs = true →
    ∀ v ∈ vs, t.check v = true
  | [], _, _, h => nomatch h
  | v :: vs, h, u, hu => by
    simp only [LTy.checkList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.1
    · exact checkList_mem h.2 u hu

mutual
/-- **The layout of a type** (32-bit pointers) is `LTy.layout`. -/
theorem layout_toClosed : ∀ t : LTy, ABI.layout .i32 t.toClosed = t.layout
  | .s32 => by simp only [LTy.toClosed, LTy.layout, ABI.layout, ABI.primitiveLayout]
  | .list t => by
    simp only [LTy.toClosed, LTy.layout, ABI.layout, ABI.pointerLayout, ABI.pointerAlignment]
  | .u32 => by simp only [LTy.toClosed, LTy.layout, ABI.layout, ABI.primitiveLayout]
  | .s64 => by simp only [LTy.toClosed, LTy.layout, ABI.layout, ABI.primitiveLayout]
  | .tuple t ts => by
    simp only [LTy.toClosed, LTy.layout, ABI.layout, ABI.layoutTypes, layout_toClosed t,
      layoutTypes_toClosedList ts]
  | .record _ _ t fs => by
    simp only [LTy.toClosed, LTy.layout, ABI.layout, ABI.layoutFields, layout_toClosed t,
      layoutFields_toClosedFields fs]

theorem layoutTypes_toClosedList : ∀ ts : List LTy,
    ABI.layoutTypes .i32 (LTy.toClosedList ts) = LTy.layoutList ts
  | [] => by simp only [LTy.toClosedList, LTy.layoutList, ABI.layoutTypes]
  | t :: ts => by
    simp only [LTy.toClosedList, LTy.layoutList, ABI.layoutTypes, layout_toClosed t,
      layoutTypes_toClosedList ts]

theorem layoutFields_toClosedFields : ∀ fs : List (String × LTy),
    ABI.layoutFields .i32 (LTy.toClosedFields fs) = LTy.layoutFields fs
  | [] => by simp only [LTy.toClosedFields, LTy.layoutFields, ABI.layoutFields]
  | (_, t) :: fs => by
    simp only [LTy.toClosedFields, LTy.layoutFields, ABI.layoutFields, layout_toClosed t,
      layoutFields_toClosedFields fs]
end

/-- The layouts of labelled fields are those of their types. -/
theorem layoutFields_eq : ∀ fs : List (String × LTy),
    LTy.layoutFields fs = LTy.layoutList (fs.map (·.2))
  | [] => rfl
  | (_, t) :: fs => by
    simp only [LTy.layoutFields, LTy.layoutList, List.map_cons, layoutFields_eq fs]

/-- The resolved types of labelled fields, positionally. -/
theorem toClosedFields_eq : ∀ fs : List (String × LTy),
    (LTy.toClosedFields fs).map (·.2) = LTy.toClosedList (fs.map (·.2))
  | [] => rfl
  | (_, t) :: fs => by
    simp only [LTy.toClosedFields, LTy.toClosedList, List.map_cons, toClosedFields_eq fs]

/-- The bytes `store_int` writes for an `s32`. -/
theorem intToLE_s32 (x : BitVec 32) : intToLE 4 x.toInt = le32 x := by
  unfold intToLE le32
  rw [show 8 * 4 = 32 from rfl, BitVec.toInt_emod_two_pow, Int.toNat_natCast]

/-- The bytes `store_int` writes for a pointer-sized number. -/
theorem intToLE_nat (q : Nat) : intToLE 4 (q : Int) = le32 (BitVec.ofNat 32 q) := by
  unfold intToLE le32
  rw [BitVec.toNat_ofNat]
  congr 1

/-- The bytes `store_int` writes for a `u32`. -/
theorem intToLE_u32 (x : BitVec 32) : intToLE 4 (x.toNat : Int) = le32 x := by
  rw [intToLE_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The bytes `store_int` writes for an `s64`. -/
theorem intToLE_s64 (x : BitVec 64) : intToLE 8 x.toInt = le64 x := by
  unfold intToLE le64
  rw [show 8 * 8 = 64 from rfl, BitVec.toInt_emod_two_pow, Int.toNat_natCast]

/-! ## Element stores -/

theorem store_s32 (cx : LiftLowerContext (E3 P)) (x : BitVec 32) (a : Nat) :
    (Canon.store Limits.spec Quirks.none cx (.int .s32 x.toInt) (.prim .s32) a :
      Canon.P (E3 P) Unit Unit) = writeMem cx a (intToLE 4 x.toInt) := by
  rw [Canon.store.eq_def]
  rfl

theorem store_u32 (cx : LiftLowerContext (E3 P)) (x : BitVec 32) (a : Nat) :
    (Canon.store Limits.spec Quirks.none cx (.int .u32 (x.toNat : Int)) (.prim .u32) a :
      Canon.P (E3 P) Unit Unit) = writeMem cx a (intToLE 4 (x.toNat : Int)) := by
  rw [Canon.store.eq_def]
  rfl

theorem store_s64 (cx : LiftLowerContext (E3 P)) (x : BitVec 64) (a : Nat) :
    (Canon.store Limits.spec Quirks.none cx (.int .s64 x.toInt) (.prim .s64) a :
      Canon.P (E3 P) Unit Unit) = writeMem cx a (intToLE 8 x.toInt) := by
  rw [Canon.store.eq_def]
  rfl

theorem store_tuple (cx : LiftLowerContext (E3 P)) (vs : List Value.Val)
    (ts : List (WIT.ClosedType RtId)) (a : Nat) :
    (Canon.store Limits.spec Quirks.none cx (.record vs) (.tuple ts) a :
      Canon.P (E3 P) Unit Unit) = storeTuple Limits.spec Quirks.none cx vs ts a := by
  rw [Canon.store.eq_def]

theorem store_record (cx : LiftLowerContext (E3 P)) (vs : List Value.Val)
    (fs : List (String × WIT.ClosedType RtId)) (a : Nat) :
    (Canon.store Limits.spec Quirks.none cx (.record vs) (.record fs) a :
      Canon.P (E3 P) Unit Unit) = storeFields Limits.spec Quirks.none cx vs fs a := by
  rw [Canon.store.eq_def]

/-- `store_record` of labelled fields is `store_record` of their types. -/
theorem storeFields_eq (cx : LiftLowerContext (E3 P)) :
    ∀ (fs : List (String × WIT.ClosedType RtId)) (vs : List Value.Val) (a : Nat),
      (storeFields Limits.spec Quirks.none cx vs fs a : Canon.P (E3 P) Unit Unit) =
        storeTuple Limits.spec Quirks.none cx vs (fs.map (·.2)) a
  | [], [], _ => by rw [storeFields.eq_def, storeTuple.eq_def]; rfl
  | [], _ :: _, _ => by rw [storeFields.eq_def, storeTuple.eq_def]; rfl
  | _ :: _, [], _ => by rw [storeFields.eq_def, storeTuple.eq_def]; rfl
  | (_, t) :: fs, v :: vs, a => by
    rw [storeFields.eq_def, storeTuple.eq_def]
    simp only [List.map_cons, storeFields_eq cx fs vs]

theorem store_list (cx : LiftLowerContext (E3 P)) (vs : List Value.Val)
    (u : WIT.ClosedType RtId) (a : Nat) :
    (Canon.store Limits.spec Quirks.none cx (.list vs) (.list u) a : Canon.P (E3 P) Unit Unit) =
      (ptrType cx >>= fun p => storeListWith cx (ABI.layout p u)
        (fun e a => Canon.store Limits.spec Quirks.none cx e u a) false vs a) := by
  rw [Canon.store.eq_def]

/-- The pointer type of a lowering context is `i32`. -/
theorem ptrTypeIn_i32 {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) {m : Config (E3 P) Unit}
    (hi : LInv P I ma m) : ptrTypeIn ((E3 P).view m.core) cx = .i32 := by
  simp only [ptrTypeIn, CanonOpts.ptrType, hcx.mem]
  exact congrArg (Option.getD · _) hi.mem

/-- A store that changes only the core store keeps the caller records and tasks. -/
theorem Grows.core (m : Config (E3 P) Unit) (c' : (E3 P).Store (CanonHost (E3 P))) :
    Grows m { m with core := c' } :=
  ⟨List.prefix_refl _, List.prefix_refl _⟩

/-- **The `s32` element store.** -/
theorem spec_store_s32 {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) (x : BitVec 32) :
    ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e LTy.s32.toClosed a)
      (LStore P ra ma .s32) (.s32 x) := by
  intro a m hi
  show SpecR prof P th (Canon.store Limits.spec Quirks.none cx (.int .s32 x.toInt) (.prim .s32) a)
    m _
  rw [store_s32]
  refine Spec.mono (spec_writeMem hcx.mem _ _) fun _ m' ⟨c', hw, hm⟩ _ _ => ?_
  subst m'
  obtain ⟨hi', hm'⟩ := hi.write hw
  rw [intToLE_s32] at hm'
  exact ⟨hi', Grows.core _ _, .s32 hm'⟩

/-- **The `u32` element store.** -/
theorem spec_store_u32 {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) (x : BitVec 32) :
    ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e LTy.u32.toClosed a)
      (LStore P ra ma .u32) (.u32 x) := by
  intro a m hi
  show SpecR prof P th (Canon.store Limits.spec Quirks.none cx (.int .u32 (x.toNat : Int))
    (.prim .u32) a) m _
  rw [store_u32]
  refine Spec.mono (spec_writeMem hcx.mem _ _) fun _ m' ⟨c', hw, hm⟩ _ _ => ?_
  subst m'
  obtain ⟨hi', hm'⟩ := hi.write hw
  rw [intToLE_u32] at hm'
  exact ⟨hi', Grows.core _ _, .u32 hm'⟩

/-- **The `s64` element store.** -/
theorem spec_store_s64 {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) (x : BitVec 64) :
    ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e LTy.s64.toClosed a)
      (LStore P ra ma .s64) (.s64 x) := by
  intro a m hi
  show SpecR prof P th (Canon.store Limits.spec Quirks.none cx (.int .s64 x.toInt) (.prim .s64) a)
    m _
  rw [store_s64]
  refine Spec.mono (spec_writeMem hcx.mem _ _) fun _ m' ⟨c', hw, hm⟩ _ _ => ?_
  subst m'
  obtain ⟨hi', hm'⟩ := hi.write hw
  rw [intToLE_s64] at hm'
  exact ⟨hi', Grows.core _ _, .s64 hm'⟩

/-- `storeInt` of a pointer-sized number. -/
theorem spec_storeInt_nat {th : Option ThreadId} {ma : Nat} {cx : LiftLowerContext (E3 P)}
    (hcx : cx.opts.memory = some (memAt P ma)) {m : Config (E3 P) Unit} (q a : Nat) :
    SpecR prof P th (storeInt cx (q : Int) a 4) m
      (fun _ m' => ∃ c', Silmaril.Wasm.SingleThreaded.memWrite? m.core ma a
        (le32 (BitVec.ofNat 32 q)) = some c' ∧
        m' = { m with core := c' }) := by
  unfold storeInt
  rw [intToLE_nat]
  exact spec_writeMem hcx _ _

/-- The elements of a list, stored by `LStore`. -/
theorem elems_of {ra ma : Nat} {t : LTy} {us : List LVal} {p : Nat}
    {s s' : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : ElemsRel t.size (LStore P ra ma t) us p s s') : LElems P ra ma t us p s s' := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons he ih

/-- **`store_list_into_range` of a list of values of type `t`** at the element layout of `t`:
the Core-level `LList`, given the element store of `t`. -/
theorem spec_storeListL {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) (t : LTy) (us : List LVal)
    (hel : ∀ u ∈ us, ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e t.toClosed a) (LStore P ra ma t) u)
    {m : Config (E3 P) Unit} (hi : LInv P I ma m) :
    SpecR prof P th (storeListIntoRangeWith cx (ABI.layout .i32 t.toClosed)
      (fun e a => Canon.store Limits.spec Quirks.none cx e t.toClosed a) (us.map LVal.toRef)) m
      (fun r m' => LInv P I ma m' ∧ Grows m m' ∧ ∃ q, r = (q, us.length) ∧
        LList P ra ma t us (cmap m.core) q (cmap m'.core)) := by
  refine Spec.mono (spec_storeListIntoRange hcx _ LVal.toRef _ _ us hel hi)
    fun r m' ⟨hi', hg', q, s₁, hr, hrun, hq, hb, he⟩ _ _ => ⟨hi', hg', q, hr, ?_⟩
  rw [layout_toClosed t] at hrun hq hb he
  exact .mk hrun hq hb (elems_of he)

/-- **The nested list element store**, given the element store of its element type. -/
theorem spec_store_list {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) (t : LTy) (us : List LVal)
    (hel : ∀ u ∈ us, ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e t.toClosed a) (LStore P ra ma t) u) :
    ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e (LTy.list t).toClosed a)
      (LStore P ra ma (.list t)) (.list us) := by
  intro a m hi
  show SpecR prof P th (Canon.store Limits.spec Quirks.none cx (.list (LVal.toRefList us))
    (.list t.toClosed) a) m _
  rw [store_list, toRefList_eq_map]
  refine Spec.bind (Spec.getsCore _) fun p m₁ ⟨hp, hm⟩ _ _ => ?_
  subst m₁
  rw [ptrTypeIn_i32 hcx hi] at hp
  subst hp
  unfold storeListWith
  refine Spec.ite_false rfl ?_
  refine Spec.bind (spec_storeListL hcx t us hel hi) fun r m₂ ⟨hi₂, hg₂, q, hr, hl⟩ _ _ => ?_
  subst r
  dsimp only
  unfold ptrSize
  refine Spec.bind (Spec.bind (Spec.getsCore _) fun p m₃ ⟨hp, hm⟩ _ _ => ?_)
    (R := fun sz m' => sz = 4 ∧ m' = m₂) fun sz m₄ ⟨hsz, hm⟩ _ _ => ?_
  · subst m₃
    rw [ptrTypeIn_i32 hcx hi₂] at hp
    subst hp
    exact Spec.mono (Spec.pure _) fun sz m' ⟨hsz, hm⟩ _ _ => ⟨hsz, hm⟩
  subst m₄ sz
  refine Spec.bind (spec_storeInt_nat hcx.mem q a) fun _ m₅ ⟨c₁, hw₁, hm⟩ _ _ => ?_
  subst m₅
  obtain ⟨hi₅, hm₁⟩ := hi₂.write hw₁
  refine Spec.mono (spec_storeInt_nat hcx.mem us.length (a + 4))
    fun _ m' ⟨c₂, hw₂, hm⟩ _ _ => ?_
  subst m'
  obtain ⟨hi', hm₂⟩ := hi₅.write hw₂
  refine ⟨hi', hg₂.trans ((Grows.core _ _).trans (Grows.core _ _)), ?_⟩
  exact .list hl hm₁ hm₂

theorem storeTuple_nil (cx : LiftLowerContext (E3 P)) (a : Nat) :
    (storeTuple Limits.spec Quirks.none cx [] [] a : Canon.P (E3 P) Unit Unit) = pure () := by
  rw [storeTuple.eq_def]

theorem storeTuple_cons (cx : LiftLowerContext (E3 P)) (v : Value.Val) (vs : List Value.Val)
    (t : WIT.ClosedType RtId) (ts : List (WIT.ClosedType RtId)) (a : Nat) :
    (storeTuple Limits.spec Quirks.none cx (v :: vs) (t :: ts) a : Canon.P (E3 P) Unit Unit) =
      (ptrType cx >>= fun p =>
        Canon.store Limits.spec Quirks.none cx v t (ABI.alignTo a (ABI.layout p t).alignment) >>=
          fun _ => storeTuple Limits.spec Quirks.none cx vs ts
            (ABI.alignTo a (ABI.layout p t).alignment + (ABI.layout p t).size)) := by
  rw [storeTuple.eq_def]

mutual
/-- **Element stores of the fragment's types**, by recursion on the value. -/
theorem spec_store {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) :
    ∀ (t : LTy) (v : LVal), t.check v = true → ElemSpec prof P I ma th LVal.toRef
      (fun e a => Canon.store Limits.spec Quirks.none cx e t.toClosed a) (LStore P ra ma t) v
  | .s32, .s32 x, _ => spec_store_s32 hcx x
  | .u32, .u32 x, _ => spec_store_u32 hcx x
  | .s64, .s64 x, _ => spec_store_s64 hcx x
  | .list t, .list us, h => spec_store_list hcx t us (spec_storeAll hcx t us h)
  | .tuple t ts, .fields vs, h => by
    intro a m hi
    show SpecR prof P th (Canon.store Limits.spec Quirks.none cx (.record (LVal.toRefList vs))
      (.tuple (LTy.toClosedList (t :: ts))) a) m _
    rw [store_tuple]
    exact Spec.mono (spec_storeTuple hcx (t :: ts) vs h a m hi)
      fun _ m' ⟨hi', hg', hf⟩ _ _ => ⟨hi', hg', .tuple hf⟩
  | .record _ l t fs, .fields vs, h => by
    intro a m hi
    show SpecR prof P th (Canon.store Limits.spec Quirks.none cx (.record (LVal.toRefList vs))
      (.record (LTy.toClosedFields ((l, t) :: fs))) a) m _
    rw [store_record, storeFields_eq, toClosedFields_eq]
    exact Spec.mono (spec_storeTuple hcx (((l, t) :: fs).map (·.2)) vs
      (by simpa only [LTy.check, List.map_cons] using h) a m hi)
      fun _ m' ⟨hi', hg', hf⟩ _ _ => ⟨hi', hg', .record hf⟩
  | .s32, .list _, h | .s32, .u32 _, h | .s32, .s64 _, h | .s32, .fields _, h
  | .list _, .s32 _, h | .list _, .u32 _, h | .list _, .s64 _, h | .list _, .fields _, h
  | .u32, .s32 _, h | .u32, .list _, h | .u32, .s64 _, h | .u32, .fields _, h
  | .s64, .s32 _, h | .s64, .list _, h | .s64, .u32 _, h | .s64, .fields _, h
  | .tuple _ _, .s32 _, h | .tuple _ _, .list _, h | .tuple _ _, .u32 _, h
  | .tuple _ _, .s64 _, h | .record _ _ _ _, .s32 _, h | .record _ _ _ _, .list _, h
  | .record _ _ _ _, .u32 _, h | .record _ _ _ _, .s64 _, h => nomatch h

/-- The element stores of the values of a list. -/
theorem spec_storeAll {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat}
    {th : Option ThreadId} {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) :
    ∀ (t : LTy) (us : List LVal), LTy.checkList t us = true → ∀ u ∈ us,
      ElemSpec prof P I ma th LVal.toRef
        (fun e a => Canon.store Limits.spec Quirks.none cx e t.toClosed a) (LStore P ra ma t) u
  | _, [], _, _, hu => nomatch hu
  | t, v :: vs, h, u, hu => by
    simp only [LTy.checkList, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hu with e | hu
    · exact e ▸ spec_store hcx t v h.1
    · exact spec_storeAll hcx t vs h.2 u hu

/-- **`store_record`** of the fields `vs` of types `ts` from the cursor `a`: `LFields`. -/
theorem spec_storeTuple {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat}
    {th : Option ThreadId} {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) :
    ∀ (ts : List LTy) (vs : List LVal), LTy.checkFields ts vs = true →
    ∀ (a : Nat) (m : Config (E3 P) Unit), LInv P I ma m →
      SpecR prof P th (storeTuple Limits.spec Quirks.none cx (LVal.toRefList vs)
        (LTy.toClosedList ts) a) m
        (fun _ m' => LInv P I ma m' ∧ Grows m m' ∧
          LFields P ra ma ts vs a (cmap m.core) (cmap m'.core))
  | [], [], _, a, m, hi => by
    simp only [LVal.toRefList, LTy.toClosedList]
    rw [storeTuple_nil]
    exact Spec.mono (Spec.pure _) fun _ m' ⟨_, hm⟩ _ _ => by
      subst m'
      exact ⟨hi, Grows.refl _, .nil⟩
  | t :: ts, v :: vs, h, a, m, hi => by
    simp only [LTy.checkFields, Bool.and_eq_true] at h
    simp only [LVal.toRefList, LTy.toClosedList]
    rw [storeTuple_cons]
    refine Spec.bind (Spec.getsCore _) fun p m₁ ⟨hp, hm⟩ _ _ => ?_
    subst m₁
    rw [ptrTypeIn_i32 hcx hi] at hp
    subst hp
    rw [layout_toClosed t]
    refine Spec.bind (spec_store hcx t v h.1 _ m hi) fun _ m₁ ⟨hi₁, hg₁, hs₁⟩ _ _ => ?_
    exact Spec.mono (spec_storeTuple hcx ts vs h.2 _ m₁ hi₁)
      fun _ m' ⟨hi', hg', hf⟩ _ _ => ⟨hi', hg₁.trans hg', .cons hs₁ hf⟩
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => nomatch h
end

/-! ## Parameters -/

theorem lowerFlatAt_s32 (cx : LiftLowerContext (E3 P)) (x : BitVec 32) :
    (lowerFlatAt Limits.spec Quirks.none cx .i32 (.int .s32 x.toInt) (.prim .s32) :
      Canon.P (E3 P) Unit (List FlatValue)) = Prog.pure [⟨.int .i32, x⟩] := by
  show Prog.pure [lowerFlatInt .s32 x.toInt] = _
  have e : lowerFlatInt .s32 x.toInt = (⟨.int .i32, x⟩ : FlatValue) := by
    show (⟨.int .i32, BitVec.ofInt 32 x.toInt⟩ : FlatValue) = ⟨.int .i32, x⟩
    rw [BitVec.ofInt_toInt]
  rw [e]

/-- **The flat lowering of the parameters** (`lower_flat` of each, left to right). -/
theorem spec_lowerFlatTypes {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat}
    {th : Option ThreadId} {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) :
    ∀ (ts : List LTy) (vs : List LVal), LTy.checkParams ts vs = true →
    (∀ t ∈ ts, t.topLevel = true) → ∀ (m : Config (E3 P) Unit), LInv P I ma m →
      SpecR prof P th (lowerFlatTypes Limits.spec Quirks.none cx .i32 (vs.map LVal.toRef)
        (ts.map LTy.toClosed)) m
        (fun fl m' => LInv P I ma m' ∧ Grows m m' ∧
          LParams P ra ma ts vs (cmap m.core) (fl.map Silmaril.Wasm.SingleThreaded.ofFlat)
            (cmap m'.core))
  | [], [], _, _, m, hi => Spec.mono (Spec.pure _) fun fl m' ⟨hfl, hm⟩ _ _ => by
      subst fl m'
      exact ⟨hi, Grows.refl _, .nil⟩
  | .s32 :: ts, .s32 x :: vs, h, htop, m, hi => by
    simp only [LTy.checkParams, LTy.check, Bool.true_and] at h
    show SpecR prof P th (lowerFlatAt Limits.spec Quirks.none cx .i32 (.int .s32 x.toInt)
      (.prim .s32) >>= fun a => lowerFlatTypes Limits.spec Quirks.none cx .i32 (vs.map LVal.toRef)
        (ts.map LTy.toClosed) >>= fun b => pure (a ++ b)) m _
    rw [lowerFlatAt_s32]
    refine Spec.bind (Spec.pure _) fun a m₁ ⟨ha, hm⟩ _ _ => ?_
    subst a m₁
    refine Spec.bind (spec_lowerFlatTypes hcx ts vs h
      (fun t ht => htop t (List.mem_cons_of_mem _ ht)) m hi) fun b m₂ ⟨hi₂, hg₂, hp₂⟩ _ _ => ?_
    refine Spec.mono (Spec.pure _) fun fl m' ⟨hfl, hm⟩ _ _ => ?_
    subst fl m'
    exact ⟨hi₂, hg₂, .s32 hp₂⟩
  | .list t :: ts, .list us :: vs, h, htop, m, hi => by
    simp only [LTy.checkParams, LTy.check, Bool.and_eq_true] at h
    show SpecR prof P th ((storeListIntoRange Limits.spec Quirks.none cx (LVal.toRefList us)
      t.toClosed >>= fun r => match r with
        | (ptr, len) => pure [ptrFlat .i32 ptr, ptrFlat .i32 len]) >>= fun a =>
      lowerFlatTypes Limits.spec Quirks.none cx .i32 (vs.map LVal.toRef)
        (ts.map LTy.toClosed) >>= fun b => pure (a ++ b)) m _
    unfold storeListIntoRange
    rw [toRefList_eq_map]
    simp only [bind_assoc]
    refine Spec.bind (Spec.getsCore _) fun p m₁ ⟨hp, hm⟩ _ _ => ?_
    subst m₁
    rw [ptrTypeIn_i32 hcx hi] at hp
    subst hp
    refine Spec.bind (spec_storeListL hcx t us (spec_storeAll hcx t us h.1) hi)
      fun r m₂ ⟨hi₂, hg₂, q, hr, hl⟩ _ _ => ?_
    subst r
    refine Spec.bind (Spec.pure _) fun a m₃ ⟨ha, hm⟩ _ _ => ?_
    subst a m₃
    refine Spec.bind (spec_lowerFlatTypes hcx ts vs h.2
      (fun t ht => htop t (List.mem_cons_of_mem _ ht)) m₂ hi₂)
      fun b m₄ ⟨hi₄, hg₄, hp₄⟩ _ _ => ?_
    refine Spec.mono (Spec.pure _) fun fl m' ⟨hfl, hm⟩ _ _ => ?_
    subst fl m'
    exact ⟨hi₄, hg₂.trans hg₄, .list hl hp₄⟩
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h
  | .s32 :: _, .list _ :: _, h, _, _, _ | .s32 :: _, .u32 _ :: _, h, _, _, _
  | .s32 :: _, .s64 _ :: _, h, _, _, _ | .s32 :: _, .fields _ :: _, h, _, _, _
  | .list _ :: _, .s32 _ :: _, h, _, _, _ | .list _ :: _, .u32 _ :: _, h, _, _, _
  | .list _ :: _, .s64 _ :: _, h, _, _, _ | .list _ :: _, .fields _ :: _, h, _, _, _ => by
    simp [LTy.checkParams, LTy.check] at h
  | .u32 :: _, _ :: _, _, htop, _, _ | .s64 :: _, _ :: _, _, htop, _, _
  | .tuple _ _ :: _, _ :: _, _, htop, _, _ | .record _ _ _ _ :: _, _ :: _, _, htop, _, _ => by
    simp [LTy.topLevel] at htop

theorem flatten_length {t : LTy} (ht : t.topLevel = true) :
    (ABI.flatten .i32 t.toClosed).length ≤ 2 := by
  cases t <;> simp_all [LTy.topLevel, LTy.toClosed, ABI.flatten, ABI.flattenPrimitive]

theorem flattenTypes_length : ∀ ts : List LTy, (∀ t ∈ ts, t.topLevel = true) →
    (ABI.flattenTypes .i32 (ts.map LTy.toClosed)).length ≤ 2 * ts.length
  | [], _ => by simp [ABI.flattenTypes]
  | t :: ts, htop => by
    have h₁ := flatten_length (htop t List.mem_cons_self)
    have h₂ := flattenTypes_length ts fun t ht => htop t (List.mem_cons_of_mem _ ht)
    simp only [List.map_cons, ABI.flattenTypes, List.length_append, List.length_cons]
    omega

/-- **The flat lowering of the parameters** by `lower_flat_values` (at most `16` flat
values: no spilling). -/
theorem spec_lowerParams {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat}
    {th : Option ThreadId} {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx)
    (ts : List LTy) (hts : 2 * ts.length ≤ 16) (htop : ∀ t ∈ ts, t.topLevel = true)
    (vs : List LVal) (hvs : LTy.checkParams ts vs = true) {m : Config (E3 P) Unit}
    (hi : LInv P I ma m) :
    SpecR prof P th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
      (vs.map LVal.toRef) (ts.map LTy.toClosed) none) m
      (fun fl m' => LInv P I ma m' ∧ Grows m m' ∧
        LParams P ra ma ts vs (cmap m.core) (fl.map Silmaril.Wasm.SingleThreaded.ofFlat)
          (cmap m'.core)) := by
  unfold lowerFlatValues
  refine Spec.bind (Spec.getsCore _) fun p m₁ ⟨hp, hm⟩ _ _ => ?_
  subst m₁
  rw [ptrTypeIn_i32 hcx hi] at hp
  subst hp
  split
  · next h =>
    have := flattenTypes_length ts htop
    exact absurd h (by unfold ABI.maxFlatParams; omega)
  · exact spec_lowerFlatTypes hcx ts vs hvs htop m hi

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
