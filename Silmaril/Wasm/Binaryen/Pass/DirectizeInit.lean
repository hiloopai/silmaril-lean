module

public import Silmaril.Wasm.Binaryen.ElemInit
public import Silmaril.Wasm.Binaryen.InlStore
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitTrap

@[expose] public section

/-! # Directize: the element segments at instantiation

The Directize simulation (`Binaryen/DirectizeRun.lean`) starts after the element segments
of the instantiation code have run, because only then do the tables hold the slots that
Directize read. This file supplies the two facts about the executable segment
initialiser (`initElemList?`, `initElemListT?`, `Exec/SegmentInit.lean`) that the start
needs:

* **it ignores the functions of the store** (`initElemListT?_withFuncs`): the left and
  right stores differ only in their functions, so the segments run the same on both;
* **it never fails** for segments with `i32.const` offsets whose table and element
  lookups succeed (`initElemListT?_ne_fail`): the segments either run or trap.
-/

namespace Silmaril.Wasm.Binaryen

namespace DirectizeInit

open Execution.Core Numerics Validation ElemInit InlS

variable {H : Type}

/-! ## The functions of the store are not read -/

theorem table?_withFuncs (s : Store H) (G : List (FuncInst H)) (f : Frame) (x : TableIdx) :
    (withFuncs s G).table? f x = s.table? f x := rfl

theorem elem?_withFuncs (s : Store H) (G : List (FuncInst H)) (f : Frame) (y : ElemIdx) :
    (withFuncs s G).elem? f y = s.elem? f y := rfl

theorem setTable_withFuncs (s : Store H) (G : List (FuncInst H)) (ta : Nat) (ti : TableInst) :
    (withFuncs s G).setTable ta ti = withFuncs (s.setTable ta ti) G := rfl

theorem tableInitLoop_withFuncs {x : TableIdx} {y : ElemIdx} {a : AddrType}
    (G : List (FuncInst H)) (f : Frame) :
    ∀ (n : BitVec 32) (s : Store H) (i : BitVec a.intType.width) (j : BitVec 32),
      tableInitLoop (withFuncs s G) f x y a i j n =
        (tableInitLoop s f x y a i j n).map (withFuncs · G) := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ m ih =>
  intro s i j
  rw [tableInitLoop, tableInitLoop, table?_withFuncs, elem?_withFuncs]
  split
  · split
    · split
      · rfl
      · rename_i hn
        split
        · rename_i r _
          rw [setTable_withFuncs]
          exact ih _ (by rw [← h]; exact bv32_sub_one_lt hn) _ rfl _ _ _
        · rfl
    · rfl
  · rfl

theorem elemDrop?_withFuncs (s : Store H) (G : List (FuncInst H)) (f : Frame) (y : ElemIdx) :
    elemDrop? (withFuncs s G) f y = (elemDrop? s f y).map (withFuncs · G) := by
  unfold elemDrop?
  rw [elem?_withFuncs]
  cases s.elem? f y <;> rfl

/-- Segments of the profile: an active segment has an `i32.const` offset. -/
def ConstSeg (e : Elem) : Prop := ∀ y off, e.mode = .active y off → ∃ o : BitVec 32, off = [.intConst .i32 o]

theorem initElemSeg?_withFuncs {ev : Store H → Frame → Expr → Option (Store H × Val)} {f : Frame}
    (hev : ConstOffsets ev f) (G : List (FuncInst H)) (s : Store H) (k : Nat) {e : Elem}
    (he : ConstSeg e) :
    initElemSeg? ev (withFuncs s G) f k e = (initElemSeg? ev s f k e).map (withFuncs · G) := by
  unfold initElemSeg?
  split
  · rfl
  · exact elemDrop?_withFuncs _ _ _ _
  · rename_i y off hm
    obtain ⟨o, rfl⟩ := he y off hm
    rw [hev, hev]
    simp only [Val.addr?]
    erw [tableInitLoop_withFuncs]
    cases tableInitLoop s f y ⟨Fin.ofNat _ k⟩ .i32 o 0 (BitVec.ofNat 32 e.init.length) with
    | none => rfl
    | some s₂ => exact elemDrop?_withFuncs _ _ _ _

theorem tableInitOob?_withFuncs (s : Store H) (G : List (FuncInst H)) (f : Frame) (x : TableIdx)
    (y : ElemIdx) (a : AddrType) (i : BitVec a.intType.width) (j n : BitVec 32) :
    tableInitOob? (withFuncs s G) f x y a i j n = tableInitOob? s f x y a i j n := rfl

theorem elemSegTrap?_withFuncs {ev : Store H → Frame → Expr → Option (Store H × Val)} {f : Frame}
    (hev : ConstOffsets ev f) (G : List (FuncInst H)) (s : Store H) (k : Nat) {e : Elem}
    (he : ConstSeg e) :
    elemSegTrap? ev (withFuncs s G) f k e = (elemSegTrap? ev s f k e).map (withFuncs · G) := by
  unfold elemSegTrap?
  split
  · rename_i y off hm
    obtain ⟨o, rfl⟩ := he y off hm
    rw [hev, hev]
    simp only [Val.addr?]
    split <;> split
    · rfl
    · rename_i h₁ h₂; exact absurd h₁ h₂
    · rename_i h₁ h₂; exact absurd h₂ h₁
    · rfl
  · rfl

/-- `SegResult` along `withFuncs`. -/
def resMap (G : List (FuncInst H)) : SegResult H (Store H) → SegResult H (Store H)
  | .ok s => .ok (withFuncs s G)
  | .trap s => .trap (withFuncs s G)
  | .fail => .fail

theorem initElemSegT?_withFuncs {ev : Store H → Frame → Expr → Option (Store H × Val)}
    {f : Frame} (hev : ConstOffsets ev f) (G : List (FuncInst H)) (s : Store H) (k : Nat)
    {e : Elem} (he : ConstSeg e) :
    initElemSegT? ev (withFuncs s G) f k e = resMap G (initElemSegT? ev s f k e) := by
  unfold initElemSegT?
  rw [initElemSeg?_withFuncs hev G s k he, elemSegTrap?_withFuncs hev G s k he]
  cases initElemSeg? ev s f k e with
  | some s' => rfl
  | none => cases elemSegTrap? ev s f k e <;> rfl

theorem initElemListT?_withFuncs {ev : Store H → Frame → Expr → Option (Store H × Val)}
    {f : Frame} (hev : ConstOffsets ev f) (G : List (FuncInst H)) :
    ∀ (L : List (Nat × Elem)) (s : Store H), (∀ p ∈ L, ConstSeg p.2) →
      initElemListT? ev (withFuncs s G) f L = resMap G (initElemListT? ev s f L)
  | [], s, _ => rfl
  | (k, e) :: L, s, hL => by
    simp only [initElemListT?]
    rw [initElemSegT?_withFuncs hev G s k (hL (k, e) (by simp))]
    cases initElemSegT? ev s f k e with
    | ok s₁ => exact initElemListT?_withFuncs hev G L s₁ (fun p hp => hL p (by simp [hp]))
    | trap s₁ => rfl
    | fail => rfl

/-! ## The segments never fail -/

theorem tableInitLoop_isSome {x : TableIdx} {y : ElemIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s : Store H} {f : Frame} {i : BitVec a.intType.width} {j : BitVec 32}
      {ta ea : Nat} {ti : TableInst} {ei : ElemInst},
      s.table? f x = some (ta, ti) → s.elem? f y = some (ea, ei) →
      i.toNat + n.toNat ≤ ti.refs.length → j.toNat + n.toNat ≤ ei.refs.length →
      (tableInitLoop s f x y a i j n).isSome := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ m ih =>
  intro s f i j ta ea ti ei ht he hi hj
  rw [tableInitLoop, ht, he]
  simp only
  rw [ite_eq_left ⟨by omega, by omega⟩]
  split
  · rfl
  · rename_i hn
    have hn' := bv32_toNat_sub_one hn
    have hpos : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hn
      · exact h0
    have hjr : j.toNat < ei.refs.length := by omega
    rw [List.getElem?_eq_getElem hjr]
    simp only
    have hta : ta < s.tables.length := by
      simp only [Store.table?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨_, -, ti', hti, rfl, rfl⟩ := ht
      exact (List.getElem?_eq_some_iff.mp hti).1
    have ht' : (s.setTable ta { ti with refs := ti.refs.set i.toNat ei.refs[j.toNat] }).table? f x =
        some (ta, { ti with refs := ti.refs.set i.toNat ei.refs[j.toNat] }) := by
      simp only [Store.table?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at ht ⊢
      obtain ⟨ta', hx, ti', hti, rfl, rfl⟩ := ht
      exact ⟨ta', hx, _, by simp [Store.setTable, hta], rfl, rfl⟩
    refine ih _ (by rw [← h]; exact bv32_sub_one_lt hn) _ rfl ht' (by rw [elem?_setTable]; exact he)
      ?_ ?_
    · have := bv_toNat_add_one_le i
      simp only [List.length_set]
      omega
    · have := bv_toNat_add_one_le j
      omega

/-- The lookups a segment needs. -/
structure SegLookups (s : Store H) (f : Frame) (p : Nat × Elem) : Prop where
  elem : ∃ ea ei, s.elem? f ⟨Fin.ofNat _ p.1⟩ = some (ea, ei)
  table : ∀ y off, p.2.mode = .active y off → ∃ ta ti, s.table? f y = some (ta, ti)

/-- Stores with the same table lengths and the same element addresses. -/
structure SameShape (s s' : Store H) : Prop where
  tables : ∀ ta, tableLen s' ta = tableLen s ta
  elems : s'.elems.length = s.elems.length

theorem SameShape.lookups {s s' : Store H} (h : SameShape s s') {f : Frame} {p : Nat × Elem}
    (hl : SegLookups s f p) : SegLookups s' f p := by
  refine ⟨?_, fun y off hm => ?_⟩
  · obtain ⟨ea, ei, he⟩ := hl.elem
    simp only [Store.elem?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at he ⊢
    obtain ⟨ea', hx, ei', hei, rfl, rfl⟩ := he
    have hlt : ea' < s'.elems.length := by
      have := (List.getElem?_eq_some_iff.mp hei).1; have := h.elems; omega
    exact ⟨ea', s'.elems[ea'], ea', hx, s'.elems[ea'], List.getElem?_eq_getElem hlt, rfl, rfl⟩
  · obtain ⟨ta, ti, ht⟩ := hl.table y off hm
    simp only [Store.table?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at ht ⊢
    obtain ⟨ta', hx, ti', hti, rfl, rfl⟩ := ht
    have e := h.tables ta'
    unfold tableLen at e
    rw [hti] at e
    cases h' : s'.tables[ta']? with
    | none => rw [h'] at e; cases e
    | some ti'' => exact ⟨ta', _, ta', hx, ti'', h', rfl, rfl⟩

theorem SameShape.refl (s : Store H) : SameShape s s := ⟨fun _ => rfl, rfl⟩

theorem SameShape.trans {s₁ s₂ s₃ : Store H} (h₁ : SameShape s₁ s₂) (h₂ : SameShape s₂ s₃) :
    SameShape s₁ s₃ := ⟨fun ta => (h₂.tables ta).trans (h₁.tables ta), h₂.elems.trans h₁.elems⟩

theorem sameShape_setElem (s : Store H) (ea : Nat) (rs : List Ref) : SameShape s (s.setElem ea rs) :=
  ⟨fun _ => rfl, by simp [Store.setElem]⟩

theorem elemDrop?_shape {s s' : Store H} {f : Frame} {y : ElemIdx} (h : elemDrop? s f y = some s') :
    SameShape s s' := by
  unfold elemDrop? at h
  cases he : s.elem? f y with
  | none => rw [he] at h; cases h
  | some q =>
    rw [he] at h
    cases h
    exact sameShape_setElem _ _ _

theorem tableInitLoop_shape {x : TableIdx} {y : ElemIdx} {a : AddrType} (n : BitVec 32)
    {s s' : Store H} {f : Frame} {i : BitVec a.intType.width} {j : BitVec 32}
    (h : tableInitLoop s f x y a i j n = some s') : SameShape s s' :=
  ⟨tableInitLoop_len n h, by rw [(tableInitLoop_elems n h).1]⟩

theorem elemDrop?_isSome {s : Store H} {f : Frame} {y : ElemIdx} {ea : Nat} {ei : ElemInst}
    (h : s.elem? f y = some (ea, ei)) : ∃ s', elemDrop? s f y = some s' := by
  unfold elemDrop?; rw [h]; exact ⟨_, rfl⟩

theorem tableInitLoop_oob {x : TableIdx} {y : ElemIdx} {a : AddrType} {s : Store H} {f : Frame}
    {i : BitVec a.intType.width} {j n : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
    (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
    (hb : ¬ (i.toNat + n.toNat ≤ ti.refs.length ∧ j.toNat + n.toNat ≤ ei.refs.length)) :
    tableInitLoop s f x y a i j n = none := by
  rw [tableInitLoop, ht, he]
  simp only
  rw [ite_eq_right hb]

/-- **One segment runs or traps.** -/
theorem initElemSegT?_cases {ev : Store H → Frame → Expr → Option (Store H × Val)} {f : Frame}
    (hev : ConstOffsets ev f) {s : Store H} {p : Nat × Elem} (hc : ConstSeg p.2)
    (hl : SegLookups s f p) :
    (∃ s', initElemSegT? ev s f p.1 p.2 = .ok s' ∧ SameShape s s') ∨
      ∃ s', initElemSegT? ev s f p.1 p.2 = .trap s' := by
  obtain ⟨k, e⟩ := p
  obtain ⟨ea, ei, he⟩ := hl.elem
  simp only at he hc ⊢
  unfold initElemSegT?
  cases hm : e.mode with
  | passive => left; exact ⟨s, by simp [initElemSeg?, hm], SameShape.refl s⟩
  | declarative =>
    obtain ⟨s', hs'⟩ := elemDrop?_isSome he
    left; exact ⟨s', by simp only [initElemSeg?, hm]; rw [hs'], elemDrop?_shape hs'⟩
  | active y off =>
    obtain ⟨o, rfl⟩ := hc y off hm
    obtain ⟨ta, ti, ht⟩ := hl.table y _ hm
    by_cases hb : o.toNat + (BitVec.ofNat 32 e.init.length).toNat ≤ ti.refs.length ∧
        (0 : BitVec 32).toNat + (BitVec.ofNat 32 e.init.length).toNat ≤ ei.refs.length
    · obtain ⟨s₂, hs₂⟩ := Option.isSome_iff_exists.mp
        (tableInitLoop_isSome (a := .i32) (i := o) (j := 0) _ ht he hb.1 hb.2)
      have he₂ : s₂.elem? f ⟨Fin.ofNat _ k⟩ = some (ea, ei) := by
        rw [← he]; simp only [Store.elem?, (tableInitLoop_elems _ hs₂).1]
      obtain ⟨s', hs'⟩ := elemDrop?_isSome he₂
      left
      refine ⟨s', ?_, (tableInitLoop_shape _ hs₂).trans (elemDrop?_shape hs')⟩
      simp only [initElemSeg?, hm]
      rw [hev s o]
      simp only [Val.addr?]
      erw [hs₂]
      simp only
      rw [hs']
    · right
      have hn : initElemSeg? ev s f k e = none := by
        simp only [initElemSeg?, hm]
        rw [hev s o]
        simp only [Val.addr?]
        erw [tableInitLoop_oob (a := .i32) (i := o) (j := 0) ht he hb]
      refine ⟨s, ?_⟩
      simp only [hn, elemSegTrap?, hm]
      rw [hev s o]
      simp only [Val.addr?]
      have hoob : tableInitOob? s f y ⟨Fin.ofNat _ k⟩ .i32 o 0 (BitVec.ofNat 32 e.init.length) =
          true := by
        simp only [tableInitOob?, ht, he, decide_eq_true_eq]
        by_contra hcon
        simp only [not_or, Nat.not_lt] at hcon
        exact hb ⟨hcon.1, hcon.2⟩
      erw [hoob]
      rfl

/-- **The element segments run or trap.** -/
theorem initElemListT?_cases {ev : Store H → Frame → Expr → Option (Store H × Val)} {f : Frame}
    (hev : ConstOffsets ev f) :
    ∀ (L : List (Nat × Elem)) (s : Store H), (∀ p ∈ L, ConstSeg p.2) →
      (∀ p ∈ L, SegLookups s f p) →
      (∃ s', initElemListT? ev s f L = .ok s') ∨ ∃ s', initElemListT? ev s f L = .trap s'
  | [], s, _, _ => .inl ⟨s, rfl⟩
  | p :: L, s, hc, hl => by
    simp only [initElemListT?]
    rcases initElemSegT?_cases hev (hc p (by simp)) (hl p (by simp)) with ⟨s₁, h₁, hsh⟩ |
        ⟨s₁, h₁⟩
    · rw [show initElemSegT? ev s f p.1 p.2 = .ok s₁ from h₁]
      exact initElemListT?_cases hev L s₁ (fun q hq => hc q (by simp [hq]))
        (fun q hq => hsh.lookups (hl q (by simp [hq])))
    · rw [show initElemSegT? ev s f p.1 p.2 = .trap s₁ from h₁]
      exact .inr ⟨s₁, rfl⟩

end DirectizeInit

end Silmaril.Wasm.Binaryen
