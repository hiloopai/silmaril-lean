module

public import Silmaril.Wasm.Component.ABI.Defs

/-!
# Canonical ABI round trip: proofs

Proofs for `Silmaril.Wasm.Component.ABI.Thms`: lifting a lowered well-typed value
gives it back (`lift_lower`), lowered values have the flattened types
(`lower_types`), lifted values are well typed (`check_of_lift`), and the
canonicalisation of trivially-represented types is a type check
(`canonFlat_trivial`).
-/

public section

namespace Silmaril.Proofs.Wasm.Component.ABI

open Silmaril.Wasm.Component
open Silmaril.Wasm (NumType IntType FloatType)

/-! ## Bit vectors and flat values -/

theorem truncate_signExtend {n m : Nat} (h : n ≤ m) (x : BitVec n) :
    (x.signExtend m).setWidth n = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have him : i < m := Nat.lt_of_lt_of_le hi h
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi, him, decide_true,
    Bool.true_and, ite_true]

theorem truncate_zeroExtend {n m : Nat} (h : n ≤ m) (x : BitVec n) :
    (x.setWidth m).setWidth n = x := by
  rw [BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]

theorem retype_retype {a b : NumType} (v : Flat) (hv : v.type = a) (h : a.width ≤ b.width) :
    Flat.retype a (Flat.retype b v) = v := by
  obtain ⟨t, x⟩ := v
  cases hv
  simp only [Flat.retype, truncate_zeroExtend h]

theorem retype_type (t : NumType) (v : Flat) : (Flat.retype t v).type = t := rfl

theorem width_le_joinType_left (a b : NumType) : a.width ≤ (joinType a b).width := by
  rcases a with (a | a) <;> cases a <;> rcases b with (b | b) <;> cases b <;> decide

theorem width_le_joinType_right (a b : NumType) : b.width ≤ (joinType a b).width := by
  rcases a with (a | a) <;> cases a <;> rcases b with (b | b) <;> cases b <;> decide

/-- `Dom xs ys`: the slots `ys` can carry values of the types `xs`. -/
inductive Dom : List NumType → List NumType → Prop
  | nil (ys : List NumType) : Dom [] ys
  | cons {a b : NumType} {xs ys : List NumType} : a.width ≤ b.width → Dom xs ys →
      Dom (a :: xs) (b :: ys)

theorem Dom.refl : ∀ xs : List NumType, Dom xs xs
  | [] => .nil _
  | _ :: xs => .cons (le_refl _) (Dom.refl xs)

theorem Dom.trans : ∀ {xs ys zs : List NumType}, Dom xs ys → Dom ys zs → Dom xs zs
  | _, _, _, .nil _, _ => .nil _
  | _, _, _, .cons h₁ d₁, .cons h₂ d₂ => .cons (le_trans h₁ h₂) (Dom.trans d₁ d₂)

theorem Dom.joinFlat_left : ∀ xs ys : List NumType, Dom xs (joinFlat xs ys)
  | [], _ => .nil _
  | x :: xs, [] => by simpa [joinFlat] using Dom.refl (x :: xs)
  | x :: xs, y :: ys => .cons (width_le_joinType_left x y) (Dom.joinFlat_left xs ys)

theorem Dom.joinFlat_right : ∀ xs ys : List NumType, Dom ys (joinFlat xs ys)
  | [], ys => by simpa [joinFlat] using Dom.refl ys
  | _ :: _, [] => .nil _
  | x :: xs, y :: ys => .cons (width_le_joinType_right x y) (Dom.joinFlat_right xs ys)

theorem fit_types : ∀ (ts : List NumType) (vs : List Flat), (Flat.fit ts vs).map (·.type) = ts
  | [], _ => rfl
  | t :: ts, [] => by simp [Flat.fit, fit_types ts [], Silmaril.Wasm.Execution.Runtime.Value.zero]
  | t :: ts, v :: vs => by simp [Flat.fit, fit_types ts vs, retype_type]

theorem unfit_fit : ∀ {xs ys : List NumType} {vs : List Flat}, vs.map (·.type) = xs →
    Dom xs ys → Flat.unfit xs (Flat.fit ys vs) = vs
  | _, _, [], rfl, _ => by cases ‹Dom _ _›; simp [Flat.unfit]
  | _, _, v :: vs, rfl, .cons h d => by
    simp only [List.map_cons] at h d ⊢
    simp only [Flat.fit, Flat.unfit, retype_retype v rfl h, unfit_fit rfl d]

theorem take_append : ∀ {ts : List NumType} {xs : List Flat} (r : List Flat),
    xs.map (·.type) = ts → Flat.take ts (xs ++ r) = some (xs, r)
  | _, [], r, rfl => rfl
  | _, x :: xs, r, rfl => by
    simp [Flat.take, take_append r (rfl : xs.map (·.type) = _)]

theorem take_spec : ∀ {ts : List NumType} {xs ys r : List Flat},
    Flat.take ts xs = some (ys, r) → xs = ys ++ r ∧ ys.map (·.type) = ts
  | [], xs, ys, r, h => by simp [Flat.take] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | _ :: _, [], _, _, h => by simp [Flat.take] at h
  | t :: ts, x :: xs, ys, r, h => by
    simp only [Flat.take] at h
    split at h
    · cases e : Flat.take ts xs with
      | none => simp [e] at h
      | some p =>
        obtain ⟨ys', r'⟩ := p
        simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h₁, h₂⟩ := take_spec e
        exact ⟨by simp [h₁], by simp [*]⟩
    · simp at h

theorem toNat_ofNat_32 {i : Nat} (h : i < 2 ^ 32) : (BitVec.ofNat 32 i).toNat = i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_ofNat_i32 {i : Nat} (h : i < 2 ^ 32) :
    @BitVec.toNat (NumType.int IntType.i32).width (BitVec.ofNat 32 i) = i := toNat_ofNat_32 h

theorem charOfBits_val (c : Char) : charOfBits c.val.toBitVec = some c := by
  simp [charOfBits, c.valid]

/-! ## Domination of case payloads -/

theorem Dom.flatCases_head (c : Option ValTy) (cs : List (Option ValTy)) :
    Dom (ValTy.flatOpt c) (ValTy.flatCases (c :: cs)) := by
  simpa [ValTy.flatCases] using Dom.joinFlat_left _ _

theorem Dom.flatCases_tail (c : Option ValTy) (cs : List (Option ValTy)) :
    Dom (ValTy.flatCases cs) (ValTy.flatCases (c :: cs)) := by
  simpa [ValTy.flatCases] using Dom.joinFlat_right _ _

/-! ## Lowered values have the flattened types -/

mutual
theorem lower_types : ∀ (t : ValTy) (v : Val), t.check v = true →
    (t.lower v).map (·.type) = t.flat
  | .bool, .bool _, _ | .s8, .s8 _, _ | .u8, .u8 _, _ | .s16, .s16 _, _ | .u16, .u16 _, _
  | .s32, .s32 _, _ | .u32, .u32 _, _ | .s64, .s64 _, _ | .u64, .u64 _, _
  | .f32, .f32 _, _ | .f64, .f64 _, _ | .char, .char _, _ => rfl
  | .record ts, .record vs, h => by
    simp only [ValTy.check] at h
    simp only [ValTy.lower, ValTy.flat]
    exact lowerList_types ts vs h
  | .variant cs, .variant i p, _ => by
    simp only [ValTy.lower, ValTy.flat, List.map_cons, fit_types]
  | .bool, .s8 _, h | .bool, .u8 _, h | .bool, .s16 _, h | .bool, .u16 _, h
  | .bool, .s32 _, h | .bool, .u32 _, h | .bool, .s64 _, h | .bool, .u64 _, h
  | .bool, .f32 _, h | .bool, .f64 _, h | .bool, .char _, h | .bool, .record _, h
  | .bool, .variant _ _, h => by simp [ValTy.check] at h
  | .s8, .bool _, h | .s8, .u8 _, h | .s8, .s16 _, h | .s8, .u16 _, h
  | .s8, .s32 _, h | .s8, .u32 _, h | .s8, .s64 _, h | .s8, .u64 _, h
  | .s8, .f32 _, h | .s8, .f64 _, h | .s8, .char _, h | .s8, .record _, h
  | .s8, .variant _ _, h => by simp [ValTy.check] at h
  | .u8, .bool _, h | .u8, .s8 _, h | .u8, .s16 _, h | .u8, .u16 _, h
  | .u8, .s32 _, h | .u8, .u32 _, h | .u8, .s64 _, h | .u8, .u64 _, h
  | .u8, .f32 _, h | .u8, .f64 _, h | .u8, .char _, h | .u8, .record _, h
  | .u8, .variant _ _, h => by simp [ValTy.check] at h
  | .s16, .bool _, h | .s16, .s8 _, h | .s16, .u8 _, h | .s16, .u16 _, h
  | .s16, .s32 _, h | .s16, .u32 _, h | .s16, .s64 _, h | .s16, .u64 _, h
  | .s16, .f32 _, h | .s16, .f64 _, h | .s16, .char _, h | .s16, .record _, h
  | .s16, .variant _ _, h => by simp [ValTy.check] at h
  | .u16, .bool _, h | .u16, .s8 _, h | .u16, .u8 _, h | .u16, .s16 _, h
  | .u16, .s32 _, h | .u16, .u32 _, h | .u16, .s64 _, h | .u16, .u64 _, h
  | .u16, .f32 _, h | .u16, .f64 _, h | .u16, .char _, h | .u16, .record _, h
  | .u16, .variant _ _, h => by simp [ValTy.check] at h
  | .s32, .bool _, h | .s32, .s8 _, h | .s32, .u8 _, h | .s32, .s16 _, h
  | .s32, .u16 _, h | .s32, .u32 _, h | .s32, .s64 _, h | .s32, .u64 _, h
  | .s32, .f32 _, h | .s32, .f64 _, h | .s32, .char _, h | .s32, .record _, h
  | .s32, .variant _ _, h => by simp [ValTy.check] at h
  | .u32, .bool _, h | .u32, .s8 _, h | .u32, .u8 _, h | .u32, .s16 _, h
  | .u32, .u16 _, h | .u32, .s32 _, h | .u32, .s64 _, h | .u32, .u64 _, h
  | .u32, .f32 _, h | .u32, .f64 _, h | .u32, .char _, h | .u32, .record _, h
  | .u32, .variant _ _, h => by simp [ValTy.check] at h
  | .s64, .bool _, h | .s64, .s8 _, h | .s64, .u8 _, h | .s64, .s16 _, h
  | .s64, .u16 _, h | .s64, .s32 _, h | .s64, .u32 _, h | .s64, .u64 _, h
  | .s64, .f32 _, h | .s64, .f64 _, h | .s64, .char _, h | .s64, .record _, h
  | .s64, .variant _ _, h => by simp [ValTy.check] at h
  | .u64, .bool _, h | .u64, .s8 _, h | .u64, .u8 _, h | .u64, .s16 _, h
  | .u64, .u16 _, h | .u64, .s32 _, h | .u64, .u32 _, h | .u64, .s64 _, h
  | .u64, .f32 _, h | .u64, .f64 _, h | .u64, .char _, h | .u64, .record _, h
  | .u64, .variant _ _, h => by simp [ValTy.check] at h
  | .f32, .bool _, h | .f32, .s8 _, h | .f32, .u8 _, h | .f32, .s16 _, h
  | .f32, .u16 _, h | .f32, .s32 _, h | .f32, .u32 _, h | .f32, .s64 _, h
  | .f32, .u64 _, h | .f32, .f64 _, h | .f32, .char _, h | .f32, .record _, h
  | .f32, .variant _ _, h => by simp [ValTy.check] at h
  | .f64, .bool _, h | .f64, .s8 _, h | .f64, .u8 _, h | .f64, .s16 _, h
  | .f64, .u16 _, h | .f64, .s32 _, h | .f64, .u32 _, h | .f64, .s64 _, h
  | .f64, .u64 _, h | .f64, .f32 _, h | .f64, .char _, h | .f64, .record _, h
  | .f64, .variant _ _, h => by simp [ValTy.check] at h
  | .char, .bool _, h | .char, .s8 _, h | .char, .u8 _, h | .char, .s16 _, h
  | .char, .u16 _, h | .char, .s32 _, h | .char, .u32 _, h | .char, .s64 _, h
  | .char, .u64 _, h | .char, .f32 _, h | .char, .f64 _, h | .char, .record _, h
  | .char, .variant _ _, h => by simp [ValTy.check] at h
  | .record _, .bool _, h | .record _, .s8 _, h | .record _, .u8 _, h
  | .record _, .s16 _, h | .record _, .u16 _, h | .record _, .s32 _, h
  | .record _, .u32 _, h | .record _, .s64 _, h | .record _, .u64 _, h
  | .record _, .f32 _, h | .record _, .f64 _, h | .record _, .char _, h
  | .record _, .variant _ _, h => by simp [ValTy.check] at h
  | .variant _, .bool _, h | .variant _, .s8 _, h | .variant _, .u8 _, h
  | .variant _, .s16 _, h | .variant _, .u16 _, h | .variant _, .s32 _, h
  | .variant _, .u32 _, h | .variant _, .s64 _, h | .variant _, .u64 _, h
  | .variant _, .f32 _, h | .variant _, .f64 _, h | .variant _, .char _, h
  | .variant _, .record _, h => by simp [ValTy.check] at h

theorem lowerList_types : ∀ (ts : List ValTy) (vs : List Val), ValTy.checkList ts vs = true →
    (ValTy.lowerList ts vs).map (·.type) = ValTy.flatList ts
  | [], [], _ => rfl
  | t :: ts, v :: vs, h => by
    simp only [ValTy.checkList, Bool.and_eq_true] at h
    simp only [ValTy.lowerList, ValTy.flatList, List.map_append, lower_types t v h.1,
      lowerList_types ts vs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [ValTy.checkList] at h

theorem lowerOpt_types : ∀ (c : Option ValTy) (p : Option Val), ValTy.checkOpt c p = true →
    (ValTy.lowerOpt c p).map (·.type) = ValTy.flatOpt c
  | none, none, _ => rfl
  | some t, some v, h => by
    simp only [ValTy.checkOpt] at h
    simp only [ValTy.lowerOpt, ValTy.flatOpt, lower_types t v h]
  | none, some _, h | some _, none, h => by simp [ValTy.checkOpt] at h
end

/-! ## The round trip -/

mutual
/-- **Canonical ABI round trip**: lifting the lowering of a well-typed value
gives the value back, leaving the rest of the flat values untouched. -/
theorem lift_lower : ∀ (t : ValTy) (v : Val), t.check v = true → ∀ r : List Flat,
    t.lift (t.lower v ++ r) = some (v, r)
  | .bool, .bool b, _, r => by cases b <;> rfl
  | .s8, .s8 x, _, r => by
    simp [ValTy.lower, ValTy.lift]; exact truncate_signExtend (by decide) x
  | .u8, .u8 x, _, r => by
    simp [ValTy.lower, ValTy.lift]; exact truncate_zeroExtend (by decide) x
  | .s16, .s16 x, _, r => by
    simp [ValTy.lower, ValTy.lift]; exact truncate_signExtend (by decide) x
  | .u16, .u16 x, _, r => by
    simp [ValTy.lower, ValTy.lift]; exact truncate_zeroExtend (by decide) x
  | .s32, .s32 _, _, _ | .u32, .u32 _, _, _ | .s64, .s64 _, _, _ | .u64, .u64 _, _, _
  | .f32, .f32 _, _, _ | .f64, .f64 _, _, _ => rfl
  | .char, .char c, _, r => by
    simp [ValTy.lower, ValTy.lift, charOfBits_val]
  | .record ts, .record vs, h, r => by
    simp only [ValTy.check] at h
    simp [ValTy.lower, ValTy.lift, liftList_lowerList ts vs h r]
  | .variant cs, .variant i p, h, r => by
    simp only [ValTy.check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [ValTy.lower, ValTy.lift, List.cons_append,
      take_append r (fit_types (ValTy.flatCases cs) (ValTy.lowerCase cs i p))]
    rw [toNat_ofNat_i32 h.1, liftCase_fit cs i p h.2 _ (Dom.refl _), Option.map_some]
  | .bool, .s8 _, h, _ | .bool, .u8 _, h, _ | .bool, .s16 _, h, _ | .bool, .u16 _, h, _
  | .bool, .s32 _, h, _ | .bool, .u32 _, h, _ | .bool, .s64 _, h, _ | .bool, .u64 _, h, _
  | .bool, .f32 _, h, _ | .bool, .f64 _, h, _ | .bool, .char _, h, _ | .bool, .record _, h, _
  | .bool, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .s8, .bool _, h, _ | .s8, .u8 _, h, _ | .s8, .s16 _, h, _ | .s8, .u16 _, h, _
  | .s8, .s32 _, h, _ | .s8, .u32 _, h, _ | .s8, .s64 _, h, _ | .s8, .u64 _, h, _
  | .s8, .f32 _, h, _ | .s8, .f64 _, h, _ | .s8, .char _, h, _ | .s8, .record _, h, _
  | .s8, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .u8, .bool _, h, _ | .u8, .s8 _, h, _ | .u8, .s16 _, h, _ | .u8, .u16 _, h, _
  | .u8, .s32 _, h, _ | .u8, .u32 _, h, _ | .u8, .s64 _, h, _ | .u8, .u64 _, h, _
  | .u8, .f32 _, h, _ | .u8, .f64 _, h, _ | .u8, .char _, h, _ | .u8, .record _, h, _
  | .u8, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .s16, .bool _, h, _ | .s16, .s8 _, h, _ | .s16, .u8 _, h, _ | .s16, .u16 _, h, _
  | .s16, .s32 _, h, _ | .s16, .u32 _, h, _ | .s16, .s64 _, h, _ | .s16, .u64 _, h, _
  | .s16, .f32 _, h, _ | .s16, .f64 _, h, _ | .s16, .char _, h, _ | .s16, .record _, h, _
  | .s16, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .u16, .bool _, h, _ | .u16, .s8 _, h, _ | .u16, .u8 _, h, _ | .u16, .s16 _, h, _
  | .u16, .s32 _, h, _ | .u16, .u32 _, h, _ | .u16, .s64 _, h, _ | .u16, .u64 _, h, _
  | .u16, .f32 _, h, _ | .u16, .f64 _, h, _ | .u16, .char _, h, _ | .u16, .record _, h, _
  | .u16, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .s32, .bool _, h, _ | .s32, .s8 _, h, _ | .s32, .u8 _, h, _ | .s32, .s16 _, h, _
  | .s32, .u16 _, h, _ | .s32, .u32 _, h, _ | .s32, .s64 _, h, _ | .s32, .u64 _, h, _
  | .s32, .f32 _, h, _ | .s32, .f64 _, h, _ | .s32, .char _, h, _ | .s32, .record _, h, _
  | .s32, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .u32, .bool _, h, _ | .u32, .s8 _, h, _ | .u32, .u8 _, h, _ | .u32, .s16 _, h, _
  | .u32, .u16 _, h, _ | .u32, .s32 _, h, _ | .u32, .s64 _, h, _ | .u32, .u64 _, h, _
  | .u32, .f32 _, h, _ | .u32, .f64 _, h, _ | .u32, .char _, h, _ | .u32, .record _, h, _
  | .u32, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .s64, .bool _, h, _ | .s64, .s8 _, h, _ | .s64, .u8 _, h, _ | .s64, .s16 _, h, _
  | .s64, .u16 _, h, _ | .s64, .s32 _, h, _ | .s64, .u32 _, h, _ | .s64, .u64 _, h, _
  | .s64, .f32 _, h, _ | .s64, .f64 _, h, _ | .s64, .char _, h, _ | .s64, .record _, h, _
  | .s64, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .u64, .bool _, h, _ | .u64, .s8 _, h, _ | .u64, .u8 _, h, _ | .u64, .s16 _, h, _
  | .u64, .u16 _, h, _ | .u64, .s32 _, h, _ | .u64, .u32 _, h, _ | .u64, .s64 _, h, _
  | .u64, .f32 _, h, _ | .u64, .f64 _, h, _ | .u64, .char _, h, _ | .u64, .record _, h, _
  | .u64, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .f32, .bool _, h, _ | .f32, .s8 _, h, _ | .f32, .u8 _, h, _ | .f32, .s16 _, h, _
  | .f32, .u16 _, h, _ | .f32, .s32 _, h, _ | .f32, .u32 _, h, _ | .f32, .s64 _, h, _
  | .f32, .u64 _, h, _ | .f32, .f64 _, h, _ | .f32, .char _, h, _ | .f32, .record _, h, _
  | .f32, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .f64, .bool _, h, _ | .f64, .s8 _, h, _ | .f64, .u8 _, h, _ | .f64, .s16 _, h, _
  | .f64, .u16 _, h, _ | .f64, .s32 _, h, _ | .f64, .u32 _, h, _ | .f64, .s64 _, h, _
  | .f64, .u64 _, h, _ | .f64, .f32 _, h, _ | .f64, .char _, h, _ | .f64, .record _, h, _
  | .f64, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .char, .bool _, h, _ | .char, .s8 _, h, _ | .char, .u8 _, h, _ | .char, .s16 _, h, _
  | .char, .u16 _, h, _ | .char, .s32 _, h, _ | .char, .u32 _, h, _ | .char, .s64 _, h, _
  | .char, .u64 _, h, _ | .char, .f32 _, h, _ | .char, .f64 _, h, _ | .char, .record _, h, _
  | .char, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .record _, .bool _, h, _ | .record _, .s8 _, h, _ | .record _, .u8 _, h, _
  | .record _, .s16 _, h, _ | .record _, .u16 _, h, _ | .record _, .s32 _, h, _
  | .record _, .u32 _, h, _ | .record _, .s64 _, h, _ | .record _, .u64 _, h, _
  | .record _, .f32 _, h, _ | .record _, .f64 _, h, _ | .record _, .char _, h, _
  | .record _, .variant _ _, h, _ => by simp [ValTy.check] at h
  | .variant _, .bool _, h, _ | .variant _, .s8 _, h, _ | .variant _, .u8 _, h, _
  | .variant _, .s16 _, h, _ | .variant _, .u16 _, h, _ | .variant _, .s32 _, h, _
  | .variant _, .u32 _, h, _ | .variant _, .s64 _, h, _ | .variant _, .u64 _, h, _
  | .variant _, .f32 _, h, _ | .variant _, .f64 _, h, _ | .variant _, .char _, h, _
  | .variant _, .record _, h, _ => by simp [ValTy.check] at h

theorem liftList_lowerList : ∀ (ts : List ValTy) (vs : List Val),
    ValTy.checkList ts vs = true → ∀ r : List Flat,
    ValTy.liftList ts (ValTy.lowerList ts vs ++ r) = some (vs, r)
  | [], [], _, _ => rfl
  | t :: ts, v :: vs, h, r => by
    simp only [ValTy.checkList, Bool.and_eq_true] at h
    simp only [ValTy.lowerList, ValTy.liftList, List.append_assoc,
      lift_lower t v h.1 _, liftList_lowerList ts vs h.2 r, Option.map_some]
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp [ValTy.checkList] at h

theorem liftOpt_lowerOpt : ∀ (c : Option ValTy) (p : Option Val),
    ValTy.checkOpt c p = true → ValTy.liftOpt c (ValTy.lowerOpt c p) = some p
  | none, none, _ => rfl
  | some t, some v, h => by
    simp only [ValTy.checkOpt] at h
    have := lift_lower t v h []
    simp only [List.append_nil] at this
    simp [ValTy.lowerOpt, ValTy.liftOpt, this]
  | none, some _, h | some _, none, h => by simp [ValTy.checkOpt] at h

theorem liftCase_fit : ∀ (cs : List (Option ValTy)) (i : Nat) (p : Option Val),
    ValTy.checkCase cs i p = true → ∀ J : List NumType, Dom (ValTy.flatCases cs) J →
    ValTy.liftCase cs i (Flat.fit J (ValTy.lowerCase cs i p)) = some p
  | [], _, _, h, _, _ => by simp [ValTy.checkCase] at h
  | c :: cs, 0, p, h, J, hJ => by
    simp only [ValTy.checkCase] at h
    simp only [ValTy.lowerCase, ValTy.liftCase,
      unfit_fit (lowerOpt_types c p h) ((Dom.flatCases_head c cs).trans hJ),
      liftOpt_lowerOpt c p h]
  | c :: cs, i + 1, p, h, J, hJ => by
    simp only [ValTy.checkCase] at h
    simp only [ValTy.lowerCase, ValTy.liftCase]
    exact liftCase_fit cs i p h J ((Dom.flatCases_tail c cs).trans hJ)
end

/-! ## Lifted values are well typed -/

mutual
theorem check_of_lift : ∀ (t : ValTy) (xs : List Flat) (v : Val) (r : List Flat),
    t.lift xs = some (v, r) → t.check v = true
  | .record ts, xs, v, r, h => by
    simp only [ValTy.lift] at h
    cases e : ValTy.liftList ts xs with
    | none => simp [e] at h
    | some q =>
      simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact checkList_of_liftList ts xs q.1 q.2 e
  | .variant cs, xs, v, r, h => by
    match xs, h with
    | ⟨.int .i32, d⟩ :: xs, h =>
      simp only [ValTy.lift] at h
      split at h
      · simp at h
      · rename_i js r' _
        cases e : ValTy.liftCase cs d.toNat js with
        | none => simp [e] at h
        | some q =>
          simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [ValTy.check, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨d.isLt, checkCase_of_liftCase cs d.toNat js q e⟩
    | [], h | ⟨.int .i64, _⟩ :: _, h | ⟨.float _, _⟩ :: _, h => simp [ValTy.lift] at h
  | .bool, xs, v, r, h | .s8, xs, v, r, h | .u8, xs, v, r, h | .s16, xs, v, r, h
  | .u16, xs, v, r, h | .s32, xs, v, r, h | .u32, xs, v, r, h | .s64, xs, v, r, h
  | .u64, xs, v, r, h | .f32, xs, v, r, h | .f64, xs, v, r, h | .char, xs, v, r, h => by
    match xs with
    | [] => simp [ValTy.lift] at h
    | ⟨.int .i32, x⟩ :: xs | ⟨.int .i64, x⟩ :: xs | ⟨.float .f32, x⟩ :: xs
    | ⟨.float .f64, x⟩ :: xs =>
      simp only [ValTy.lift, Option.some.injEq, Prod.mk.injEq, reduceCtorEq,
        Option.map_eq_some_iff] at h ; all_goals
      first
        | (obtain ⟨rfl, rfl⟩ := h; rfl)
        | (obtain ⟨c, -, rfl, rfl⟩ := h; rfl)

theorem checkList_of_liftList : ∀ (ts : List ValTy) (xs : List Flat) (vs : List Val)
    (r : List Flat), ValTy.liftList ts xs = some (vs, r) → ValTy.checkList ts vs = true
  | [], xs, vs, r, h => by
    simp only [ValTy.liftList, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | t :: ts, xs, vs, r, h => by
    simp only [ValTy.liftList] at h
    split at h
    · simp at h
    · rename_i v r' e
      cases e' : ValTy.liftList ts r' with
      | none => simp [e'] at h
      | some q =>
        simp only [e', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [ValTy.checkList, Bool.and_eq_true]
        exact ⟨check_of_lift t xs v r' e, checkList_of_liftList ts r' q.1 q.2 e'⟩

theorem checkOpt_of_liftOpt : ∀ (c : Option ValTy) (xs : List Flat) (p : Option Val),
    ValTy.liftOpt c xs = some p → ValTy.checkOpt c p = true
  | none, xs, p, h => by
    simp only [ValTy.liftOpt, Option.some.injEq] at h
    subst h; rfl
  | some t, xs, p, h => by
    simp only [ValTy.liftOpt] at h
    split at h
    · rename_i v e
      simp only [Option.some.injEq] at h
      subst h
      exact check_of_lift t xs v [] e
    · simp at h

theorem checkCase_of_liftCase : ∀ (cs : List (Option ValTy)) (i : Nat) (js : List Flat)
    (p : Option Val), ValTy.liftCase cs i js = some p → ValTy.checkCase cs i p = true
  | [], _, _, _, h => by simp [ValTy.liftCase] at h
  | c :: cs, 0, js, p, h => by
    simp only [ValTy.liftCase] at h
    exact checkOpt_of_liftOpt c _ p h
  | c :: cs, i + 1, js, p, h => by
    simp only [ValTy.liftCase] at h
    exact checkCase_of_liftCase cs i js p h
end

/-! ## Argument lists -/

theorem liftArgs_lowerArgs {ts : List ValTy} {vs : List Val} (h : ValTy.checkList ts vs = true) :
    liftArgs ts (lowerArgs ts vs) = some vs := by
  have := liftList_lowerList ts vs h []
  simp only [List.append_nil] at this
  simp [liftArgs, lowerArgs, this]

theorem checkList_of_liftArgs {ts : List ValTy} {xs : List Flat} {vs : List Val}
    (h : liftArgs ts xs = some vs) : ValTy.checkList ts vs = true := by
  unfold liftArgs at h
  split at h
  · rename_i vs' e
    simp only [Option.some.injEq] at h
    subst h
    exact checkList_of_liftList ts xs vs' [] e
  · simp at h

/-! ## Trivially represented types -/

mutual
theorem lift_trivial : ∀ (t : ValTy), t.trivial = true → ∀ (xs : List Flat) (v : Val)
    (r : List Flat), t.lift xs = some (v, r) → xs = t.lower v ++ r
  | .s32, _, xs, v, r, h | .u32, _, xs, v, r, h | .s64, _, xs, v, r, h
  | .u64, _, xs, v, r, h | .f32, _, xs, v, r, h | .f64, _, xs, v, r, h => by
    match xs with
    | [] => simp [ValTy.lift] at h
    | ⟨.int .i32, x⟩ :: xs | ⟨.int .i64, x⟩ :: xs | ⟨.float .f32, x⟩ :: xs
    | ⟨.float .f64, x⟩ :: xs =>
      simp only [ValTy.lift, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h ; all_goals
      (obtain ⟨rfl, rfl⟩ := h; rfl)
  | .record ts, ht, xs, v, r, h => by
    simp only [ValTy.trivial] at ht
    simp only [ValTy.lift] at h
    cases e : ValTy.liftList ts xs with
    | none => simp [e] at h
    | some q =>
      simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact liftList_trivial ts ht xs q.1 q.2 e
  | .bool, ht, _, _, _, _ | .s8, ht, _, _, _, _ | .u8, ht, _, _, _, _
  | .s16, ht, _, _, _, _ | .u16, ht, _, _, _, _ | .char, ht, _, _, _, _
  | .variant _, ht, _, _, _, _ => by simp [ValTy.trivial] at ht

theorem liftList_trivial : ∀ (ts : List ValTy), ValTy.trivialList ts = true →
    ∀ (xs : List Flat) (vs : List Val) (r : List Flat),
    ValTy.liftList ts xs = some (vs, r) → xs = ValTy.lowerList ts vs ++ r
  | [], _, xs, vs, r, h => by
    simp only [ValTy.liftList, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | t :: ts, ht, xs, vs, r, h => by
    simp only [ValTy.trivialList, Bool.and_eq_true] at ht
    simp only [ValTy.liftList] at h
    split at h
    · simp at h
    · rename_i v r' e
      cases e' : ValTy.liftList ts r' with
      | none => simp [e'] at h
      | some q =>
        simp only [e', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [lift_trivial t ht.1 xs v r' e, liftList_trivial ts ht.2 r' q.1 q.2 e']
        simp [ValTy.lowerList]
end

mutual
theorem lift_of_types_trivial : ∀ (t : ValTy), t.trivial = true → ∀ ys : List Flat,
    ys.map (·.type) = t.flat → ∃ v, t.check v = true ∧ t.lower v = ys
  | .s32, _, [⟨.int .i32, x⟩], _ => ⟨.s32 x, rfl, rfl⟩
  | .u32, _, [⟨.int .i32, x⟩], _ => ⟨.u32 x, rfl, rfl⟩
  | .s64, _, [⟨.int .i64, x⟩], _ => ⟨.s64 x, rfl, rfl⟩
  | .u64, _, [⟨.int .i64, x⟩], _ => ⟨.u64 x, rfl, rfl⟩
  | .f32, _, [⟨.float .f32, x⟩], _ => ⟨.f32 x, rfl, rfl⟩
  | .f64, _, [⟨.float .f64, x⟩], _ => ⟨.f64 x, rfl, rfl⟩
  | .record ts, ht, ys, hy => by
    obtain ⟨vs, hvs, rfl⟩ := liftList_of_types_trivial ts ht ys hy
    exact ⟨.record vs, hvs, rfl⟩
  | .s32, _, [], h | .u32, _, [], h | .s64, _, [], h | .u64, _, [], h
  | .f32, _, [], h | .f64, _, [], h => by simp [ValTy.flat] at h
  | .s32, _, _ :: _ :: _, h | .u32, _, _ :: _ :: _, h | .s64, _, _ :: _ :: _, h
  | .u64, _, _ :: _ :: _, h | .f32, _, _ :: _ :: _, h | .f64, _, _ :: _ :: _, h => by
    simp [ValTy.flat] at h
  | .s32, _, [⟨.int .i64, _⟩], h | .s32, _, [⟨.float _, _⟩], h
  | .u32, _, [⟨.int .i64, _⟩], h | .u32, _, [⟨.float _, _⟩], h
  | .s64, _, [⟨.int .i32, _⟩], h | .s64, _, [⟨.float _, _⟩], h
  | .u64, _, [⟨.int .i32, _⟩], h | .u64, _, [⟨.float _, _⟩], h
  | .f32, _, [⟨.int _, _⟩], h | .f32, _, [⟨.float .f64, _⟩], h
  | .f64, _, [⟨.int _, _⟩], h | .f64, _, [⟨.float .f32, _⟩], h => by simp [ValTy.flat] at h
  | .bool, ht, _, _ | .s8, ht, _, _ | .u8, ht, _, _ | .s16, ht, _, _ | .u16, ht, _, _
  | .char, ht, _, _ | .variant _, ht, _, _ => by simp [ValTy.trivial] at ht

/-- Trivially represented types: every flat list of the right types lifts. -/
theorem liftList_of_types_trivial : ∀ (ts : List ValTy), ValTy.trivialList ts = true →
    ∀ xs : List Flat, xs.map (·.type) = ValTy.flatList ts →
    ∃ vs, ValTy.checkList ts vs = true ∧ ValTy.lowerList ts vs = xs
  | [], _, [], _ => ⟨[], rfl, rfl⟩
  | [], _, _ :: _, h => by simp [ValTy.flatList] at h
  | t :: ts, ht, xs, hx => by
    simp only [ValTy.trivialList, Bool.and_eq_true] at ht
    obtain ⟨ht, hts⟩ := ht
    simp only [ValTy.flatList] at hx
    obtain ⟨ys, zs, rfl, hy, hz⟩ : ∃ ys zs, xs = ys ++ zs ∧ ys.map (·.type) = t.flat ∧
        zs.map (·.type) = ValTy.flatList ts := by
      refine ⟨xs.take t.flat.length, xs.drop t.flat.length, (List.take_append_drop _ _).symm,
        ?_, ?_⟩
      · rw [List.map_take, hx, List.take_left' rfl]
      · rw [List.map_drop, hx, List.drop_left' rfl]
    obtain ⟨vs, hvs, rfl⟩ := liftList_of_types_trivial ts hts zs hz
    obtain ⟨v, hv, rfl⟩ := lift_of_types_trivial t ht ys hy
    exact ⟨v :: vs, by simp [ValTy.checkList, hv, hvs], rfl⟩
end

/-- For trivially represented types the canonicalisation is a type check. -/
theorem canonFlat_trivial {ts : List ValTy} (ht : ValTy.trivialList ts = true) (xs : List Flat) :
    canonFlat ts xs = checkFlat (ValTy.flatList ts) xs := by
  unfold canonFlat checkFlat
  split_ifs with hx
  · obtain ⟨vs, hvs, rfl⟩ := liftList_of_types_trivial ts ht xs hx
    rw [show ValTy.lowerList ts vs = lowerArgs ts vs from rfl, liftArgs_lowerArgs hvs]
    rfl
  · cases e : liftArgs ts xs with
    | none => rfl
    | some vs =>
      exfalso
      apply hx
      have hvs := checkList_of_liftArgs e
      unfold liftArgs at e
      split at e
      · rename_i vs' e'
        simp only [Option.some.injEq] at e
        subst e
        rw [liftList_trivial ts ht xs vs' [] e', List.append_nil]
        exact lowerList_types ts vs' hvs
      · simp at e
