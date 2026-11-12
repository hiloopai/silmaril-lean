module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Raw.Wasm.Component.Canon.Flat
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The flat canonical ABI of the reference machine on IR types

`toClosed t` is the resolved reference type of the IR type `t` as instantiation of
`Simple.toRef` produces it (records with labels `f, fx, …`, variants with labels `c, cx, …`).
This module relates the reference flat ABI (`Canon/Flat.lean`) on these types to the IR's:

* `flatten_toClosed`: the reference flattening is the IR's `ValTy.flat`;
* `lowerFlatAt_toClosed`: for a float-free type and a well-typed value, the reference
  `lower_flat` program is `pure` of the IR lowering `ValTy.lower` (no effect at all: floats,
  whose lowering may choose a NaN, are excluded).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Runtime (RtId)

/-! ## Resolved types -/

export Silmaril.Wasm.Component.Reference (toClosed toClosedList toClosedCases)

theorem mapIdx_pair_snd {α : Type} (xs : List α) :
    ∀ f : Nat → String, (xs.mapIdx fun i x => (f i, x)).map Prod.snd = xs := by
  induction xs with
  | nil => intro f; rfl
  | cons x xs ih =>
    intro f
    simp only [List.mapIdx_cons, List.map_cons, ih (fun i => f (i + 1))]

theorem labels_map_snd {α : Type} (p : String) (xs : List α) : (labels p xs).map Prod.snd = xs :=
  mapIdx_pair_snd xs (tag p)

/-! ## Flattening -/

theorem joinType_eq (a b : Silmaril.Wasm.NumType) :
    Silmaril.Wasm.Component.joinType a b = Silmaril.Wasm.Component.ABI.joinType a b := by
  rcases a with (a | a) <;> cases a <;> rcases b with (b | b) <;> cases b <;> rfl

theorem joinFlat_eq (xs ys : List Silmaril.Wasm.NumType) :
    Silmaril.Wasm.Component.joinFlat xs ys = Silmaril.Wasm.Component.ABI.joinFlat xs ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys => simp only [Silmaril.Wasm.Component.joinFlat, ABI.joinFlat, joinType_eq, ih]

mutual
theorem flatten_toClosed (p : Silmaril.Wasm.AddrType) :
    ∀ t : ValTy, flatten p (toClosed t) = t.flat
  | .bool | .s8 | .u8 | .s16 | .u16 | .s32 | .u32 | .s64 | .u64 | .f32 | .f64 | .char => by
    first | (simp only [toClosed, flatten, flattenPrimitive, ValTy.flat])
  | .record ts => by
    simp only [toClosed, flatten, ValTy.flat]
    exact flattenFields_toClosed p ts _ (labels_map_snd "f" _)
  | .variant cs => by
    simp only [toClosed, flatten, ValTy.flat]
    rw [flattenCases_toClosed p cs _ (labels_map_snd "c" _)]

theorem flattenFields_toClosed (p : Silmaril.Wasm.AddrType) :
    ∀ (ts : List ValTy) (fs : List (String × WIT.ClosedType RtId)),
      fs.map Prod.snd = toClosedList ts → flattenFields p fs = ValTy.flatList ts
  | [], [], _ => by simp only [flattenFields, ValTy.flatList]
  | [], _ :: _, h => by simp [toClosedList] at h
  | _ :: _, [], h => by simp [toClosedList] at h
  | t :: ts, (n, u) :: fs, h => by
    simp only [List.map_cons, toClosedList, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [flattenFields, ValTy.flatList, flatten_toClosed p t,
      flattenFields_toClosed p ts fs h]

theorem flattenCases_toClosed (p : Silmaril.Wasm.AddrType) :
    ∀ (cs : List (Option ValTy)) (fs : List (String × Option (WIT.ClosedType RtId))),
      fs.map Prod.snd = toClosedCases cs →
        variantPayload (flattenCases p fs) = ValTy.flatCases cs
  | [], [], _ => by simp only [flattenCases, variantPayload, ValTy.flatCases]
  | [], _ :: _, h => by simp [toClosedCases] at h
  | none :: _, [], h => by simp [toClosedCases] at h
  | some _ :: _, [], h => by simp [toClosedCases] at h
  | none :: cs, (n, u) :: fs, h => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [flattenCases, variantPayload, flattenOption, ValTy.flatCases, ValTy.flatOpt,
      flattenCases_toClosed p cs fs h, ← joinFlat_eq]
  | some t :: cs, (n, u) :: fs, h => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [flattenCases, variantPayload, flattenOption, ValTy.flatCases, ValTy.flatOpt,
      flattenCases_toClosed p cs fs h, flatten_toClosed p t, ← joinFlat_eq]
end

/-! ## Integer flat types -/

/-- Integer core types only. -/
def IntFlat (ts : List Silmaril.Wasm.NumType) : Prop := ∀ x ∈ ts, x = .int .i32 ∨ x = .int .i64

/-- Each slot of `hs` fits the slot of `ws` at the same position: equal, or `i32` widened to
`i64`; `ws` is at least as long. -/
def Dom : List Silmaril.Wasm.NumType → List Silmaril.Wasm.NumType → Prop
  | [], _ => True
  | _ :: _, [] => False
  | h :: hs, w :: ws => (h = w ∨ (h = .int .i32 ∧ w = .int .i64)) ∧ Dom hs ws

theorem Dom.refl : ∀ hs : List Silmaril.Wasm.NumType, Dom hs hs
  | [] => trivial
  | _ :: hs => ⟨.inl rfl, Dom.refl hs⟩

theorem Dom.trans : ∀ {a b c : List Silmaril.Wasm.NumType}, Dom a b → Dom b c → Dom a c
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim
  | x :: a, y :: b, z :: c, ⟨hxy, hab⟩, ⟨hyz, hbc⟩ => by
    refine ⟨?_, Dom.trans hab hbc⟩
    rcases hxy with rfl | ⟨rfl, rfl⟩ <;> rcases hyz with rfl | ⟨h₁, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨h₁, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
    · cases h₁

theorem intFlat_append {a b : List Silmaril.Wasm.NumType} (ha : IntFlat a) (hb : IntFlat b) :
    IntFlat (a ++ b) := fun x hx => (List.mem_append.mp hx).elim (ha x) (hb x)

theorem joinType_int {x y : Silmaril.Wasm.NumType} (hx : x = .int .i32 ∨ x = .int .i64)
    (hy : y = .int .i32 ∨ y = .int .i64) :
    (Silmaril.Wasm.Component.joinType x y = .int .i32 ∨ Silmaril.Wasm.Component.joinType x y = .int .i64) ∧
      (x = Silmaril.Wasm.Component.joinType x y ∨
        (x = .int .i32 ∧ Silmaril.Wasm.Component.joinType x y = .int .i64)) ∧
      (y = Silmaril.Wasm.Component.joinType x y ∨
        (y = .int .i32 ∧ Silmaril.Wasm.Component.joinType x y = .int .i64)) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

theorem joinFlat_int : ∀ {a b : List Silmaril.Wasm.NumType}, IntFlat a → IntFlat b →
    IntFlat (Silmaril.Wasm.Component.joinFlat a b) ∧ Dom a (Silmaril.Wasm.Component.joinFlat a b) ∧
      Dom b (Silmaril.Wasm.Component.joinFlat a b)
  | [], b, _, hb => ⟨hb, trivial, Dom.refl b⟩
  | x :: a, [], ha, _ => ⟨ha, Dom.refl _, trivial⟩
  | x :: a, y :: b, ha, hb => by
    have hx := ha x List.mem_cons_self
    have hy := hb y List.mem_cons_self
    obtain ⟨hi, hd₁, hd₂⟩ := joinFlat_int (a := a) (b := b)
      (fun z hz => ha z (List.mem_cons_of_mem _ hz)) (fun z hz => hb z (List.mem_cons_of_mem _ hz))
    obtain ⟨hj, hjx, hjy⟩ := joinType_int hx hy
    refine ⟨?_, ⟨hjx, hd₁⟩, ⟨hjy, hd₂⟩⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hj
    · exact hi z hz

mutual
theorem flat_int : ∀ t : ValTy, floatFree t = true → IntFlat t.flat
  | .bool, _ | .s8, _ | .u8, _ | .s16, _ | .u16, _ | .s32, _ | .u32, _ | .char, _ => by
    intro x hx; simp only [ValTy.flat, List.mem_singleton] at hx; exact .inl hx
  | .s64, _ | .u64, _ => by
    intro x hx; simp only [ValTy.flat, List.mem_singleton] at hx; exact .inr hx
  | .f32, h | .f64, h => by simp [floatFree] at h
  | .record ts, h => by
    simp only [ValTy.flat]
    exact flatList_int ts (by simpa only [floatFree] using h)
  | .variant cs, h => by
    have hc := flatCases_int cs (by simpa only [floatFree] using h)
    intro x hx
    simp only [ValTy.flat, List.mem_cons] at hx
    exact hx.elim .inl (hc x)

theorem flatList_int : ∀ ts : List ValTy, floatFreeList ts = true → IntFlat (ValTy.flatList ts)
  | [], _ => fun _ hx => by simp [ValTy.flatList] at hx
  | t :: ts, h => by
    simp only [floatFreeList, Bool.and_eq_true] at h
    simp only [ValTy.flatList]
    exact intFlat_append (flat_int t h.1) (flatList_int ts h.2)

theorem flatCases_int : ∀ cs : List (Option ValTy), floatFreeCases cs = true →
    IntFlat (ValTy.flatCases cs)
  | [], _ => fun _ hx => by simp [ValTy.flatCases] at hx
  | none :: cs, h => by
    simp only [floatFreeCases] at h
    simp only [ValTy.flatCases, ValTy.flatOpt]
    exact (joinFlat_int (fun _ hx => by simp at hx) (flatCases_int cs h)).1
  | some t :: cs, h => by
    simp only [floatFreeCases, Bool.and_eq_true] at h
    simp only [ValTy.flatCases, ValTy.flatOpt]
    exact (joinFlat_int (flat_int t h.1) (flatCases_int cs h.2)).1
end

/-! ## Payload slots of variants -/

theorem dom_case : ∀ (cs : List (Option ValTy)) (i : Nat) (c : Option ValTy),
    floatFreeCases cs = true → cs[i]? = some c → Dom (ValTy.flatOpt c) (ValTy.flatCases cs)
  | [], _, _, _, h => by simp at h
  | none :: cs, 0, c, hf, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    trivial
  | some t :: cs, 0, c, hf, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [floatFreeCases, Bool.and_eq_true] at hf
    exact (joinFlat_int (flat_int t hf.1) (flatCases_int cs hf.2)).2.1
  | none :: cs, i + 1, c, hf, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [floatFreeCases] at hf
    exact (dom_case cs i c hf h).trans
      (joinFlat_int (a := []) (fun _ hx => by simp at hx) (flatCases_int cs hf)).2.2
  | some t :: cs, i + 1, c, hf, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [floatFreeCases, Bool.and_eq_true] at hf
    exact (dom_case cs i c hf.2 h).trans
      (joinFlat_int (flat_int t hf.1) (flatCases_int cs hf.2)).2.2

theorem Dom.int : ∀ {hs ws : List Silmaril.Wasm.NumType}, Dom hs ws → IntFlat ws → IntFlat hs
  | [], _, _, _ => fun _ hx => by simp at hx
  | _ :: _, [], h, _ => h.elim
  | h :: hs, w :: ws, ⟨hhw, hd⟩, hw => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rcases hhw with rfl | ⟨rfl, -⟩
      · exact hw x List.mem_cons_self
      · exact .inl rfl
    · exact Dom.int hd (fun y hy => hw y (List.mem_cons_of_mem _ hy)) x hx

theorem fit_nil : ∀ ws : List Silmaril.Wasm.NumType,
    Flat.fit ws [] = ws.map Silmaril.Wasm.Execution.Runtime.Value.zero
  | [] => rfl
  | w :: ws => by simp only [Flat.fit, List.map_cons, fit_nil ws]

theorem retype_self (v : Flat) : Flat.retype v.type v = v := by
  obtain ⟨t, b⟩ := v
  simp only [Flat.retype, BitVec.setWidth_eq]

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {σ : Type}

/-- The coercion of one lowered payload slot is the IR's re-typing. -/
theorem coerceLower_eq {h w : Silmaril.Wasm.NumType} {v : Flat} (hv : v.type = h)
    (hd : h = w ∨ (h = .int .i32 ∧ w = .int .i64)) (hi : h = .int .i32 ∨ h = .int .i64) :
    (coerceLower h w v : P E σ Flat) = pure (Flat.retype w v) := by
  obtain ⟨t, b⟩ := v
  simp only at hv
  subst hv
  rcases hd with rfl | ⟨rfl, rfl⟩
  · rcases hi with rfl | rfl
    · simp only [coerceLower, Flat.retype, BitVec.setWidth_eq]
    · simp only [coerceLower, Flat.retype, BitVec.setWidth_eq]
  · simp only [coerceLower, Flat.retype, flatBits64, BitVec.ofNat_toNat]
    rfl

/-- The `(have, want)` loop of `lower_flat_variant` followed by zero padding is the IR's
`Flat.fit`. -/
theorem coerceLowerSlots_eq : ∀ (hs ws : List Silmaril.Wasm.NumType) (fl : List Flat),
    fl.map (·.type) = hs → IntFlat hs → Dom hs ws →
      ((do
        let (coerced, rest) ← coerceLowerSlots hs ws fl
        pure (coerced ++ rest.map Silmaril.Wasm.Execution.Runtime.Value.zero)) : P E σ _) =
        pure (Flat.fit ws fl)
  | [], ws, fl, hfl, _, _ => by
    have h0 : fl = [] := List.map_eq_nil_iff.mp hfl
    subst h0
    cases ws <;> simp only [coerceLowerSlots, pure_bind, List.nil_append, fit_nil]
  | _ :: _, [], _, _, _, hd => hd.elim
  | h :: hs, w :: ws, [], hfl, _, _ => by simp at hfl
  | h :: hs, w :: ws, v :: fl, hfl, hi, ⟨hhw, hd⟩ => by
    simp only [List.map_cons, List.cons.injEq] at hfl
    have hc := coerceLower_eq (E := E) (σ := σ) hfl.1 hhw (hi h List.mem_cons_self)
    have ih := coerceLowerSlots_eq hs ws fl hfl.2 (fun x hx => hi x (List.mem_cons_of_mem _ hx)) hd
    simp only [coerceLowerSlots, hc, pure_bind, bind_assoc, Flat.fit] at ih ⊢
    calc _ = (List.cons (Flat.retype w v)) <$> (do
            let x ← coerceLowerSlots hs ws fl
            pure (x.1 ++ x.2.map Silmaril.Wasm.Execution.Runtime.Value.zero) : P E σ _) := by
          simp only [map_eq_pure_bind, bind_assoc, pure_bind, List.cons_append]
      _ = _ := by rw [ih]; rfl

/-! ## Types of lowered values -/

theorem fit_types : ∀ (ws : List Silmaril.Wasm.NumType) (vs : List Flat),
    (Flat.fit ws vs).map (·.type) = ws
  | [], _ => rfl
  | w :: ws, [] => by simp only [Flat.fit, List.map_cons, fit_types ws []]; rfl
  | w :: ws, v :: vs => by simp only [Flat.fit, List.map_cons, fit_types ws vs]; rfl

mutual
theorem refLower_types : ∀ (t : ValTy) (v : Silmaril.Wasm.Component.Val), t.check v = true →
    (t.lower v).map (·.type) = t.flat
  | t, v, h => by
    cases t <;> cases v <;>
      first
        | rfl
        | (simp only [ValTy.lower, ValTy.flat]
           exact refLowerList_types _ _ (by simpa only [ValTy.check] using h))
        | (simp only [ValTy.lower, ValTy.flat, List.map_cons, fit_types]; done)
        | (simp only [ValTy.check, Bool.false_eq_true] at h)

theorem refLowerList_types : ∀ (ts : List ValTy) (vs : List Silmaril.Wasm.Component.Val),
    ValTy.checkList ts vs = true → (ValTy.lowerList ts vs).map (·.type) = ValTy.flatList ts
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, h => by
    simp only [ValTy.checkList, Bool.and_eq_true] at h
    simp only [ValTy.lowerList, ValTy.flatList, List.map_append, refLower_types t v h.1,
      refLowerList_types ts vs h.2]
end

theorem checkCase_some : ∀ (cs : List (Option ValTy)) (i : Nat) (p : Option Silmaril.Wasm.Component.Val),
    ValTy.checkCase cs i p = true → ∃ c, cs[i]? = some c ∧ ValTy.checkOpt c p = true
  | [], _, _, h => by simp [ValTy.checkCase] at h
  | c :: _, 0, _, h => ⟨c, rfl, h⟩
  | _ :: cs, i + 1, p, h => checkCase_some cs i p h

theorem lowerOpt_types : ∀ (c : Option ValTy) (p : Option Silmaril.Wasm.Component.Val),
    ValTy.checkOpt c p = true → (ValTy.lowerOpt c p).map (·.type) = ValTy.flatOpt c
  | none, none, _ => rfl
  | some t, some v, h => refLower_types t v h
  | none, some _, h | some _, none, h => by simp [ValTy.checkOpt] at h

theorem lowerCase_types : ∀ (cs : List (Option ValTy)) (i : Nat) (c : Option ValTy)
    (p : Option Silmaril.Wasm.Component.Val), cs[i]? = some c → ValTy.checkOpt c p = true →
      (ValTy.lowerCase cs i p).map (·.type) = ValTy.flatOpt c
  | [], _, _, _, h, _ => by simp at h
  | c' :: _, 0, c, p, h, hc => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact lowerOpt_types c' p hc
  | _ :: cs, i + 1, c, p, h, hc => lowerCase_types cs i c p h hc

theorem flattenOption_toClosed (p : Silmaril.Wasm.AddrType) :
    ∀ c : Option ValTy, flattenOption p (c.map toClosed) = ValTy.flatOpt c
  | none => by simp only [Option.map_none, flattenOption, ValTy.flatOpt]
  | some t => by simp only [Option.map_some, flattenOption, ValTy.flatOpt, flatten_toClosed]

theorem toClosedCases_getElem? : ∀ (cs : List (Option ValTy)) (i : Nat),
    (toClosedCases cs)[i]? = cs[i]?.map (Option.map toClosed)
  | [], _ => rfl
  | none :: _, 0 => rfl
  | some _ :: _, 0 => rfl
  | none :: cs, i + 1 => toClosedCases_getElem? cs i
  | some _ :: cs, i + 1 => toClosedCases_getElem? cs i

theorem caseFlat_eq (p : Silmaril.Wasm.AddrType) {cs : List (Option ValTy)}
    {fs : List (String × Option (WIT.ClosedType RtId))} (hfs : fs.map Prod.snd = toClosedCases cs)
    {i : Nat} {c : Option ValTy} (hc : cs[i]? = some c) : caseFlat p fs i = ValTy.flatOpt c := by
  have h : (fs[i]?).map Prod.snd = some (c.map toClosed) := by
    rw [← List.getElem?_map, hfs, toClosedCases_getElem?, hc]
    rfl
  obtain ⟨⟨n, u⟩, hu, hu'⟩ := Option.map_eq_some_iff.mp h
  simp only at hu'
  simp only [caseFlat, hu, hu', flattenOption_toClosed]

theorem toClosedCases_length : ∀ cs : List (Option ValTy), (toClosedCases cs).length = cs.length
  | [] => rfl
  | none :: cs => by simp only [toClosedCases, List.length_cons, toClosedCases_length cs]
  | some _ :: cs => by simp only [toClosedCases, List.length_cons, toClosedCases_length cs]

/-! ## Lowering -/

theorem value_int_ofInt_toInt32 (x : BitVec 32) :
    Silmaril.Wasm.Execution.Runtime.Value.int .i32
      (BitVec.ofInt Silmaril.Wasm.IntType.i32.width x.toInt) = Flat.i32 x := by
  change Silmaril.Wasm.Execution.Runtime.Value.int .i32 (BitVec.ofInt 32 x.toInt) = _
  rw [BitVec.ofInt_toInt]
  rfl

theorem value_int_ofInt_toInt64 (x : BitVec 64) :
    Silmaril.Wasm.Execution.Runtime.Value.int .i64
      (BitVec.ofInt Silmaril.Wasm.IntType.i64.width x.toInt) = Flat.i64 x := by
  change Silmaril.Wasm.Execution.Runtime.Value.int .i64 (BitVec.ofInt 64 x.toInt) = _
  rw [BitVec.ofInt_toInt]
  rfl

variable (lim : Limits) (q : Quirks) (cx : Silmaril.Wasm.Component.Runtime.LiftLowerContext E) (p : Silmaril.Wasm.AddrType)

mutual
/-- **Reference `lower_flat` on IR types is the IR lowering**, for float-free types and
well-typed values. -/
theorem lowerFlatAt_toClosed : ∀ (t : ValTy) (v : Silmaril.Wasm.Component.Val),
    floatFree t = true → t.check v = true →
      (lowerFlatAt lim q cx p (toRefVal v) (toClosed t) : P E σ _) = pure (t.lower v)
  | t, v, hf, h => by
    cases t <;> cases v <;>
      first
        | (simp only [ValTy.check, Bool.false_eq_true] at h; done)
        | (simp only [floatFree, Bool.false_eq_true] at hf; done)
        | (simp only [toRefVal, toClosed, lowerFlatAt, lowerFlatPrim, Value.IntKind.ofPrimitive,
            lowerFlatInt, intKindCore, Value.IntKind.toScalar, ABI.Scalar.coreType, ValTy.lower,
            i32Flat]
           first
             | rfl
             | (cases ‹Bool› <;> rfl)
             | (congr 1; simp; done)
             | (congr 1; simp; rfl)
             | (rw [value_int_ofInt_toInt32])
             | (rw [value_int_ofInt_toInt64]))
        | (simp only [toRefVal, toClosed, lowerFlatAt, ValTy.lower]
           exact lowerFlatFields_toClosed _ _ _ (labels_map_snd "f" _)
             (by simpa only [floatFree] using hf) (by simpa only [ValTy.check] using h))
        | (exact lowerVariant_toClosed _ _ _ (by simpa only [floatFree] using hf)
             (by simpa only [ValTy.check] using h))

theorem lowerVariant_toClosed : ∀ (cs : List (Option ValTy)) (i : Nat)
    (pl : Option Silmaril.Wasm.Component.Val), floatFreeCases cs = true →
      (decide (i < 2 ^ 32) && ValTy.checkCase cs i pl) = true →
      (lowerFlatAt lim q cx p (toRefVal (.variant i pl)) (toClosed (.variant cs)) : P E σ _) =
        pure (ValTy.lower (.variant cs) (.variant i pl))
  | cs, i, pl, hf, h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨c, hc, hco⟩ := checkCase_some cs i pl h.2
    have hlen : i < (labels "c" (toClosedCases cs)).length := by
      simp only [labels, List.length_mapIdx, toClosedCases_length]
      exact (List.getElem?_eq_some_iff.mp hc).1
    have hpay : (lowerFlatCase lim q cx p i (toRefOpt pl) (labels "c" (toClosedCases cs)) :
        P E σ _) = pure (ValTy.lowerCase cs i pl) :=
      lowerFlatCase_toClosed cs _ i pl (labels_map_snd "c" _) hf h.2
    have hdom : Dom (ValTy.flatOpt c) (ValTy.flatCases cs) := dom_case cs i c hf hc
    have hint : IntFlat (ValTy.flatOpt c) := Dom.int hdom (flatCases_int cs hf)
    have hcoe := coerceLowerSlots_eq (E := E) (σ := σ) _ _ _ (lowerCase_types cs i c pl hc hco)
      hint hdom
    simp only [toRefVal, toClosed, lowerFlatAt, ValTy.lower, lowerFlatVariantWith, hlen, ↓reduceIte,
      flattenCases_toClosed p cs _ (labels_map_snd "c" _), caseFlat_eq p (labels_map_snd "c" _) hc,
      hpay, pure_bind]
    calc _ = (List.cons (i32Flat i)) <$> (do
            let x ← coerceLowerSlots (ValTy.flatOpt c) (ValTy.flatCases cs) (ValTy.lowerCase cs i pl)
            pure (x.1 ++ x.2.map Silmaril.Wasm.Execution.Runtime.Value.zero) : P E σ _) := by
          simp only [map_eq_pure_bind, bind_assoc, pure_bind]
      _ = _ := by rw [hcoe]; rfl

theorem lowerFlatCase_toClosed : ∀ (cs : List (Option ValTy))
    (fs : List (String × Option (WIT.ClosedType RtId))) (i : Nat)
    (pl : Option Silmaril.Wasm.Component.Val), fs.map Prod.snd = toClosedCases cs →
      floatFreeCases cs = true → ValTy.checkCase cs i pl = true →
        (lowerFlatCase lim q cx p i (toRefOpt pl) fs : P E σ _) = pure (ValTy.lowerCase cs i pl)
  | [], _, _, _, _, _, h => by simp [ValTy.checkCase] at h
  | none :: _, [], _, _, hfs, _, _ | some _ :: _, [], _, _, hfs, _, _ => by
    simp [toClosedCases] at hfs
  | none :: cs, (n, u) :: fs, 0, pl, hfs, _, h => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    cases pl with
    | none => rfl
    | some _ => simp [ValTy.checkCase, ValTy.checkOpt] at h
  | some t :: cs, (n, u) :: fs, 0, pl, hfs, hf, h => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    simp only [floatFreeCases, Bool.and_eq_true] at hf
    cases pl with
    | none => simp [ValTy.checkCase, ValTy.checkOpt] at h
    | some v =>
      simp only [ValTy.checkCase, ValTy.checkOpt] at h
      simp only [toRefOpt, lowerFlatCase, lowerFlatOpt, ValTy.lowerCase, ValTy.lowerOpt,
        lowerFlatAt_toClosed t v hf.1 h]
  | c :: cs, (n, u) :: fs, i + 1, pl, hfs, hf, h => by
    have hfs' : fs.map Prod.snd = toClosedCases cs := by
      cases c <;> simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs <;> exact hfs.2
    have hf' : floatFreeCases cs = true := by
      cases c <;> simp only [floatFreeCases, Bool.and_eq_true] at hf <;> first | exact hf | exact hf.2
    simp only [lowerFlatCase, ValTy.lowerCase]
    exact lowerFlatCase_toClosed cs fs i pl hfs' hf' h

theorem lowerFlatFields_toClosed : ∀ (ts : List ValTy) (vs : List Silmaril.Wasm.Component.Val)
    (fs : List (String × WIT.ClosedType RtId)), fs.map Prod.snd = toClosedList ts →
      floatFreeList ts = true → ValTy.checkList ts vs = true →
        (lowerFlatFields lim q cx p (toRefVals vs) fs : P E σ _) = pure (ValTy.lowerList ts vs)
  | [], [], [], _, _, _ => rfl
  | [], [], _ :: _, h, _, _ => by simp [toClosedList] at h
  | _ :: _, _, [], h, _, _ => by simp [toClosedList] at h
  | [], _ :: _, _, _, _, h | _ :: _, [], _, _, _, h => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, (n, u) :: fs, hfs, hf, h => by
    simp only [List.map_cons, toClosedList, List.cons.injEq] at hfs
    obtain ⟨rfl, hfs⟩ := hfs
    simp only [floatFreeList, Bool.and_eq_true] at hf
    simp only [ValTy.checkList, Bool.and_eq_true] at h
    simp only [toRefVals, lowerFlatFields, lowerFlatAt_toClosed t v hf.1 h.1,
      lowerFlatFields_toClosed ts vs fs hfs hf.2 h.2, pure_bind, ValTy.lowerList]
end

theorem toRefVals_eq : ∀ vs : List Silmaril.Wasm.Component.Val, toRefVals vs = vs.map toRefVal
  | [] => rfl
  | v :: vs => by simp only [toRefVals, List.map_cons, toRefVals_eq vs]

theorem flattenTypes_toClosed (p : Silmaril.Wasm.AddrType) :
    ∀ ts : List ValTy, flattenTypes p (toClosedList ts) = ValTy.flatList ts
  | [] => by simp only [toClosedList, flattenTypes, ValTy.flatList]
  | t :: ts => by
    simp only [toClosedList, flattenTypes, ValTy.flatList, flatten_toClosed, flattenTypes_toClosed p ts]

theorem lowerFlatTypes_toClosed : ∀ (ts : List ValTy) (vs : List Silmaril.Wasm.Component.Val),
    floatFreeList ts = true → ValTy.checkList ts vs = true →
      (lowerFlatTypes lim q cx p (toRefVals vs) (toClosedList ts) : P E σ _) =
        pure (ValTy.lowerList ts vs)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, hf, h => by
    simp only [floatFreeList, Bool.and_eq_true] at hf
    simp only [ValTy.checkList, Bool.and_eq_true] at h
    simp only [toRefVals, toClosedList, lowerFlatTypes, lowerFlatAt_toClosed lim q cx p t v hf.1 h.1,
      lowerFlatTypes_toClosed ts vs hf.2 h.2, pure_bind, ValTy.lowerList]

/-- **Reference `lower_flat_values` on IR argument types is `checkLower`** (after reading the
pointer type of the context): float-free types, well-typed values, flat arity within `max`. -/
theorem lowerFlatValues_toClosed {max : Nat} {ts : List ValTy} {vs : List Silmaril.Wasm.Component.Val}
    (hf : floatFreeList ts = true) (h : ValTy.checkList ts vs = true)
    (hmax : (ValTy.flatList ts).length ≤ max) (op : Option FlatCursor) :
    (lowerFlatValues lim q cx max (vs.map toRefVal) (toClosedList ts) op : P E σ _) =
      ptrType cx >>= fun _ => pure (lowerArgs ts vs) := by
  unfold lowerFlatValues
  congr 1
  funext p
  have hle : ¬ (flattenTypes p (toClosedList ts)).length > max := by
    rw [flattenTypes_toClosed]
    omega
  simp only [hle, ↓reduceIte, ← toRefVals_eq, lowerFlatTypes_toClosed lim q cx p ts vs hf h,
    lowerArgs]

/-! ## Lifting: scalars -/

theorem convertI32ToChar?_eq (x : BitVec 32) : ABI.convertI32ToChar? x = charOfBits x := by
  unfold ABI.convertI32ToChar? charOfBits
  have hv : (UInt32.ofBitVec x).isValidChar ↔ ABI.IsUnicodeScalar x.toNat := by
    rw [ABI.isUnicodeScalar_iff_isValidChar]
    rfl
  by_cases h : ABI.IsUnicodeScalar x.toNat
  · simp only [h, hv.mpr h, ↓reduceDIte, Option.some.injEq]
    apply Char.ext
    simp only [Char.ofNatAux]
    apply UInt32.toBitVec_inj.mp
    simp
  · have h' : ¬ (UInt32.ofBitVec x).isValidChar := fun h' => h (hv.mp h')
    simp only [h, h', ↓reduceDIte]

theorem liftFlatBool_eq (x : BitVec (Silmaril.Wasm.NumType.int .i32).width) :
    liftFlatBool ⟨.int .i32, x⟩ = (x != 0) := by
  simp only [liftFlatBool, convertIntToBool]
  by_cases h : x = 0
  · subst h; rfl
  · have h' : (x.toNat : Int) ≠ 0 := by
      intro e; apply h; apply BitVec.eq_of_toNat_eq; simpa using e
    rw [Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq, h, not_false_eq_true, iff_true]
    exact h'

theorem signInterpret_toNat {w : Nat} (hw : 0 < w) (y : BitVec w) :
    signInterpret w (y.toNat : Int) = y.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  unfold signInterpret
  have hp : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hp' : (2 : Nat) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hc : ((2 ^ (w - 1) : Nat) : Int) = (2 : Int) ^ (w - 1) := by push_cast; rfl
  have hc' : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by push_cast; rfl
  split_ifs with h₁ h₂ h₂ <;> omega

theorem liftFlatInt_unsigned {k : Value.IntKind} {w : Nat} (hk : k.signed = false)
    (hw : k.width = w) (v : Flat) :
    liftFlatInt k v = ((BitVec.ofNat w v.bits.toNat).toNat : Int) := by
  subst hw
  simp only [liftFlatInt, hk, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
  push_cast
  rfl

theorem liftFlatInt_signed {k : Value.IntKind} {w : Nat} (hk : k.signed = true)
    (hw : k.width = w) (hw0 : 0 < w) (v : Flat) :
    liftFlatInt k v = (BitVec.ofNat w v.bits.toNat).toInt := by
  subst hw
  rw [← signInterpret_toNat hw0]
  simp only [liftFlatInt, hk, ↓reduceIte, BitVec.toNat_ofNat]
  push_cast
  rfl

/-! ## Lifting: programs that trap, cursors -/

/-- The program traps at its first operation. -/
def IsTrap {α : Type} (prog : P E σ α) : Prop :=
  ∃ (r : TrapReason) (k : Empty → P E σ α), prog = .op (S := Eff E σ) (.trap r) k

theorem IsTrap.bind {α β : Type} {prog : P E σ α} (h : IsTrap prog) (f : α → P E σ β) :
    IsTrap (prog >>= f) := by
  obtain ⟨r, k, rfl⟩ := h
  exact ⟨r, fun e => k e >>= f, rfl⟩

theorem isTrap_trap {α : Type} (r : TrapReason) : IsTrap (trap r : P E σ α) := ⟨r, _, rfl⟩

theorem next_eq {ys : List Flat} {n : Nat} {y : Flat} {rest : List Flat} (h : ys.drop n = y :: rest)
    (t : Silmaril.Wasm.NumType) :
    (FlatCursor.next ⟨ys, n⟩ t : P E σ _) = pure (y, ⟨ys, n + 1⟩) := by
  have hy : ys[n]? = some y := by
    rw [← List.head?_drop, h]
    rfl
  simp only [FlatCursor.next, hy]

theorem drop_succ_of {ys : List Flat} {n : Nat} {y : Flat} {rest : List Flat}
    (h : ys.drop n = y :: rest) : ys.drop (n + 1) = rest := by
  rw [← List.drop_drop, h]
  rfl

theorem nextN_eq : ∀ (ts : List Silmaril.Wasm.NumType) (ys : List Flat) (n : Nat),
    ts.length ≤ (ys.drop n).length →
      (FlatCursor.nextN ⟨ys, n⟩ ts : P E σ _) =
        pure ((ys.drop n).take ts.length, ⟨ys, n + ts.length⟩)
  | [], ys, n, _ => rfl
  | t :: ts, ys, n, h => by
    obtain ⟨y, rest, hd⟩ : ∃ y rest, ys.drop n = y :: rest := by
      cases hdn : ys.drop n with
      | nil => rw [hdn] at h; simp at h
      | cons y rest => exact ⟨y, rest, rfl⟩
    have h' : ts.length ≤ (ys.drop (n + 1)).length := by
      rw [drop_succ_of hd]; rw [hd] at h; simpa using h
    simp only [FlatCursor.nextN, next_eq hd, pure_bind, nextN_eq ts ys (n + 1) h', hd,
      drop_succ_of hd, List.length_cons, List.take_succ_cons]
    congr 3
    omega

/-! ## Lifting: the IR side -/

/-- The first `fl.length` flat values have the types `fl`. -/
def Typed (fl : List Silmaril.Wasm.NumType) (xs : List Flat) : Prop :=
  (xs.take fl.length).map (·.type) = fl ∧ fl.length ≤ xs.length

theorem Typed.left {a b : List Silmaril.Wasm.NumType} {xs : List Flat} (h : Typed (a ++ b) xs) :
    Typed a xs := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, by simp at h₂; omega⟩
  have := congrArg (List.take a.length) h₁
  rwa [← List.map_take, List.take_take, List.take_left' rfl, Nat.min_eq_left (by simp)] at this

theorem Typed.right {a b : List Silmaril.Wasm.NumType} {xs : List Flat} (h : Typed (a ++ b) xs) :
    Typed b (xs.drop a.length) := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, by simp at h₂ ⊢; omega⟩
  have := congrArg (List.drop a.length) h₁
  rw [← List.map_drop, List.drop_take, List.drop_left' rfl] at this
  simpa [Nat.add_sub_cancel_left] using this

theorem flatTake_eq : ∀ (ts : List Silmaril.Wasm.NumType) (vs : List Flat), Typed ts vs →
    Flat.take ts vs = some (vs.take ts.length, vs.drop ts.length)
  | [], vs, _ => rfl
  | t :: ts, [], h => by simp [Typed] at h
  | t :: ts, v :: vs, ⟨h₁, h₂⟩ => by
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, List.cons.injEq] at h₁
    have ih := flatTake_eq ts vs ⟨h₁.2, by simp at h₂; omega⟩
    simp only [Flat.take, h₁.1, ↓reduceIte, ih, Option.map_some, List.length_cons,
      List.take_succ_cons, List.drop_succ_cons]

theorem liftCase_some : ∀ (cs : List (Option ValTy)) (i : Nat) (c : Option ValTy) (js : List Flat),
    cs[i]? = some c → ValTy.liftCase cs i js = ValTy.liftOpt c (Flat.unfit (ValTy.flatOpt c) js)
  | [], _, _, _, h => by simp at h
  | c' :: _, 0, c, js, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rfl
  | _ :: cs, i + 1, c, js, h => liftCase_some cs i c js h

theorem liftCase_none : ∀ (cs : List (Option ValTy)) (i : Nat) (js : List Flat),
    cs.length ≤ i → ValTy.liftCase cs i js = none
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => by simp at h
  | _ :: cs, i + 1, js, h => liftCase_none cs i js (by simp at h; omega)

theorem coerceLiftFlat_eq {h w : Silmaril.Wasm.NumType} {v : Flat} (hv : v.type = h)
    (hd : w = h ∨ (w = .int .i32 ∧ h = .int .i64)) (hi : w = .int .i32 ∨ w = .int .i64) :
    coerceLiftFlat h w v = Flat.retype w v := by
  obtain ⟨t, b⟩ := v
  simp only at hv
  subst hv
  rcases hd with rfl | ⟨rfl, rfl⟩
  · rcases hi with rfl | rfl <;> simp only [coerceLiftFlat, Flat.retype, BitVec.setWidth_eq]
  · simp only [coerceLiftFlat, Flat.retype, wrapI64ToI32, BitVec.ofNat_toNat]
    rfl

theorem coerceLiftSlots_eq : ∀ (ws hs : List Silmaril.Wasm.NumType) (js : List Flat),
    Dom ws hs → IntFlat ws → js.map (·.type) = hs →
      coerceLiftSlots hs ws js = Flat.unfit ws js
  | [], _, _, _, _, _ => by
    cases ‹List Silmaril.Wasm.NumType› <;> rfl
  | _ :: _, [], _, hd, _, _ => hd.elim
  | w :: ws, h :: hs, [], _, _, hj => by simp at hj
  | w :: ws, h :: hs, v :: js, ⟨hwh, hd⟩, hi, hj => by
    simp only [List.map_cons, List.cons.injEq] at hj
    have hwh' : w = h ∨ (w = .int .i32 ∧ h = .int .i64) := hwh
    simp only [coerceLiftSlots, Flat.unfit, coerceLiftFlat_eq hj.1 hwh' (hi w List.mem_cons_self),
      coerceLiftSlots_eq ws hs js hd (fun x hx => hi x (List.mem_cons_of_mem _ hx)) hj.2]

/-! ## Lifting -/

/-- The reference lift of one value relates to the IR lift (`res`): the same value (as a
reference value) and the cursor advanced to `n'`, or a trap where the IR traps. -/
def LiftRel (prog : P E σ (Value.Val × FlatCursor))
    (res : Option (Silmaril.Wasm.Component.Val × List Flat)) (ys : List Flat) (n' : Nat) : Prop :=
  match res with
  | some (w, r) => prog = pure (toRefVal w, ⟨ys, n'⟩) ∧ r = ys.drop n'
  | none => IsTrap prog

/-- `LiftRel` for lists of values. -/
def LiftsRel (prog : P E σ (List Value.Val × FlatCursor))
    (res : Option (List Silmaril.Wasm.Component.Val × List Flat)) (ys : List Flat) (n' : Nat) : Prop :=
  match res with
  | some (ws, r) => prog = pure (toRefVals ws, ⟨ys, n'⟩) ∧ r = ys.drop n'
  | none => IsTrap prog

/-- `LiftRel` for an optional payload, whose cursor is discarded. -/
def CaseRel (prog : P E σ (Option Value.Val × FlatCursor))
    (res : Option (Option Silmaril.Wasm.Component.Val)) : Prop :=
  match res with
  | some o => ∃ c, prog = pure (toRefOpt o, c)
  | none => IsTrap prog

theorem drop_cons_of_typed {fl : List Silmaril.Wasm.NumType} {xs : List Flat} (h : Typed fl xs)
    (hne : fl ≠ []) : ∃ y rest, xs = y :: rest := by
  cases xs with
  | nil => cases fl with
    | nil => exact absurd rfl hne
    | cons _ _ => simp [Typed] at h
  | cons y rest => exact ⟨y, rest, rfl⟩

theorem typed_head {f : Silmaril.Wasm.NumType} {fl : List Silmaril.Wasm.NumType} {y : Flat}
    {rest : List Flat} (h : Typed (f :: fl) (y :: rest)) : y.type = f := by
  obtain ⟨h₁, -⟩ := h
  simp only [List.length_cons, List.take_succ_cons, List.map_cons, List.cons.injEq] at h₁
  exact h₁.1

theorem wrap_i32 (b : BitVec (Silmaril.Wasm.NumType.int .i32).width) :
    wrapI64ToI32 ⟨.int .i32, b⟩ = b := by
  change BitVec.ofNat 32 (b : BitVec 32).toNat = (b : BitVec 32)
  rw [BitVec.ofNat_toNat]
  exact BitVec.setWidth_eq _

theorem liftChar {ys : List Flat} {n : Nat} {rest : List Flat}
    (b : BitVec (Silmaril.Wasm.NumType.int .i32).width)
    (hd : ys.drop n = ⟨.int .i32, b⟩ :: rest) (hrest : rest = ys.drop (n + 1)) :
    LiftRel (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed .char) ⟨ys, n⟩)
      (ValTy.lift .char (⟨.int .i32, b⟩ :: rest)) ys (n + 1) := by
  have hp : (liftFlatAt (σ := σ) lim q cx p (toClosed .char) ⟨ys, n⟩) =
      (do let c ← orTrap .invalidChar (charOfBits b); pure (Value.Val.char c, ⟨ys, n + 1⟩)) := by
    simp only [toClosed, liftFlatAt, liftFlatPrim, next_eq hd, pure_bind, wrap_i32,
      convertI32ToChar, convertI32ToChar?_eq]
  rw [hp]
  cases hc : charOfBits b with
  | none =>
    simp only [ValTy.lift, hc, Option.map_none, orTrap, LiftRel]
    exact (isTrap_trap _).bind _
  | some c =>
    simp only [ValTy.lift, hc, Option.map_some, orTrap, LiftRel, pure_bind]
    exact ⟨rfl, hrest⟩

/-- One scalar value. -/
theorem liftPrim_toClosed (t : ValTy) (ys : List Flat) (n : Nat) (y : Flat) (rest : List Flat)
    (hd : ys.drop n = y :: rest) (hty : t.flat = [y.type]) (hf : floatFree t = true)
    (hs : ∀ ts, t ≠ .record ts) (hv : ∀ cs, t ≠ .variant cs) :
    LiftRel (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed t) ⟨ys, n⟩)
      (ValTy.lift t (ys.drop n)) ys (n + 1) := by
  obtain ⟨ty, b⟩ := y
  rw [hd]
  have hrest : rest = ys.drop (n + 1) := (drop_succ_of hd).symm
  cases t <;>
    first
      | exact absurd rfl (hs _)
      | exact absurd rfl (hv _)
      | (simp only [floatFree, Bool.false_eq_true] at hf; done)
      | (simp only [ValTy.flat, List.cons.injEq, and_true] at hty
         subst hty
         first
           | (refine ⟨?_, hrest⟩
              simp only [toClosed, liftFlatAt, liftFlatPrim, Value.IntKind.ofPrimitive, next_eq hd,
                pure_bind, toRefVal, intKindCore]
              first
                | (rw [liftFlatBool_eq])
                | (rw [liftFlatInt_unsigned rfl rfl]
                   simp only [BitVec.ofNat_toNat]
                   rfl)
                | (rw [liftFlatInt_signed rfl rfl (by decide)]
                   simp only [BitVec.ofNat_toNat]
                   rfl))
           | exact liftChar lim q cx p b hd hrest)

theorem unfit_types : ∀ (ws : List Silmaril.Wasm.NumType) (js : List Flat), ws.length ≤ js.length →
    (Flat.unfit ws js).map (·.type) = ws
  | [], _, _ => rfl
  | w :: ws, [], h => by simp at h
  | w :: ws, j :: js, h => by
    simp only [Flat.unfit, List.map_cons, unfit_types ws js (by simp at h; omega)]
    rfl

theorem Dom.length_le : ∀ {hs ws : List Silmaril.Wasm.NumType}, Dom hs ws → hs.length ≤ ws.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, ⟨_, hd⟩ => Nat.succ_le_succ (Dom.length_le hd)

theorem typed_length {fl : List Silmaril.Wasm.NumType} {xs : List Flat} (h : Typed fl xs) :
    ((xs.take fl.length).map (·.type)).length = fl.length := by
  rw [h.1]

/-- One scalar value, from a typed cursor. -/
theorem liftScalar_toClosed (t : ValTy) (ys : List Flat) (n : Nat) {f : Silmaril.Wasm.NumType}
    (hfl : t.flat = [f]) (hf : floatFree t = true) (ht : Typed t.flat (ys.drop n))
    (hs : ∀ ts, t ≠ .record ts) (hv : ∀ cs, t ≠ .variant cs) :
    LiftRel (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed t) ⟨ys, n⟩)
      (ValTy.lift t (ys.drop n)) ys (n + t.flat.length) := by
  rw [hfl] at ht ⊢
  obtain ⟨y, rest, hd⟩ := drop_cons_of_typed ht (List.cons_ne_nil _ _)
  have hy : y.type = f := typed_head (hd ▸ ht)
  exact liftPrim_toClosed lim q cx p t ys n y rest hd (by rw [hfl, hy]) hf hs hv

mutual
/-- **Reference `lift_flat` on IR types is the IR lift**, for float-free types and flat values of
the right types: the same values, or a trap where the IR traps. -/
theorem liftFlatAt_toClosed : ∀ (t : ValTy) (ys : List Flat) (n : Nat), floatFree t = true →
    Typed t.flat (ys.drop n) →
      LiftRel (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed t) ⟨ys, n⟩)
        (ValTy.lift t (ys.drop n)) ys (n + t.flat.length)
  | .record ts, ys, n, hf, ht => by
    have ih := liftFlatFields_toClosed ts (labels "f" (toClosedList ts)) ys n
      (labels_map_snd "f" _) (by simpa only [floatFree] using hf) (by simpa only [ValTy.flat] using ht)
    simp only [ValTy.flat]
    simp only [toClosed, liftFlatAt, ValTy.lift]
    revert ih
    cases ValTy.liftList ts (ys.drop n) with
    | none => intro ih; exact ih.bind _
    | some pr =>
      intro ih
      obtain ⟨hp, hr⟩ := ih
      refine ⟨?_, hr⟩
      rw [hp]
      rfl
  | .variant cs, ys, n, hf, ht => liftVariant_toClosed cs ys n (by simpa only [floatFree] using hf) ht
  | .bool, ys, n, hf, ht => liftScalar_toClosed lim q cx p .bool ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .s8, ys, n, hf, ht => liftScalar_toClosed lim q cx p .s8 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .u8, ys, n, hf, ht => liftScalar_toClosed lim q cx p .u8 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .s16, ys, n, hf, ht => liftScalar_toClosed lim q cx p .s16 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .u16, ys, n, hf, ht => liftScalar_toClosed lim q cx p .u16 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .s32, ys, n, hf, ht => liftScalar_toClosed lim q cx p .s32 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .u32, ys, n, hf, ht => liftScalar_toClosed lim q cx p .u32 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .s64, ys, n, hf, ht => liftScalar_toClosed lim q cx p .s64 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .u64, ys, n, hf, ht => liftScalar_toClosed lim q cx p .u64 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .f32, ys, n, hf, ht => liftScalar_toClosed lim q cx p .f32 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .f64, ys, n, hf, ht => liftScalar_toClosed lim q cx p .f64 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .char, ys, n, hf, ht => liftScalar_toClosed lim q cx p .char ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)

theorem liftVariant_toClosed : ∀ (cs : List (Option ValTy)) (ys : List Flat) (n : Nat),
    floatFreeCases cs = true → Typed (ValTy.flat (.variant cs)) (ys.drop n) →
      LiftRel (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed (.variant cs)) ⟨ys, n⟩)
        (ValTy.lift (.variant cs) (ys.drop n)) ys (n + (ValTy.flat (.variant cs)).length)
  | cs, ys, n, hf, ht => by
    simp only [ValTy.flat] at ht ⊢
    obtain ⟨d, rest, hd⟩ := drop_cons_of_typed ht (List.cons_ne_nil _ _)
    have hdty : d.type = .int .i32 := typed_head (hd ▸ ht)
    obtain ⟨dt, db⟩ := d
    simp only at hdty
    subst hdty
    have hrest : rest = ys.drop (n + 1) := (drop_succ_of hd).symm
    have htr : Typed (ValTy.flatCases cs) rest := by
      have h' : Typed ([.int .i32] ++ ValTy.flatCases cs) (⟨.int .i32, db⟩ :: rest) := hd ▸ ht
      simpa only [List.length_singleton, List.drop_one, List.tail_cons] using h'.right
    have hlen : (labels "c" (toClosedCases cs)).length = cs.length := by
      simp only [labels, List.length_mapIdx, toClosedCases_length]
    have hjoin : variantPayload (flattenCases p (labels "c" (toClosedCases cs))) =
        ValTy.flatCases cs := flattenCases_toClosed p cs _ (labels_map_snd "c" _)
    rw [hd]
    simp only [ValTy.lift, flatTake_eq _ _ htr, toClosed, liftFlatAt, liftFlatVariantWith,
      next_eq hd, pure_bind, flatNat, hlen, hjoin]
    by_cases hlt : db.toNat < cs.length
    · obtain ⟨c, hc⟩ : ∃ c, cs[db.toNat]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
      have hng : ¬ (db.toNat ≥ cs.length) := Nat.not_le.mpr hlt
      have hlen' : (ValTy.flatCases cs).length ≤ (ys.drop (n + 1)).length := by
        rw [← hrest]; exact htr.2
      have hxs : (rest.take (ValTy.flatCases cs).length).map (·.type) = ValTy.flatCases cs := htr.1
      have hdom : Dom (ValTy.flatOpt c) (ValTy.flatCases cs) := dom_case cs _ c hf hc
      have hint : IntFlat (ValTy.flatOpt c) := Dom.int hdom (flatCases_int cs hf)
      have hzs : (Flat.unfit (ValTy.flatOpt c) (rest.take (ValTy.flatCases cs).length)).map
          (·.type) = ValTy.flatOpt c :=
        unfit_types _ _ (by
          have h₁ := congrArg List.length hxs
          rw [List.length_map] at h₁
          rw [h₁]
          exact hdom.length_le)
      have ih := liftFlatCase_toClosed cs (labels "c" (toClosedCases cs)) db.toNat c _
        (labels_map_snd "c" _) hf hc hzs
      simp only [hng, decide_false, trapIf, Bool.false_eq_true, ↓reduceIte, pure_bind,
        nextN_eq _ ys (n + 1) hlen', ← hrest, caseFlat_eq p (labels_map_snd "c" _) hc,
        coerceLiftSlots_eq _ _ _ hdom hint hxs, liftCase_some cs _ c _ hc, FlatCursor.ofList]
      revert ih
      cases ValTy.liftOpt c (Flat.unfit (ValTy.flatOpt c) (rest.take (ValTy.flatCases cs).length)) with
      | none => intro ih; exact ih.bind _
      | some o =>
        intro ih
        obtain ⟨cur, hcur⟩ := ih
        refine ⟨?_, ?_⟩
        · rw [hcur, pure_bind]
          simp only [List.length_cons, toRefVal]
          congr 3
          omega
        · rw [hrest, List.drop_drop]
          congr 1
          simp only [List.length_cons]
          omega
    · have hge : cs.length ≤ db.toNat := Nat.le_of_not_lt hlt
      simp only [ge_iff_le, hge, decide_true, trapIf, ↓reduceIte, liftCase_none _ _ _ hge,
        Option.map_none, LiftRel]
      exact (isTrap_trap _).bind _

theorem liftFlatCase_toClosed : ∀ (cs : List (Option ValTy))
    (fs : List (String × Option (WIT.ClosedType RtId))) (i : Nat) (c : Option ValTy)
    (zs : List Flat), fs.map Prod.snd = toClosedCases cs → floatFreeCases cs = true →
      cs[i]? = some c → zs.map (·.type) = ValTy.flatOpt c →
        CaseRel (σ := σ) (liftFlatCaseAt (σ := σ) lim q cx p fs i ⟨zs, 0⟩) (ValTy.liftOpt c zs)
  | [], _, _, _, _, _, _, hc, _ => by simp at hc
  | none :: _, [], _, _, _, hfs, _, _, _ | some _ :: _, [], _, _, _, hfs, _, _, _ => by
    simp [toClosedCases] at hfs
  | none :: cs, (nm, u) :: fs, 0, c, zs, hfs, _, hc, _ => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    exact ⟨⟨zs, 0⟩, rfl⟩
  | some t :: cs, (nm, u) :: fs, 0, c, zs, hfs, hf, hc, hz => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    simp only [floatFreeCases, Bool.and_eq_true] at hf
    simp only [ValTy.flatOpt] at hz
    have hlen : zs.length = t.flat.length := by rw [← hz, List.length_map]
    have ht : Typed t.flat (zs.drop 0) := by
      refine ⟨?_, by simp [hlen]⟩
      rw [List.drop_zero, ← hlen, List.take_length, hz]
    have ih := liftFlatAt_toClosed t zs 0 hf.1 ht
    rw [List.drop_zero] at ih
    simp only [liftFlatCaseAt, liftFlatOpt, ValTy.liftOpt]
    revert ih
    cases ValTy.lift t zs with
    | none => intro ih; exact ih.bind _
    | some pr =>
      intro ih
      obtain ⟨w, r⟩ := pr
      obtain ⟨hp, hr⟩ := ih
      have hr' : r = [] := by rw [hr, Nat.zero_add, ← hlen, List.drop_length]
      subst hr'
      exact ⟨_, by rw [hp, pure_bind]; rfl⟩
  | c' :: cs, (nm, u) :: fs, i + 1, c, zs, hfs, hf, hc, hz => by
    have hfs' : fs.map Prod.snd = toClosedCases cs := by
      cases c' <;> simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs <;> exact hfs.2
    have hf' : floatFreeCases cs = true := by
      cases c' <;> simp only [floatFreeCases, Bool.and_eq_true] at hf <;> first | exact hf | exact hf.2
    simp only [List.getElem?_cons_succ] at hc
    simp only [liftFlatCaseAt]
    exact liftFlatCase_toClosed cs fs i c zs hfs' hf' hc hz

theorem liftFlatFields_toClosed : ∀ (ts : List ValTy) (fs : List (String × WIT.ClosedType RtId))
    (ys : List Flat) (n : Nat), fs.map Prod.snd = toClosedList ts → floatFreeList ts = true →
      Typed (ValTy.flatList ts) (ys.drop n) →
        LiftsRel (σ := σ) (liftFlatFields (σ := σ) lim q cx p fs ⟨ys, n⟩)
          (ValTy.liftList ts (ys.drop n)) ys (n + (ValTy.flatList ts).length)
  | [], [], ys, n, _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _ => by simp [toClosedList] at h
  | t :: ts, (nm, u) :: fs, ys, n, hfs, hf, ht => by
    simp only [List.map_cons, toClosedList, List.cons.injEq] at hfs
    obtain ⟨rfl, hfs⟩ := hfs
    simp only [floatFreeList, Bool.and_eq_true] at hf
    simp only [ValTy.flatList] at ht
    have ih₁ := liftFlatAt_toClosed t ys n hf.1 ht.left
    simp only [liftFlatFields, ValTy.liftList, ValTy.flatList, List.length_append]
    revert ih₁
    cases ValTy.lift t (ys.drop n) with
    | none => intro ih₁; exact ih₁.bind _
    | some pr =>
      intro ih₁
      obtain ⟨w, r⟩ := pr
      obtain ⟨hp, hr⟩ := ih₁
      subst hr
      have ht₂ : Typed (ValTy.flatList ts) (ys.drop (n + t.flat.length)) := by
        have := ht.right
        rwa [List.drop_drop] at this
      have ih₂ := liftFlatFields_toClosed ts fs ys (n + t.flat.length) hfs hf.2 ht₂
      rw [hp, pure_bind]
      dsimp only
      revert ih₂
      cases ValTy.liftList ts (ys.drop (n + t.flat.length)) with
      | none => intro ih₂; exact ih₂.bind _
      | some pr₂ =>
        intro ih₂
        obtain ⟨hp₂, hr₂⟩ := ih₂
        refine ⟨?_, by rw [hr₂, Nat.add_assoc]⟩
        rw [hp₂, pure_bind, Nat.add_assoc]
        rfl
end

theorem liftFlatTypes_toClosed : ∀ (ts : List ValTy) (ys : List Flat) (n : Nat),
    floatFreeList ts = true → Typed (ValTy.flatList ts) (ys.drop n) →
      LiftsRel (σ := σ) (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, n⟩)
        (ValTy.liftList ts (ys.drop n)) ys (n + (ValTy.flatList ts).length)
  | ts, ys, n, hf, ht => by
    have hfs : (labels "f" (toClosedList ts)).map Prod.snd = toClosedList ts := labels_map_snd "f" _
    have h := liftFlatFields_toClosed (σ := σ) lim q cx p ts _ ys n hfs hf ht
    have heq : ∀ (fs : List (String × WIT.ClosedType RtId)) (c : FlatCursor),
        (liftFlatFields (σ := σ) lim q cx p fs c) = liftFlatTypes lim q cx p (fs.map Prod.snd) c := by
      intro fs
      induction fs with
      | nil => intro c; rfl
      | cons f fs ih =>
        intro c
        obtain ⟨nm, u⟩ := f
        simp only [liftFlatFields, liftFlatTypes, List.map_cons, ih]
    rwa [heq, hfs] at h

/-- **Reference `lift_flat_values` on IR result types is `liftArgs`** (after reading the pointer
type): flat arity within `max`. -/
theorem liftFlatValues_toClosed {max : Nat} {ts : List ValTy} {ys : List Flat}
    (hmax : (ValTy.flatList ts).length ≤ max) :
    (liftFlatValues (σ := σ) lim q cx max ⟨ys, 0⟩ (toClosedList ts)) =
      ptrType cx >>= fun p => liftFlatTypes lim q cx p (toClosedList ts) ⟨ys, 0⟩ := by
  unfold liftFlatValues
  congr 1
  funext p
  have hle : ¬ (flattenTypes p (toClosedList ts)).length > max := by
    rw [flattenTypes_toClosed]
    omega
  simp only [hle, ↓reduceIte]

/-- The direct lift path relates to `liftArgs`. -/
theorem liftFlatTypes_liftArgs {ts : List ValTy} {ys : List Flat} (hf : floatFreeList ts = true)
    (hys : ys.map (·.type) = ValTy.flatList ts) :
    match liftArgs ts ys with
    | some ws => ∃ c, (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, 0⟩) =
        pure (ws.map toRefVal, c)
    | none => IsTrap (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, 0⟩) := by
  have hlen : ys.length = (ValTy.flatList ts).length := by rw [← hys, List.length_map]
  have ht : Typed (ValTy.flatList ts) (ys.drop 0) := by
    refine ⟨?_, by simp [hlen]⟩
    rw [List.drop_zero, ← hlen, List.take_length, hys]
  have h := liftFlatTypes_toClosed (σ := σ) lim q cx p ts ys 0 hf ht
  rw [List.drop_zero] at h
  unfold liftArgs
  revert h
  cases ValTy.liftList ts ys with
  | none => intro h; exact h
  | some pr =>
    intro h
    obtain ⟨ws, r⟩ := pr
    obtain ⟨hp, hr⟩ := h
    have hr' : r = [] := by rw [hr, Nat.zero_add, ← hlen, List.drop_length]
    subst hr'
    exact ⟨_, by rw [hp, toRefVals_eq]⟩

end Silmaril.Proofs.Wasm.Component.Reference
