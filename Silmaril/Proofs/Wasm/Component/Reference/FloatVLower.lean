module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatVSlots

/-!
# Floats in variant payloads: lowering

Reference `lower_flat` with floats at every type, variant payloads included:

* `floatRelAt_comp`: `FloatRelAt` composes along a composition of the float relations;
* `lower_inv`: a flat lowering `t.lower v` whose float slots are changed by `NanLowerQ prof` is
  the lowering of some `v'` related to `v` by `FloatRelAt (NanLowerQ prof)`. Inside a variant the
  float slots of the joined payload are the float slots of the case (`slotOk_float`), and
  padding zeros are not NaNs;
* `lowerAtV`: reference `lower_flat` of `v` is a program of C7 choices whose results are the IR
  lowerings `t.lower v'` of the admissible `v'` (`NanAtV prof t v v'`, well typed). In a variant
  the payload's choices come first, then those of `coerceLowerSlots` (`encodeFloat` for a float
  in an integer slot); `lower_inv` turns the re-chosen slots into a value and `nanLower_trans`
  composes the two choices;
* `lowerFlatTypesV`: the same on argument lists.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Runtime (RtId)
open Silmaril.Wasm.Component.Value (NanLower)
open Silmaril.Wasm (FloatType IntType NumType)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Composition of `FloatRelAt` -/

section Comp

variable {R S T : (f : FloatType) → BitVec f.width → BitVec f.width → Prop}

mutual
theorem floatRelAt_comp (hRS : ∀ f x y z, R f x y → S f y z → T f x z) :
    ∀ (t : ValTy) (a b c : IVal), FloatRelAt R t a b →
    FloatRelAt S t b c → FloatRelAt T t a c
  | .f32, _, _, _, h₁, h₂ => by
    obtain ⟨x, y, rfl, rfl, h₁⟩ := h₁
    obtain ⟨y', z, e, rfl, h₂⟩ := h₂
    cases e
    exact ⟨x, z, rfl, rfl, hRS _ _ _ _ h₁ h₂⟩
  | .f64, _, _, _, h₁, h₂ => by
    obtain ⟨x, y, rfl, rfl, h₁⟩ := h₁
    obtain ⟨y', z, e, rfl, h₂⟩ := h₂
    cases e
    exact ⟨x, z, rfl, rfl, hRS _ _ _ _ h₁ h₂⟩
  | .record ts, _, _, _, h₁, h₂ => by
    obtain ⟨vs, ws, rfl, rfl, h₁⟩ := h₁
    obtain ⟨ws', us, e, rfl, h₂⟩ := h₂
    cases e
    exact ⟨vs, us, rfl, rfl, floatRelAtList_comp hRS ts vs ws us h₁ h₂⟩
  | .variant cs, _, _, _, h₁, h₂ => by
    obtain ⟨i, p, p', rfl, rfl, h₁⟩ := h₁
    obtain ⟨i', p'', p''', e, rfl, h₂⟩ := h₂
    cases e
    exact ⟨i, p, p''', rfl, rfl, floatRelAtCase_comp hRS cs i p p' p''' h₁ h₂⟩
  | .bool, _, _, _, h₁, h₂ | .s8, _, _, _, h₁, h₂ | .u8, _, _, _, h₁, h₂
  | .s16, _, _, _, h₁, h₂ | .u16, _, _, _, h₁, h₂ | .s32, _, _, _, h₁, h₂
  | .u32, _, _, _, h₁, h₂ | .s64, _, _, _, h₁, h₂ | .u64, _, _, _, h₁, h₂
  | .char, _, _, _, h₁, h₂ => Eq.trans h₁ h₂

theorem floatRelAtList_comp (hRS : ∀ f x y z, R f x y → S f y z → T f x z) :
    ∀ (ts : List ValTy) (a b c : List IVal),
    FloatRelAtList R ts a b → FloatRelAtList S ts b c → FloatRelAtList T ts a c
  | [], _, _, _, h₁, h₂ => ⟨h₁.1, h₂.2⟩
  | t :: ts, _, _, _, h₁, h₂ => by
    obtain ⟨v, vs, w, ws, rfl, rfl, hv, hvs⟩ := h₁
    obtain ⟨w', ws', u, us, e, rfl, hw, hws⟩ := h₂
    cases e
    exact ⟨v, vs, u, us, rfl, rfl, floatRelAt_comp hRS t v w u hv hw,
      floatRelAtList_comp hRS ts vs ws us hvs hws⟩

theorem floatRelAtCase_comp (hRS : ∀ f x y z, R f x y → S f y z → T f x z) :
    ∀ (cs : List (Option ValTy)) (i : Nat) (a b c : Option IVal),
    FloatRelAtCase R cs i a b → FloatRelAtCase S cs i b c → FloatRelAtCase T cs i a c
  | [], _, _, _, _, h₁, h₂ => Eq.trans h₁ h₂
  | c :: _, 0, a, b, d, h₁, h₂ => floatRelAtOpt_comp hRS c a b d h₁ h₂
  | _ :: cs, i + 1, a, b, d, h₁, h₂ => floatRelAtCase_comp hRS cs i a b d h₁ h₂

theorem floatRelAtOpt_comp (hRS : ∀ f x y z, R f x y → S f y z → T f x z) :
    ∀ (c : Option ValTy) (a b d : Option IVal),
    FloatRelAtOpt R c a b → FloatRelAtOpt S c b d → FloatRelAtOpt T c a d
  | none, _, _, _, h₁, h₂ => ⟨h₁.1, h₂.2⟩
  | some t, _, _, _, h₁, h₂ => by
    obtain ⟨v, w, rfl, rfl, h₁⟩ := h₁
    obtain ⟨w', u, e, rfl, h₂⟩ := h₂
    cases e
    exact ⟨v, u, rfl, rfl, floatRelAt_comp hRS t v w u h₁ h₂⟩
end

end Comp

/-! ## Inverting the lowering -/

/-- A padding zero is related to itself only. -/
theorem flatRel1_zero (prof : ProfileKind) (t : NumType) (y : Flat)
    (h : FlatRel1 (NanLowerQ prof) (Silmaril.Wasm.Execution.Runtime.Value.zero t) y) :
    y = Silmaril.Wasm.Execution.Runtime.Value.zero t := by
  rcases t with w | f
  · exact h.int_eq rfl
  · change FlatRel1 (NanLowerQ prof) ⟨.float f, 0⟩ y at h
    cases h with
    | float _ _ y hq =>
      rcases hq with rfl | hq
      · rfl
      · have hn : isNaN f 0 = false := by cases f <;> decide
        rw [nanLower_eq_of_not_isNaN hq hn]
        rfl

theorem fitNil_inv (prof : ProfileKind) : ∀ (ws : List NumType) (out : List Flat),
    FlatRel (NanLowerQ prof) (Flat.fit ws []) out → out = Flat.fit ws []
  | [], _, h => by cases h; rfl
  | w :: ws, _, h => by
    cases h with
    | cons hd htl => rw [flatRel1_zero prof w _ hd, fitNil_inv prof ws _ htl]; rfl

theorem flatRel_int_eq {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop} :
    ∀ {fl out : List Flat} {ws : List NumType}, fl.map (·.type) = ws → IntFlat ws →
      FlatRel R fl out → out = fl
  | [], [], _, _, _, .nil => rfl
  | a :: fl, b :: out, ws, hty, hi, .cons hab hrest => by
    cases ws with
    | nil => simp at hty
    | cons w ws =>
      simp only [List.map_cons, List.cons.injEq] at hty
      have hw := hi w List.mem_cons_self
      have hb : b = a := by
        rcases hw with rfl | rfl
        · exact hab.int_eq hty.1
        · exact hab.int_eq hty.1
      rw [hb, flatRel_int_eq hty.2 (fun x hx => hi x (List.mem_cons_of_mem _ hx)) hrest]

/-- **Inverting `Flat.fit`**: re-chosen joined slots are the fit of re-chosen case slots. -/
theorem fit_inv (prof : ProfileKind) : ∀ (hs ws : List NumType) (fl out : List Flat),
    fl.map (·.type) = hs → JDom hs ws → FlatRel (NanLowerQ prof) (Flat.fit ws fl) out →
      ∃ fl', FlatRel (NanLowerQ prof) fl fl' ∧ out = Flat.fit ws fl'
  | [], ws, fl, out, hfl, _, h => by
    have h0 : fl = [] := List.map_eq_nil_iff.mp hfl
    subst h0
    exact ⟨[], .nil, fitNil_inv prof ws out h⟩
  | _ :: _, [], _, _, _, hd, _ => hd.elim
  | _ :: _, _ :: _, [], _, hfl, _, _ => by simp at hfl
  | h :: hs, w :: ws, v :: fl, out, hfl, ⟨hhw, hd⟩, hrel => by
    simp only [List.map_cons, List.cons.injEq] at hfl
    cases hrel with
    | cons hy hrest =>
      rename_i y out'
      obtain ⟨fl', hfl', rfl⟩ := fit_inv prof hs ws fl out' hfl.2 hd hrest
      rcases w with iw | f
      · have hy' := hy.int_eq rfl
        exact ⟨v :: fl', .cons (FlatRel1.refl (fun _ _ => .inl rfl) v) hfl', by rw [hy']; rfl⟩
      · have hv : v.type = .float f := hfl.1.trans (slotOk_float (hfl.1 ▸ hhw))
        have hself : Flat.retype (.float f) v = v := by rw [← hv]; exact retype_self v
        rw [hself] at hy
        have hyt : y.type = .float f := hy.type_eq.trans hv
        refine ⟨y :: fl', .cons hy hfl', ?_⟩
        show y :: Flat.fit ws fl' = Flat.retype (.float f) y :: Flat.fit ws fl'
        rw [← hyt, retype_self]

/-- One float slot. -/
theorem float_inv {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop} {f : FloatType}
    {x : BitVec f.width} {out : List Flat} (h : FlatRel R [⟨.float f, x⟩] out) :
    ∃ y, out = [⟨.float f, y⟩] ∧ R f x y := by
  cases h with
  | cons hd htl =>
    cases htl
    cases hd with
    | float _ _ y hy => exact ⟨y, rfl, hy⟩

/-- A scalar other than a float lowers to integers only. -/
theorem scalar_inv {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop} {t : ValTy}
    {v : IVal} {out : List Flat} (hc : t.check v = true) (hff : floatFree t = true)
    (h : FlatRel R (t.lower v) out) : out = t.lower v :=
  flatRel_int_eq (refLower_types t v hc) (flat_int t hff) h

mutual
/-- **Inverting the lowering**: re-chosen float slots of `t.lower v` are the lowering of a
related value. -/
theorem lower_inv (prof : ProfileKind) : ∀ (t : ValTy) (v : IVal) (out : List Flat),
    t.check v = true → FlatRel (NanLowerQ prof) (t.lower v) out →
      ∃ v', FloatRelAt (NanLowerQ prof) t v v' ∧ t.check v' = true ∧ out = t.lower v'
  | t, v, out, hc, h => by
    cases t <;> cases v <;>
      first
        | (simp only [ValTy.check, Bool.false_eq_true] at hc; done)
        | exact ⟨_, rfl, hc, scalar_inv hc rfl h⟩
        | (obtain ⟨y, rfl, hy⟩ := float_inv h
           exact ⟨_, ⟨_, y, rfl, rfl, hy⟩, rfl, rfl⟩)
        | (obtain ⟨vs', hr, hc', rfl⟩ := lowerList_inv prof _ _ out
             (by simpa only [ValTy.check] using hc) h
           exact ⟨.record vs', ⟨_, vs', rfl, rfl, hr⟩, by simpa only [ValTy.check] using hc', rfl⟩)
        | exact variant_inv prof _ _ _ out hc h

theorem variant_inv (prof : ProfileKind) : ∀ (cs : List (Option ValTy)) (i : Nat)
    (pl : Option IVal) (out : List Flat), (decide (i < 2 ^ 32) && ValTy.checkCase cs i pl) = true →
      FlatRel (NanLowerQ prof) (ValTy.lower (.variant cs) (.variant i pl)) out →
        ∃ v', FloatRelAt (NanLowerQ prof) (.variant cs) (.variant i pl) v' ∧
          (ValTy.variant cs).check v' = true ∧ out = (ValTy.variant cs).lower v'
  | cs, i, pl, out, hc, h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨c, hcs, hco⟩ := checkCase_some cs i pl hc.2
    simp only [ValTy.lower] at h
    cases h with
    | cons hd htl =>
      rename_i y out'
      have hy := hd.int_eq rfl
      subst hy
      obtain ⟨fl', hfl', rfl⟩ := fit_inv prof _ _ _ _ (lowerCase_types cs i c pl hcs hco)
        (jdom_case cs i c hcs) htl
      obtain ⟨pl', hr, hc', rfl⟩ := lowerCase_inv prof cs i pl fl' hc.2 hfl'
      refine ⟨.variant i pl', ⟨i, pl, pl', rfl, rfl, hr⟩, ?_, rfl⟩
      simp only [ValTy.check, hc.1, decide_true, hc', Bool.and_self]

theorem lowerList_inv (prof : ProfileKind) : ∀ (ts : List ValTy) (vs : List IVal)
    (out : List Flat), ValTy.checkList ts vs = true →
      FlatRel (NanLowerQ prof) (ValTy.lowerList ts vs) out →
        ∃ vs', FloatRelAtList (NanLowerQ prof) ts vs vs' ∧ ValTy.checkList ts vs' = true ∧
          out = ValTy.lowerList ts vs'
  | [], [], out, _, h => by cases h; exact ⟨[], ⟨rfl, rfl⟩, rfl, rfl⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, out, hc, h => by
    simp only [ValTy.checkList, Bool.and_eq_true] at hc
    simp only [ValTy.lowerList] at h
    obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := flatRel_append_left h
    obtain ⟨v', hv, hcv, rfl⟩ := lower_inv prof t v l₁ hc.1 h₁
    obtain ⟨vs', hvs, hcvs, rfl⟩ := lowerList_inv prof ts vs l₂ hc.2 h₂
    refine ⟨v' :: vs', ⟨v, vs, v', vs', rfl, rfl, hv, hvs⟩, ?_, rfl⟩
    simp only [ValTy.checkList, hcv, hcvs, Bool.and_self]

theorem lowerCase_inv (prof : ProfileKind) : ∀ (cs : List (Option ValTy)) (i : Nat)
    (pl : Option IVal) (out : List Flat), ValTy.checkCase cs i pl = true →
      FlatRel (NanLowerQ prof) (ValTy.lowerCase cs i pl) out →
        ∃ pl', FloatRelAtCase (NanLowerQ prof) cs i pl pl' ∧ ValTy.checkCase cs i pl' = true ∧
          out = ValTy.lowerCase cs i pl'
  | [], _, _, _, h, _ => by simp [ValTy.checkCase] at h
  | c :: _, 0, pl, out, hc, h => lowerOpt_inv prof c pl out hc h
  | _ :: cs, i + 1, pl, out, hc, h => lowerCase_inv prof cs i pl out hc h

theorem lowerOpt_inv (prof : ProfileKind) : ∀ (c : Option ValTy) (pl : Option IVal)
    (out : List Flat), ValTy.checkOpt c pl = true →
      FlatRel (NanLowerQ prof) (ValTy.lowerOpt c pl) out →
        ∃ pl', FloatRelAtOpt (NanLowerQ prof) c pl pl' ∧ ValTy.checkOpt c pl' = true ∧
          out = ValTy.lowerOpt c pl'
  | none, none, out, _, h => by cases h; exact ⟨none, ⟨rfl, rfl⟩, rfl, rfl⟩
  | some t, some v, out, hc, h => by
    obtain ⟨v', hv, hcv, rfl⟩ := lower_inv prof t v out hc h
    exact ⟨some v', ⟨v, v', rfl, rfl, hv⟩, hcv, rfl⟩
  | none, some _, _, h, _ | some _, none, _, h, _ => by simp [ValTy.checkOpt] at h
end

/-! ## Lowering -/

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {σ : Type}

/-- The admissible lowerings of `v` at `t` (floats in variant payloads included), lowered. -/
def LowOutV (prof : ProfileKind) (t : ValTy) (v : IVal) (out : List Flat) : Prop :=
  ∃ v', NanAtV prof t v v' ∧ t.check v' = true ∧ out = t.lower v'

/-- The admissible lowerings of `vs` at `ts`, lowered. -/
def LowOutVList (prof : ProfileKind) (ts : List ValTy) (vs : List IVal) (out : List Flat) :
    Prop :=
  ∃ vs', NanAtVList prof ts vs vs' ∧ ValTy.checkList ts vs' = true ∧
    out = ValTy.lowerList ts vs'

/-- The admissible lowerings of the payload of case `i`, lowered. -/
def LowOutVCase (prof : ProfileKind) (cs : List (Option ValTy)) (i : Nat) (pl : Option IVal)
    (out : List Flat) : Prop :=
  ∃ pl', FloatRelAtCase (NanLower prof) cs i pl pl' ∧ ValTy.checkCase cs i pl' = true ∧
    out = ValTy.lowerCase cs i pl'

theorem lowOutV_cons {prof : ProfileKind} {t : ValTy} {ts : List ValTy} {v : IVal}
    {vs : List IVal} {a b : List Flat} (ha : LowOutV prof t v a)
    (hb : LowOutVList prof ts vs b) : LowOutVList prof (t :: ts) (v :: vs) (a ++ b) := by
  obtain ⟨v', hn, hc, rfl⟩ := ha
  obtain ⟨vs', hn', hc', rfl⟩ := hb
  refine ⟨v' :: vs', ⟨v, vs, v', vs', rfl, rfl, hn, hn'⟩, ?_, rfl⟩
  simp only [ValTy.checkList, hc, hc', Bool.and_self]

variable (lim : Limits) (q : Quirks) (cx : Silmaril.Wasm.Component.Runtime.LiftLowerContext E)
  (p : Silmaril.Wasm.AddrType)

/-- The payload of the case has been lowered, the joined slots are re-chosen. -/
theorem variant_coerceV (prof : ProfileKind) {cs : List (Option ValTy)} {i : Nat}
    {pl : Option IVal} {c : Option ValTy} (hi : i < 2 ^ 32) (hc : cs[i]? = some c) (fl : List Flat)
    (hfl : LowOutVCase prof cs i pl fl) :
    ChoiceProg prof (LowOutV prof (.variant cs) (.variant i pl))
      ((do
        let (coerced, rest) ← coerceLowerSlots (ValTy.flatOpt c) (ValTy.flatCases cs) fl
        pure (coerced ++ rest.map Silmaril.Wasm.Execution.Runtime.Value.zero)) >>= fun r =>
          pure (i32Flat i :: r) : P E σ _) := by
  obtain ⟨pl', hr, hc', rfl⟩ := hfl
  obtain ⟨c', hc'', hco⟩ := checkCase_some cs i pl' hc'
  rw [hc] at hc''
  cases hc''
  refine (coerceLowerSlots_choice prof _ _ _ (lowerCase_types cs i c pl' hc hco)
    (jdom_case cs i c hc)).bind fun r ⟨fl', hrel, hr'⟩ => ?_
  obtain ⟨pl'', hr₂, hc₂, rfl⟩ := lowerCase_inv prof cs i pl' fl' hc' hrel
  refine .pure ⟨.variant i pl'', ⟨i, pl, pl'', rfl, rfl,
    floatRelAtCase_comp (R := NanLower prof) (S := NanLowerQ prof) (T := NanLower prof)
      (fun _ _ _ _ h₁ h₂ => nanLower_trans_q h₁ h₂) cs i pl pl' pl'' hr hr₂⟩,
    ?_, ?_⟩
  · simp only [ValTy.check, hi, decide_true, hc₂, Bool.and_self]
  · rw [hr']
    rfl

mutual
/-- **Reference `lower_flat` with floats at every type** chooses an admissible lowering. -/
theorem lowerAtV (prof : ProfileKind) : ∀ (t : ValTy) (v : IVal), t.check v = true →
    ChoiceProg prof (LowOutV prof t v)
      (lowerFlatAt lim q cx p (toRefVal v) (toClosed t) : P E σ _)
  | t, v, h => by
    cases t <;> cases v <;>
      first
        | (simp only [ValTy.check, Bool.false_eq_true] at h; done)
        | (rw [lowerFlatAt_toClosed lim q cx p _ _ rfl h]
           exact .pure ⟨_, rfl, h, rfl⟩)
        | (rename_i x
           have e : (lowerFlatAt lim q cx p (toRefVal (.f32 x)) (toClosed .f32) : P E σ _) =
               lowerFloat .f32 x >>= fun y => pure [⟨.float .f32, y⟩] := rfl
           rw [e]
           exact (lowerFloat_choice prof .f32 x).bind fun y hy =>
             .pure ⟨.f32 y, ⟨x, y, rfl, rfl, hy⟩, rfl, rfl⟩)
        | (rename_i x
           have e : (lowerFlatAt lim q cx p (toRefVal (.f64 x)) (toClosed .f64) : P E σ _) =
               lowerFloat .f64 x >>= fun y => pure [⟨.float .f64, y⟩] := rfl
           rw [e]
           exact (lowerFloat_choice prof .f64 x).bind fun y hy =>
             .pure ⟨.f64 y, ⟨x, y, rfl, rfl, hy⟩, rfl, rfl⟩)
        | (rename_i ts vs
           have ih := lowerFieldsV prof ts vs (labels "f" (toClosedList ts))
             (labels_map_snd "f" _) (by simpa only [ValTy.check] using h)
           exact ih.mono fun _ ⟨vs', hn, hc, he⟩ =>
             ⟨.record vs', ⟨vs, vs', rfl, rfl, hn⟩, by simpa only [ValTy.check] using hc, he⟩)
        | exact lowerVariantV prof _ _ _ h

theorem lowerVariantV (prof : ProfileKind) : ∀ (cs : List (Option ValTy)) (i : Nat)
    (pl : Option IVal), (decide (i < 2 ^ 32) && ValTy.checkCase cs i pl) = true →
      ChoiceProg prof (LowOutV prof (.variant cs) (.variant i pl))
        (lowerFlatAt lim q cx p (toRefVal (.variant i pl)) (toClosed (.variant cs)) : P E σ _)
  | cs, i, pl, h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨c, hc, -⟩ := checkCase_some cs i pl h.2
    have hlen : i < (labels "c" (toClosedCases cs)).length := by
      simp only [labels, List.length_mapIdx, toClosedCases_length]
      exact (List.getElem?_eq_some_iff.mp hc).1
    have hpay := lowerCaseV prof cs (labels "c" (toClosedCases cs)) i pl (labels_map_snd "c" _)
      h.2
    simp only [toRefVal, toClosed, lowerFlatAt, lowerFlatVariantWith, hlen, ↓reduceIte,
      flattenCases_toClosed p cs _ (labels_map_snd "c" _), caseFlat_eq p (labels_map_snd "c" _) hc]
    have e : ∀ (pr : P E σ (List Flat)), (do
          let fl ← pr
          let (coerced, rest) ← coerceLowerSlots (ValTy.flatOpt c) (ValTy.flatCases cs) fl
          pure (i32Flat i :: (coerced ++ rest.map Silmaril.Wasm.Execution.Runtime.Value.zero))) =
        pr >>= fun fl => (do
          let (coerced, rest) ← coerceLowerSlots (ValTy.flatOpt c) (ValTy.flatCases cs) fl
          pure (coerced ++ rest.map Silmaril.Wasm.Execution.Runtime.Value.zero)) >>= fun r =>
            pure (i32Flat i :: r) := by
      intro pr
      simp only [bind_assoc, pure_bind]
    rw [e]
    exact hpay.bind fun fl hfl => variant_coerceV prof h.1 hc fl hfl

theorem lowerCaseV (prof : ProfileKind) : ∀ (cs : List (Option ValTy))
    (fs : List (String × Option (WIT.ClosedType RtId))) (i : Nat) (pl : Option IVal),
      fs.map Prod.snd = toClosedCases cs → ValTy.checkCase cs i pl = true →
        ChoiceProg prof (LowOutVCase prof cs i pl)
          (lowerFlatCase lim q cx p i (toRefOpt pl) fs : P E σ _)
  | [], _, _, _, _, h => by simp [ValTy.checkCase] at h
  | none :: _, [], _, _, hfs, _ | some _ :: _, [], _, _, hfs, _ => by
    simp [toClosedCases] at hfs
  | none :: cs, (n, u) :: fs, 0, pl, hfs, h => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    cases pl with
    | none => exact .pure ⟨none, ⟨rfl, rfl⟩, rfl, rfl⟩
    | some _ => simp [ValTy.checkCase, ValTy.checkOpt] at h
  | some t :: cs, (n, u) :: fs, 0, pl, hfs, h => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    cases pl with
    | none => simp [ValTy.checkCase, ValTy.checkOpt] at h
    | some v =>
      have h' : t.check v = true := by simpa only [ValTy.checkCase, ValTy.checkOpt] using h
      simp only [toRefOpt, lowerFlatCase, lowerFlatOpt]
      exact (lowerAtV prof t v h').mono fun _ ⟨v', hn, hc, he⟩ =>
        ⟨some v', ⟨v, v', rfl, rfl, hn⟩, hc, he⟩
  | c :: cs, (n, u) :: fs, i + 1, pl, hfs, h => by
    have hfs' : fs.map Prod.snd = toClosedCases cs := by
      cases c <;> simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs <;> exact hfs.2
    simp only [lowerFlatCase]
    exact lowerCaseV prof cs fs i pl hfs' h

/-- `lowerAtV` on record fields. -/
theorem lowerFieldsV (prof : ProfileKind) : ∀ (ts : List ValTy) (vs : List IVal)
    (fs : List (String × WIT.ClosedType RtId)), fs.map Prod.snd = toClosedList ts →
      ValTy.checkList ts vs = true →
        ChoiceProg prof (LowOutVList prof ts vs)
          (lowerFlatFields lim q cx p (toRefVals vs) fs : P E σ _)
  | [], [], [], _, _ => .pure ⟨[], ⟨rfl, rfl⟩, rfl, rfl⟩
  | [], [], _ :: _, h, _ => by simp [toClosedList] at h
  | _ :: _, _, [], h, _ => by simp [toClosedList] at h
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, (n, u) :: fs, hfs, h => by
    have hfs' : u = toClosed t ∧ fs.map Prod.snd = toClosedList ts := by
      simpa only [List.map_cons, toClosedList, List.cons.injEq] using hfs
    have h' : t.check v = true ∧ ValTy.checkList ts vs = true := by
      simpa only [ValTy.checkList, Bool.and_eq_true] using h
    rw [hfs'.1]
    exact (lowerAtV prof t v h'.1).bind fun a ha =>
      (lowerFieldsV prof ts vs fs hfs'.2 h'.2).bind fun b hb =>
        .pure (lowOutV_cons ha hb)
end

/-- `lowerAtV` on argument lists. -/
theorem lowerFlatTypesV (prof : ProfileKind) : ∀ (ts : List ValTy) (vs : List IVal),
    ValTy.checkList ts vs = true →
      ChoiceProg prof (LowOutVList prof ts vs)
        (lowerFlatTypes lim q cx p (toRefVals vs) (toClosedList ts) : P E σ _)
  | [], [], _ => .pure ⟨[], ⟨rfl, rfl⟩, rfl, rfl⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, h => by
    have h' : t.check v = true ∧ ValTy.checkList ts vs = true := by
      simpa only [ValTy.checkList, Bool.and_eq_true] using h
    exact (lowerAtV lim q cx p prof t v h'.1).bind fun a ha =>
      (lowerFlatTypesV prof ts vs h'.2).bind fun b hb => .pure (lowOutV_cons ha hb)

end Silmaril.Proofs.Wasm.Component.Reference
