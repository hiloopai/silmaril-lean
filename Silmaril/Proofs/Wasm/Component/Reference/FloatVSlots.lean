module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatVariant
public import Silmaril.Wasm.Component.Reference.FloatV.Defs
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Floats in variant payloads: slots

Facts about the joined payload slots of variants with floats, for the variant cases of the flat
lowering and lifting with floats (`FloatVLower`, `FloatVLift`):

* `nanLower_trans`: `NanLower prof` is transitive at every profile, so the two C7 choices a
  float in a variant payload may undergo (`lowerFloat`, then `encodeFloat`) are one admissible
  lowering;
* `SlotOk h w`: the case slot type `h` fits the joined slot type `w` (equal, `i32` into `i64`,
  or a float into an integer slot, `FloatSlot`); `JDom` slotwise. Unlike `Dom` it needs no
  integer-only slots (`IntFlat`): `jdom_case` holds for every variant;
* `FlatRel R fl fl'`: the flat values `fl'` are `fl` with the float slots related by `R`;
* `coerceLowerSlots_choice`: the `(have, want)` loop of `lower_flat_variant` followed by zero
  padding is a program of C7 choices ending in `Flat.fit ws fl'` for some `fl'` related to the
  lowered payload `fl` by `NanLowerQ prof` (equal or `NanLower prof`) on the float slots.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Value (NanLower)
open Silmaril.Wasm (FloatType IntType NumType)

/-! ## Transitivity of `NanLower` -/

theorem nanLower_trans_nondet {t : FloatType} {x y z : BitVec t.width}
    (h₁ : NanLower .nondet t x y) (h₂ : NanLower .nondet t y z) : NanLower .nondet t x z := by
  have s₁ : ScrambleNaN false t x y := Silmaril.Wasm.Component.Value.nanLower_nondet_iff.mp h₁
  have s₂ : ScrambleNaN false t y z := Silmaril.Wasm.Component.Value.nanLower_nondet_iff.mp h₂
  refine Silmaril.Wasm.Component.Value.nanLower_nondet_iff.mpr
    ((scrambleNaN_false_iff t x z).mpr ?_)
  rcases (scrambleNaN_false_iff t x y).mp s₁ with ⟨hx, rfl⟩ | ⟨hx, hy⟩
  · exact (scrambleNaN_false_iff _ _ _).mp s₂
  · rcases (scrambleNaN_false_iff t y z).mp s₂ with ⟨hy', _⟩ | ⟨_, hz⟩
    · exact absurd (hy'.symm.trans hy) (by decide)
    · exact .inr ⟨hx, hz⟩

theorem nanLower_trans_refStrict {t : FloatType} {x y z : BitVec t.width}
    (h₁ : NanLower .refStrict t x y) (h₂ : NanLower .refStrict t y z) :
    NanLower .refStrict t x z := by
  obtain ⟨s₁, r₁⟩ := h₁
  obtain ⟨s₂, r₂⟩ := h₂
  rcases (scrambleNaN_false_iff t x y).mp s₁ with ⟨_, rfl⟩ | ⟨hx, hy⟩
  · exact ⟨s₂, r₂⟩
  · rcases (scrambleNaN_false_iff t y z).mp s₂ with ⟨hy', _⟩ | ⟨_, hz⟩
    · exact absurd (hy'.symm.trans hy) (by decide)
    · exact ⟨(scrambleNaN_false_iff t x z).mpr (.inr ⟨hx, hz⟩), fun _ => r₂ hy⟩

theorem nanLower_trans_deterministic {t : FloatType} {x y z : BitVec t.width}
    (h₁ : NanLower .deterministic t x y) (h₂ : NanLower .deterministic t y z) :
    NanLower .deterministic t x z := by
  have e₁ : y = canonicalizeNaN t x := (scrambleNaN_true_iff t x y).mp h₁
  have e₂ : z = canonicalizeNaN t y := (scrambleNaN_true_iff t y z).mp h₂
  have e : z = canonicalizeNaN t x := by rw [e₂, e₁, canonicalizeNaN_idem]
  exact (scrambleNaN_true_iff t x z).mpr e

/-- **`NanLower prof` is transitive** at every profile. -/
theorem nanLower_trans {prof : ProfileKind} {t : FloatType} {x y z : BitVec t.width}
    (h₁ : NanLower prof t x y) (h₂ : NanLower prof t y z) : NanLower prof t x z := by
  cases prof
  · exact nanLower_trans_nondet h₁ h₂
  · exact nanLower_trans_refStrict h₁ h₂
  · exact nanLower_trans_deterministic h₁ h₂

/-- A non-NaN lowers only to itself. -/
theorem nanLower_eq_of_not_isNaN {prof : ProfileKind} {t : FloatType} {x y : BitVec t.width}
    (h : NanLower prof t x y) (hx : isNaN t x = false) : y = x := by
  cases prof
  · simpa only [NanLower, hx, Bool.false_eq_true, ↓reduceIte] using h
  · exact ((scrambleNaN_false_iff t x y).mp h.1).elim (fun h' => h'.2)
      (fun h' => absurd (hx.symm.trans h'.1) (by decide))
  · rw [show y = canonicalizeNaN t x from (scrambleNaN_true_iff t x y).mp h,
      canonicalizeNaN_of_not_isNaN hx]

/-- Equal, or an admissible lowering: a float slot coerced to a slot of its own type is kept. -/
def NanLowerQ (prof : ProfileKind) (f : FloatType) (x y : BitVec f.width) : Prop :=
  x = y ∨ NanLower prof f x y

theorem nanLower_trans_q {prof : ProfileKind} {t : FloatType} {x y z : BitVec t.width}
    (h₁ : NanLower prof t x y) (h₂ : NanLowerQ prof t y z) : NanLower prof t x z := by
  rcases h₂ with rfl | h₂
  · exact h₁
  · exact nanLower_trans h₁ h₂

/-! ## Slots -/

/-- The case slot type `h` fits the joined slot type `w` (the `(have, want)` table of
`lower_flat_variant`, plus the identity). -/
def SlotOk : NumType → NumType → Bool
  | .int .i32, .int .i32 | .int .i32, .int .i64 | .int .i64, .int .i64 => true
  | .float .f32, .float .f32 | .float .f64, .float .f64 => true
  | .float .f32, .int .i32 | .float .f32, .int .i64 | .float .f64, .int .i64 => true
  | _, _ => false

theorem slotOk_refl (x : NumType) : SlotOk x x = true := by
  rcases x with (_ | _) | (_ | _) <;> rfl

theorem slotOk_trans {a b c : NumType} (h₁ : SlotOk a b = true) (h₂ : SlotOk b c = true) :
    SlotOk a c = true := by
  revert h₁ h₂
  rcases a with (_ | _) | (_ | _) <;> rcases b with (_ | _) | (_ | _) <;>
    rcases c with (_ | _) | (_ | _) <;> decide

theorem slotOk_join (x y : NumType) :
    SlotOk x (Silmaril.Wasm.Component.joinType x y) = true ∧
      SlotOk y (Silmaril.Wasm.Component.joinType x y) = true := by
  rcases x with (_ | _) | (_ | _) <;> rcases y with (_ | _) | (_ | _) <;> decide

/-- A float joined slot holds a case slot of the same type only. -/
theorem slotOk_float {h : NumType} {f : FloatType} (hs : SlotOk h (.float f) = true) :
    h = .float f := by
  revert hs
  rcases h with (_ | _) | (_ | _) <;> rcases f with (_ | _) <;> decide

/-- Each slot of `hs` fits the slot of `ws` at the same position; `ws` is at least as long. -/
def JDom : List NumType → List NumType → Prop
  | [], _ => True
  | _ :: _, [] => False
  | h :: hs, w :: ws => SlotOk h w = true ∧ JDom hs ws

theorem JDom.refl : ∀ hs : List NumType, JDom hs hs
  | [] => trivial
  | h :: hs => ⟨slotOk_refl h, JDom.refl hs⟩

theorem JDom.trans : ∀ {a b c : List NumType}, JDom a b → JDom b c → JDom a c
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, _ :: _, ⟨h₁, hab⟩, ⟨h₂, hbc⟩ => ⟨slotOk_trans h₁ h₂, JDom.trans hab hbc⟩

theorem JDom.length_le : ∀ {hs ws : List NumType}, JDom hs ws → hs.length ≤ ws.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, ⟨_, hd⟩ => Nat.succ_le_succ (JDom.length_le hd)

theorem jdom_joinFlat : ∀ a b : List NumType,
    JDom a (Silmaril.Wasm.Component.joinFlat a b) ∧ JDom b (Silmaril.Wasm.Component.joinFlat a b)
  | [], b => ⟨trivial, JDom.refl b⟩
  | _ :: _, [] => ⟨JDom.refl _, trivial⟩
  | x :: a, y :: b =>
    ⟨⟨(slotOk_join x y).1, (jdom_joinFlat a b).1⟩, ⟨(slotOk_join x y).2, (jdom_joinFlat a b).2⟩⟩

/-- **The payload slots of case `i` fit the joined slots**, for every variant. -/
theorem jdom_case : ∀ (cs : List (Option ValTy)) (i : Nat) (c : Option ValTy),
    cs[i]? = some c → JDom (ValTy.flatOpt c) (ValTy.flatCases cs)
  | [], _, _, h => by simp at h
  | c' :: cs, 0, c, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact (jdom_joinFlat _ _).1
  | c' :: cs, i + 1, c, h => by
    simp only [List.getElem?_cons_succ] at h
    exact (jdom_case cs i c h).trans (jdom_joinFlat _ _).2

/-! ## Flat values related on their floats -/

/-- One flat value related to another: the same integer, or floats of the same type related by
`R`. -/
inductive FlatRel1 (R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop) :
    Flat → Flat → Prop where
  | int (w : IntType) (b : BitVec (NumType.int w).width) : FlatRel1 R ⟨.int w, b⟩ ⟨.int w, b⟩
  | float (f : FloatType) (x y : BitVec f.width) : R f x y → FlatRel1 R ⟨.float f, x⟩ ⟨.float f, y⟩

/-- `FlatRel1` slotwise. -/
abbrev FlatRel (R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop) :
    List Flat → List Flat → Prop :=
  List.Forall₂ (FlatRel1 R)

theorem FlatRel1.type_eq {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop}
    {a b : Flat} (h : FlatRel1 R a b) : b.type = a.type := by
  cases h <;> rfl

theorem FlatRel1.refl {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop}
    (hR : ∀ f x, R f x x) : ∀ a : Flat, FlatRel1 R a a
  | ⟨.int w, b⟩ => .int w b
  | ⟨.float f, x⟩ => .float f x x (hR f x)

theorem FlatRel.refl {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop}
    (hR : ∀ f x, R f x x) : ∀ fl : List Flat, FlatRel R fl fl
  | [] => .nil
  | a :: fl => .cons (FlatRel1.refl hR a) (FlatRel.refl hR fl)

/-- An integer is related to itself only. -/
theorem FlatRel1.int_eq {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop}
    {a b : Flat} {w : IntType} (ha : a.type = .int w) (h : FlatRel1 R a b) : b = a := by
  cases h with
  | int => rfl
  | float => cases ha

theorem flatRel_append_left {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop} :
    ∀ {a b l : List Flat}, FlatRel R (a ++ b) l →
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ FlatRel R a l₁ ∧ FlatRel R b l₂
  | [], _, l, h => ⟨[], l, rfl, .nil, h⟩
  | x :: a, b, _, .cons hx h => by
    obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := flatRel_append_left h
    exact ⟨_ :: l₁, l₂, rfl, .cons hx h₁, h₂⟩

theorem flatRel_types {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop} :
    ∀ {a b : List Flat}, FlatRel R a b → b.map (·.type) = a.map (·.type)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, h.type_eq, flatRel_types hs]

/-! ## Coercing lowered payload slots -/

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {σ : Type}

/-- **The coercion of one lowered payload slot** chooses a `NanLowerQ` image and re-types it. -/
theorem coerceLower_choice (prof : ProfileKind) {h w : NumType} {v : Flat} (hv : v.type = h)
    (hs : SlotOk h w = true) :
    ChoiceProg prof (fun out => ∃ v', FlatRel1 (NanLowerQ prof) v v' ∧ out = Flat.retype w v')
      (coerceLower h w v : P E σ Flat) := by
  obtain ⟨t, b⟩ := v
  simp only at hv
  subst hv
  have hpure : (coerceLower t t ⟨t, b⟩ : P E σ Flat) = pure ⟨t, b⟩ := by
    rcases t with (_ | _) | (_ | _) <;> rfl
  have hrefl := FlatRel1.refl (R := NanLowerQ prof) (fun _ _ => .inl rfl)
  rcases t with (_ | _) | (_ | _) <;> rcases w with (_ | _) | (_ | _) <;>
    try first
      | (simp only [SlotOk, Bool.false_eq_true] at hs; done)
      | (rw [hpure]; exact .pure ⟨_, hrefl _, (retype_self _).symm⟩)
  · rw [coerceLower_eq (E := E) (σ := σ) (v := ⟨.int .i32, b⟩) rfl (.inr ⟨rfl, rfl⟩) (.inl rfl)]
    exact .pure ⟨_, hrefl _, rfl⟩
  · exact (coerceLower_float prof (t := .f32) (w := .i32) trivial b).mono
      fun out ⟨y, hy, he⟩ => ⟨_, .float .f32 b y (.inr hy), he⟩
  · exact (coerceLower_float prof (t := .f32) (w := .i64) trivial b).mono
      fun out ⟨y, hy, he⟩ => ⟨_, .float .f32 b y (.inr hy), he⟩
  · exact (coerceLower_float prof (t := .f64) (w := .i64) trivial b).mono
      fun out ⟨y, hy, he⟩ => ⟨_, .float .f64 b y (.inr hy), he⟩

/-- **The `(have, want)` loop of `lower_flat_variant` followed by zero padding** chooses
`NanLowerQ` images of the float slots and fits the result into the joined slots. -/
theorem coerceLowerSlots_choice (prof : ProfileKind) : ∀ (hs ws : List NumType) (fl : List Flat),
    fl.map (·.type) = hs → JDom hs ws →
      ChoiceProg prof (fun out => ∃ fl', FlatRel (NanLowerQ prof) fl fl' ∧ out = Flat.fit ws fl')
        ((do
          let (coerced, rest) ← coerceLowerSlots hs ws fl
          pure (coerced ++ rest.map Silmaril.Wasm.Execution.Runtime.Value.zero)) : P E σ _)
  | [], ws, fl, hfl, _ => by
    have h0 : fl = [] := List.map_eq_nil_iff.mp hfl
    subst h0
    have e : ((do
          let (coerced, rest) ← coerceLowerSlots [] ws []
          pure (coerced ++ rest.map Silmaril.Wasm.Execution.Runtime.Value.zero)) : P E σ _) =
        pure (Flat.fit ws []) := by
      cases ws <;> simp only [coerceLowerSlots, pure_bind, List.nil_append, fit_nil]
    rw [e]
    exact .pure ⟨[], .nil, rfl⟩
  | _ :: _, [], _, _, hd => hd.elim
  | h :: hs, w :: ws, [], hfl, _ => by simp at hfl
  | h :: hs, w :: ws, v :: fl, hfl, ⟨hhw, hd⟩ => by
    simp only [List.map_cons, List.cons.injEq] at hfl
    have e : ((do
          let (coerced, rest) ← coerceLowerSlots (h :: hs) (w :: ws) (v :: fl)
          pure (coerced ++ rest.map Silmaril.Wasm.Execution.Runtime.Value.zero)) : P E σ _) =
        coerceLower h w v >>= fun v' => (do
          let x ← coerceLowerSlots hs ws fl
          pure (x.1 ++ x.2.map Silmaril.Wasm.Execution.Runtime.Value.zero)) >>= fun r =>
            pure (v' :: r) := by
      simp only [coerceLowerSlots, bind_assoc, pure_bind, List.cons_append]
    rw [e]
    exact (coerceLower_choice prof hfl.1 hhw).bind fun a ⟨v', hv', ha⟩ =>
      (coerceLowerSlots_choice prof hs ws fl hfl.2 hd).bind fun b ⟨fl', hfl', hb⟩ =>
        .pure ⟨v' :: fl', .cons hv' hfl', by rw [ha, hb]; rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference
