module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatVLower

/-!
# Floats in variant payloads: the IR lift up to canonicalisation

The reference lift decodes a float payload held in an integer joined slot with
`coerceLiftFlat` (`decodeFloat`, which canonicalises), where the IR re-types the bits
(`Flat.unfit`). The two payload slot lists agree up to the canonicalisation of their float slots
(`FlatRel CanonEq`, `coerceLiftSlots_canon`). This module shows that the IR lift does not see the
difference once its results are canonicalised:

* `lift_canon`: on flat lists related by `FlatRel CanonEq`, `ValTy.lift t` fails on both or
  succeeds on both, with results equal after `canonAtV t` and related remainders.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm (FloatType IntType NumType)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- Float bits equal after canonicalisation. -/
def CanonEq (f : FloatType) (x y : BitVec f.width) : Prop :=
  canonicalizeNaN f x = canonicalizeNaN f y

theorem canonEq_refl (f : FloatType) (x : BitVec f.width) : CanonEq f x x := rfl

/-- Two IR lift results agree up to `canonAtV t`, with related remainders. -/
def LiftCEq (t : ValTy) : Option (IVal × List Flat) → Option (IVal × List Flat) → Prop
  | none, none => True
  | some (w, r), some (w', r') => canonAtV t w = canonAtV t w' ∧ FlatRel CanonEq r r'
  | _, _ => False

/-- `LiftCEq` for lists of values. -/
def LiftsCEq (ts : List ValTy) :
    Option (List IVal × List Flat) → Option (List IVal × List Flat) → Prop
  | none, none => True
  | some (w, r), some (w', r') => canonAtVList ts w = canonAtVList ts w' ∧ FlatRel CanonEq r r'
  | _, _ => False

/-- `LiftCEq` for optional payloads. -/
def OptCEq (c : Option ValTy) : Option (Option IVal) → Option (Option IVal) → Prop
  | none, none => True
  | some o, some o' => canonAtVOpt c o = canonAtVOpt c o'
  | _, _ => False

theorem take_canon : ∀ (ts : List NumType) (r r' : List Flat), FlatRel CanonEq r r' →
    match Flat.take ts r, Flat.take ts r' with
    | none, none => True
    | some (js, q), some (js', q') =>
      js.map (·.type) = ts ∧ FlatRel CanonEq js js' ∧ FlatRel CanonEq q q'
    | _, _ => False
  | [], r, r', h => ⟨rfl, .nil, h⟩
  | _ :: _, [], [], .nil => trivial
  | t :: ts, y :: r, y' :: r', .cons hy hr => by
    have ih := take_canon ts r r' hr
    have hty := hy.type_eq
    simp only [Flat.take, hty]
    by_cases e : y.type = t
    · simp only [e, ↓reduceIte]
      revert ih
      cases Flat.take ts r with
      | none =>
        cases Flat.take ts r' with
        | none => intro; trivial
        | some _ => intro ih; exact (ih : False).elim
      | some a =>
        cases Flat.take ts r' with
        | none => intro ih; exact (ih : False).elim
        | some b =>
          intro ⟨h₁, h₂, h₃⟩
          exact ⟨by simp only [List.map_cons, e, h₁], .cons hy h₂, h₃⟩
    · simp only [e, ↓reduceIte]

/-- Re-typing related slots at case types fitting the joined slots keeps them related. -/
theorem unfit_canon : ∀ (hs ws : List NumType) (js js' : List Flat), js.map (·.type) = ws →
    JDom hs ws → FlatRel CanonEq js js' →
      FlatRel CanonEq (Flat.unfit hs js) (Flat.unfit hs js')
  | [], _, _, _, _, _, _ => by
    simp only [Flat.unfit]
    exact .nil
  | _ :: _, [], _, _, _, hd, _ => hd.elim
  | _ :: _, _ :: _, [], _, _, _, h => by cases h; exact .nil
  | h :: hs, w :: ws, j :: js, j' :: js', hty, ⟨hhw, hd⟩, .cons hj hrest => by
    simp only [List.map_cons, List.cons.injEq] at hty
    refine .cons ?_ (unfit_canon hs ws js js' hty.2 hd hrest)
    rcases w with iw | f
    · rw [hj.int_eq hty.1]
      exact FlatRel1.refl canonEq_refl _
    · have hhf := slotOk_float hhw
      subst hhf
      have hj' : j'.type = .float f := hj.type_eq.trans hty.1
      have e₁ : Flat.retype (.float f) j = j := by rw [← hty.1]; exact retype_self j
      have e₂ : Flat.retype (.float f) j' = j' := by rw [← hj']; exact retype_self j'
      rw [e₁, e₂]
      exact hj

theorem canonAtVCase_some : ∀ {cs : List (Option ValTy)} {i : Nat} {c : Option ValTy}
    (_ : cs[i]? = some c) (o : Option IVal), canonAtVCase cs i o = canonAtVOpt c o
  | [], _, _, hc, _ => by simp at hc
  | _ :: _, 0, _, hc, o => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    rfl
  | _ :: cs, i + 1, c, hc, o => canonAtVCase_some (cs := cs) (i := i) hc o

theorem lift_scalar_canon_int {t : ValTy} (hr : ∀ ts, t ≠ .record ts)
    (hv : ∀ cs, t ≠ .variant cs) {w : IntType} {b : BitVec (NumType.int w).width}
    {r r' : List Flat} (hrest : FlatRel CanonEq r r') :
    LiftCEq t (ValTy.lift t (⟨.int w, b⟩ :: r)) (ValTy.lift t (⟨.int w, b⟩ :: r')) := by
  cases t <;> first
    | exact absurd rfl (hr _)
    | exact absurd rfl (hv _)
    | (cases w <;> first
        | trivial
        | (simp only [ValTy.lift]
           cases charOfBits b <;> trivial))

theorem lift_scalar_canon_float {t : ValTy} (hr : ∀ ts, t ≠ .record ts)
    (hv : ∀ cs, t ≠ .variant cs) {f : FloatType} {x y : BitVec f.width} (hxy : CanonEq f x y)
    {r r' : List Flat} (hrest : FlatRel CanonEq r r') :
    LiftCEq t (ValTy.lift t (⟨.float f, x⟩ :: r)) (ValTy.lift t (⟨.float f, y⟩ :: r')) := by
  cases t <;> first
    | exact absurd rfl (hr _)
    | exact absurd rfl (hv _)
    | (cases f <;> first
        | trivial
        | exact ⟨congrArg Silmaril.Wasm.Component.Val.f32 hxy, hrest⟩
        | exact ⟨congrArg Silmaril.Wasm.Component.Val.f64 hxy, hrest⟩)

/-- An integer scalar or float type lifts its head only. -/
theorem lift_scalar_canon {t : ValTy} (hr : ∀ ts, t ≠ .record ts) (hv : ∀ cs, t ≠ .variant cs)
    {ys ys' : List Flat} (h : FlatRel CanonEq ys ys') :
    LiftCEq t (ValTy.lift t ys) (ValTy.lift t ys') := by
  cases h with
  | nil => cases t <;> first | exact absurd rfl (hr _) | exact absurd rfl (hv _) | trivial
  | cons hy hrest =>
    cases hy with
    | int w b => exact lift_scalar_canon_int hr hv hrest
    | float f x y hxy => exact lift_scalar_canon_float hr hv hxy hrest

mutual
/-- **The IR lift up to canonicalisation.** -/
theorem lift_canon : ∀ (t : ValTy) (ys ys' : List Flat), FlatRel CanonEq ys ys' →
    LiftCEq t (ValTy.lift t ys) (ValTy.lift t ys')
  | .record ts, ys, ys', h => by
    have ih := liftList_canon ts ys ys' h
    simp only [ValTy.lift]
    revert ih
    cases ValTy.liftList ts ys with
    | none =>
      cases ValTy.liftList ts ys' with
      | none => intro; trivial
      | some _ => intro ih; exact (ih : False).elim
    | some a =>
      cases ValTy.liftList ts ys' with
      | none => intro ih; exact (ih : False).elim
      | some b =>
        intro ⟨h₁, h₂⟩
        exact ⟨by simp only [canonAtV, h₁], h₂⟩
  | .variant cs, ys, ys', h => variant_canon cs ys ys' h
  | .bool, _, _, h | .s8, _, _, h | .u8, _, _, h | .s16, _, _, h | .u16, _, _, h
  | .s32, _, _, h | .u32, _, _, h | .s64, _, _, h | .u64, _, _, h | .f32, _, _, h
  | .f64, _, _, h | .char, _, _, h =>
    lift_scalar_canon (fun _ e => by cases e) (fun _ e => by cases e) h

theorem variant_canon : ∀ (cs : List (Option ValTy)) (ys ys' : List Flat),
    FlatRel CanonEq ys ys' →
      LiftCEq (.variant cs) (ValTy.lift (.variant cs) ys) (ValTy.lift (.variant cs) ys')
  | cs, ys, ys', h => by
    cases h with
    | nil => trivial
    | cons hy hrest =>
      cases hy with
      | float f x y _ => cases f <;> trivial
      | int w d =>
        cases w with
        | i64 => trivial
        | i32 =>
          rename_i r r'
          have ht := take_canon (ValTy.flatCases cs) r r' hrest
          simp only [ValTy.lift]
          revert ht
          cases Flat.take (ValTy.flatCases cs) r with
          | none =>
            cases Flat.take (ValTy.flatCases cs) r' with
            | none => intro; trivial
            | some _ => intro ih; exact (ih : False).elim
          | some a =>
          cases Flat.take (ValTy.flatCases cs) r' with
          | none => intro ih; exact (ih : False).elim
          | some b =>
          obtain ⟨js, q⟩ := a
          obtain ⟨js', q'⟩ := b
          intro ⟨hty, hjs, hq⟩
          by_cases hlt : d.toNat < cs.length
          · obtain ⟨c, hc⟩ : ∃ c, cs[d.toNat]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
            have hu := unfit_canon (ValTy.flatOpt c) _ js js' hty (jdom_case cs _ c hc) hjs
            have ih := liftCase_canon cs d.toNat c _ _ hc hu
            simp only [liftCase_some cs _ c _ hc]
            revert ih
            cases ValTy.liftOpt c (Flat.unfit (ValTy.flatOpt c) js) with
            | none =>
              cases ValTy.liftOpt c (Flat.unfit (ValTy.flatOpt c) js') with
              | none => intro; trivial
              | some _ => intro ih; exact (ih : False).elim
            | some o =>
              cases ValTy.liftOpt c (Flat.unfit (ValTy.flatOpt c) js') with
              | none => intro ih; exact (ih : False).elim
              | some o' =>
                intro e
                refine ⟨?_, hq⟩
                simp only [canonAtV, canonAtVCase_some hc]
                exact congrArg _ (e : canonAtVOpt c o = canonAtVOpt c o')
          · have hge : cs.length ≤ d.toNat := Nat.le_of_not_lt hlt
            simp only [liftCase_none _ _ _ hge, Option.map_none]
            trivial

theorem liftCase_canon : ∀ (cs : List (Option ValTy)) (i : Nat) (c : Option ValTy)
    (zs zs' : List Flat), cs[i]? = some c → FlatRel CanonEq zs zs' →
      OptCEq c (ValTy.liftOpt c zs) (ValTy.liftOpt c zs')
  | [], _, _, _, _, hc, _ => by simp at hc
  | none :: _, 0, c, _, _, hc, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    rfl
  | some t :: _, 0, c, zs, zs', hc, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    have ih := lift_canon t zs zs' h
    simp only [ValTy.liftOpt]
    revert ih
    cases ValTy.lift t zs with
    | none =>
      cases ValTy.lift t zs' with
      | none => intro; trivial
      | some _ => intro ih; exact ih.elim
    | some pr =>
      cases ValTy.lift t zs' with
      | none => intro ih; exact ih.elim
      | some pr' =>
        obtain ⟨w, r⟩ := pr
        obtain ⟨w', r'⟩ := pr'
        intro ⟨hw, hr⟩
        cases hr with
        | nil => exact congrArg some hw
        | cons _ _ => trivial
  | _ :: cs, i + 1, c, zs, zs', hc, h => liftCase_canon cs i c zs zs' hc h

theorem liftList_canon : ∀ (ts : List ValTy) (ys ys' : List Flat), FlatRel CanonEq ys ys' →
    LiftsCEq ts (ValTy.liftList ts ys) (ValTy.liftList ts ys')
  | [], _, _, h => ⟨rfl, h⟩
  | t :: ts, ys, ys', h => by
    have ih₁ := lift_canon t ys ys' h
    simp only [ValTy.liftList]
    revert ih₁
    cases ValTy.lift t ys with
    | none =>
      cases ValTy.lift t ys' with
      | none => intro; trivial
      | some _ => intro ih; exact ih.elim
    | some pr =>
      cases ValTy.lift t ys' with
      | none => intro ih; exact ih.elim
      | some pr' =>
        obtain ⟨w, r⟩ := pr
        obtain ⟨w', r'⟩ := pr'
        intro ⟨hw, hr⟩
        dsimp only
        have ih₂ := liftList_canon ts r r' hr
        revert ih₂
        cases ValTy.liftList ts r with
        | none =>
          cases ValTy.liftList ts r' with
          | none => intro; trivial
          | some _ => intro ih; exact (ih : False).elim
        | some a =>
          cases ValTy.liftList ts r' with
          | none => intro ih; exact (ih : False).elim
          | some b =>
            intro ⟨h₁, h₂⟩
            exact ⟨by simp only [canonAtVList, hw, h₁], h₂⟩
end

end Silmaril.Proofs.Wasm.Component.Reference
