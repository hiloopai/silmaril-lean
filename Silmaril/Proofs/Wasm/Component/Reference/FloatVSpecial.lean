module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatVLift

/-!
# Floats in variant payloads: the old relations as special cases

On types with floats only outside variant payloads (`floatOk`), the relations of
`Reference.FloatV` are those of `Reference.Sound` (`FloatABI`):

* `canonAtV_eq_canonAt`, `canonAtVList_eq_canonAtList`: `canonAtV` is `canonAt`;
* `nanAtV_of_nanAt`, `nanAtVList_of_nanAtList`: for well-typed `v`, `NanAt` implies `NanAtV`
  (variant payloads are float-free, related to themselves: `floatRelAt_refl_free`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm (FloatType)
open Silmaril.Wasm.Component (ProfileKind)

local notation "IVal" => Silmaril.Wasm.Component.Val

mutual
theorem canonAtV_free : ∀ (t : ValTy) (v : IVal), floatFree t = true → canonAtV t v = v
  | t, v, hf => by
    cases t <;> cases v <;> first
      | (simp only [floatFree, Bool.false_eq_true] at hf; done)
      | rfl
      | exact congrArg Val.record (canonAtVList_free _ _ (by simpa only [floatFree] using hf))
      | exact congrArg (Val.variant _)
          (canonAtVCase_free _ _ _ (by simpa only [floatFree] using hf))

theorem canonAtVList_free : ∀ (ts : List ValTy) (vs : List IVal), floatFreeList ts = true →
    canonAtVList ts vs = vs
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | t :: ts, v :: vs, hf => by
    have hf' : floatFree t = true ∧ floatFreeList ts = true := by
      simpa only [floatFreeList, Bool.and_eq_true] using hf
    exact congrArg₂ List.cons (canonAtV_free t v hf'.1) (canonAtVList_free ts vs hf'.2)

theorem canonAtVCase_free : ∀ (cs : List (Option ValTy)) (i : Nat) (p : Option IVal),
    floatFreeCases cs = true → canonAtVCase cs i p = p
  | [], _, _, _ => rfl
  | none :: _, 0, none, _ | none :: _, 0, some _, _ | some _ :: _, 0, none, _ => rfl
  | some t :: _, 0, some v, hf => by
    have hf' : floatFree t = true := by
      simp only [floatFreeCases, Bool.and_eq_true] at hf
      exact hf.1
    exact congrArg some (canonAtV_free t v hf')
  | none :: cs, i + 1, p, hf => canonAtVCase_free cs i p hf
  | some _ :: cs, i + 1, p, hf => by
    have hf' : floatFreeCases cs = true := by
      simp only [floatFreeCases, Bool.and_eq_true] at hf
      exact hf.2
    exact canonAtVCase_free cs i p hf'
end

mutual
/-- **`canonAtV` is `canonAt`** where floats occur only outside variant payloads. -/
theorem canonAtV_eq_canonAt : ∀ (t : ValTy) (v : IVal), floatOk t = true →
    canonAtV t v = canonAt t v
  | t, v, hf => by
    cases t <;> cases v <;> first
      | rfl
      | exact congrArg Val.record
          (canonAtVList_eq_canonAtList _ _ (by simpa only [floatOk] using hf))
      | exact canonAtV_free (.variant _) _ (by simpa only [floatOk, floatFree] using hf)

/-- `canonAtV_eq_canonAt` on lists. -/
theorem canonAtVList_eq_canonAtList : ∀ (ts : List ValTy) (vs : List IVal),
    floatOkList ts = true → canonAtVList ts vs = canonAtList ts vs
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | t :: ts, v :: vs, hf => by
    have hf' : floatOk t = true ∧ floatOkList ts = true := by
      simpa only [floatOkList, Bool.and_eq_true] using hf
    exact congrArg₂ List.cons (canonAtV_eq_canonAt t v hf'.1)
      (canonAtVList_eq_canonAtList ts vs hf'.2)
end

section Refl

variable {R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop}

mutual
/-- A float-free type relates a well-typed value to itself. -/
theorem floatRelAt_refl_free : ∀ (t : ValTy) (v : IVal), floatFree t = true →
    t.check v = true → FloatRelAt R t v v
  | t, v, hf, hc => by
    cases t <;> cases v <;> first
      | (simp only [floatFree, Bool.false_eq_true] at hf; done)
      | (simp only [ValTy.check, Bool.false_eq_true] at hc; done)
      | exact rfl
      | exact ⟨_, _, rfl, rfl, floatRelAtList_refl_free _ _ (by simpa only [floatFree] using hf)
          (by simpa only [ValTy.check] using hc)⟩
      | exact ⟨_, _, _, rfl, rfl, floatRelAtCase_refl_free _ _ _
          (by simpa only [floatFree] using hf)
          (by simp only [ValTy.check, Bool.and_eq_true] at hc; exact hc.2)⟩

theorem floatRelAtList_refl_free : ∀ (ts : List ValTy) (vs : List IVal),
    floatFreeList ts = true → ValTy.checkList ts vs = true → FloatRelAtList R ts vs vs
  | [], [], _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, hf, hc => by
    have hf' : floatFree t = true ∧ floatFreeList ts = true := by
      simpa only [floatFreeList, Bool.and_eq_true] using hf
    have hc' : t.check v = true ∧ ValTy.checkList ts vs = true := by
      simpa only [ValTy.checkList, Bool.and_eq_true] using hc
    exact ⟨v, vs, v, vs, rfl, rfl, floatRelAt_refl_free t v hf'.1 hc'.1,
      floatRelAtList_refl_free ts vs hf'.2 hc'.2⟩

theorem floatRelAtCase_refl_free : ∀ (cs : List (Option ValTy)) (i : Nat) (p : Option IVal),
    floatFreeCases cs = true → ValTy.checkCase cs i p = true → FloatRelAtCase R cs i p p
  | [], _, _, _, h => by simp [ValTy.checkCase] at h
  | none :: _, 0, none, _, _ => ⟨rfl, rfl⟩
  | none :: _, 0, some _, _, h | some _ :: _, 0, none, _, h => by
    simp [ValTy.checkCase, ValTy.checkOpt] at h
  | some t :: _, 0, some v, hf, hc => by
    have hf' : floatFree t = true := by
      simp only [floatFreeCases, Bool.and_eq_true] at hf
      exact hf.1
    exact ⟨v, v, rfl, rfl, floatRelAt_refl_free t v hf' hc⟩
  | none :: cs, i + 1, p, hf, hc => floatRelAtCase_refl_free cs i p hf hc
  | some _ :: cs, i + 1, p, hf, hc => by
    have hf' : floatFreeCases cs = true := by
      simp only [floatFreeCases, Bool.and_eq_true] at hf
      exact hf.2
    exact floatRelAtCase_refl_free cs i p hf' hc
end

end Refl

mutual
/-- **`NanAt` is a special case of `NanAtV`** on well-typed values of types with floats only
outside variant payloads. -/
theorem nanAtV_of_nanAt {prof : ProfileKind} : ∀ (t : ValTy) (v w : IVal), floatOk t = true →
    t.check v = true → NanAt prof t v w → NanAtV prof t v w
  | t, v, w, hf, hc, h => by
    cases t <;> cases v <;> first
      | (simp only [ValTy.check, Bool.false_eq_true] at hc; done)
      | exact h
      | (cases w <;> first | exact ⟨_, _, rfl, rfl, h⟩ | (cases h; done))
      | (cases w <;> first
          | exact ⟨_, _, rfl, rfl, nanAtVList_of_nanAtList _ _ _
              (by simpa only [floatOk] using hf) (by simpa only [ValTy.check] using hc) h⟩
          | (cases h; done))
      | (subst h
         exact floatRelAt_refl_free (.variant _) _ (by simpa only [floatOk, floatFree] using hf)
           hc)

/-- `nanAtV_of_nanAt` on lists. -/
theorem nanAtVList_of_nanAtList {prof : ProfileKind} : ∀ (ts : List ValTy) (vs ws : List IVal),
    floatOkList ts = true → ValTy.checkList ts vs = true → NanAtList prof ts vs ws →
      NanAtVList prof ts vs ws
  | [], [], _, _, _, h => ⟨rfl, h.symm⟩
  | [], _ :: _, _, _, hc, _ | _ :: _, [], _, _, hc, _ => by simp [ValTy.checkList] at hc
  | _ :: _, _ :: _, [], _, _, h => by cases h
  | t :: ts, v :: vs, w :: ws, hf, hc, h => by
    have hf' : floatOk t = true ∧ floatOkList ts = true := by
      simpa only [floatOkList, Bool.and_eq_true] using hf
    have hc' : t.check v = true ∧ ValTy.checkList ts vs = true := by
      simpa only [ValTy.checkList, Bool.and_eq_true] using hc
    exact ⟨v, vs, w, ws, rfl, rfl, nanAtV_of_nanAt t v w hf'.1 hc'.1 h.1,
      nanAtVList_of_nanAtList ts vs ws hf'.2 hc'.2 h.2⟩
end

end Silmaril.Proofs.Wasm.Component.Reference
