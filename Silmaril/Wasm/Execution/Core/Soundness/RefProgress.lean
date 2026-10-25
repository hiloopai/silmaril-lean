module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs

@[expose] public section

/-! # Soundness, reference family: progress

`RefInstrOk.progress_ref'` has exactly the statement of `RefInstrOk.progress_ref`
(`Soundness/Reference.lean`); that lemma's former `sorry` has since been replaced with it.

The helpers live in the `RefProgress` namespace so they do not clash with the
similar lemmas of `Soundness/RefTyping.lean` / `StateFacts.lean` (branch
`wasm3-q7-core-ref-redex`, which currently does not build on `wasm3`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

namespace RefProgress

/-- Heap types below a leaf class (`i31`, `exn`, `extern`). -/
def HeapDown (a : AbsHeapType) : CHeapType → Prop
  | .abs z => z = a ∨ z = .none ∨ z = .nofunc ∨ z = .noexn ∨ z = .noextern
  | .bot => True
  | .use _ => False

def IsLeaf (a : AbsHeapType) : Prop := a = .i31 ∨ a = .exn ∨ a = .extern

def DownMotive : (k : TKind) → Ty k → Ty k → Prop
  | .heap, x, y => ∀ a, IsLeaf a → HeapDown a y → HeapDown a x
  | _, _, _ => True

/-- Only bottom types lie below a leaf abstract heap type. -/
theorem sub_down {Δ : TypeCtx} : ∀ {k : TKind} {x y : Ty k}, Sub Δ x y → DownMotive k x y
  | _, _, _, .heapRefl => by intro a _ h; exact h
  | _, _, _, .heapTrans _ h₁ h₂ => by
    have ih₁ := sub_down h₁
    have ih₂ := sub_down h₂
    dsimp only [DownMotive] at ih₁ ih₂ ⊢
    intro a ha h
    exact ih₁ a ha (ih₂ a ha h)
  | _, _, _, .eqAny => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .i31Eq => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .structEq => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .arrayEq => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .defStruct _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .defArray _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .defFunc _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .defDef _ => by intro a _ h; simp [HeapDown] at h
  | _, _, _, .idxL _ hs => by
    have ih := sub_down hs
    dsimp only [DownMotive] at ih ⊢
    intro a ha h
    exact absurd (ih a ha h) (by simp [HeapDown])
  | _, _, _, .idxR _ _ => by intro a _ h; simp [HeapDown] at h
  | _, _, _, .recStruct _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .recArray _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .recFunc _ => by
    intro a ha h; rcases ha with rfl | rfl | rfl <;> simp [HeapDown] at h
  | _, _, _, .recSub _ _ => by intro a _ h; simp [HeapDown] at h
  | _, _, _, .none _ _ => by intro a _ _; simp [HeapDown]
  | _, _, _, .nofunc _ _ => by intro a _ _; simp [HeapDown]
  | _, _, _, .noexn _ _ => by intro a _ _; simp [HeapDown]
  | _, _, _, .noextern _ _ => by intro a _ _; simp [HeapDown]
  | _, _, _, .bot => by intro a _ _; simp [HeapDown]
  | _, _, _, .refNonNull _ => trivial
  | _, _, _, .refNull _ => trivial
  | _, _, _, .num => trivial
  | _, _, _, .vec => trivial
  | _, _, _, .refv _ => trivial
  | _, _, _, .botv => trivial
  | _, _, _, .val _ => trivial
  | _, _, _, .pack => trivial
  | _, _, _, .fieldConst _ => trivial
  | _, _, _, .fieldVar _ _ => trivial
  | _, _, _, .struct _ => trivial
  | _, _, _, .array _ => trivial
  | _, _, _, .func _ _ => trivial
  | _, _, _, .defRefl _ => trivial
  | _, _, _, .defSuper _ _ _ => trivial
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ => trivial

/-- The references that may inhabit a type below a leaf class. -/
def LeafOf : AbsHeapType → Ref → Prop
  | .i31, r => ∃ b, r = .i31 b
  | .exn, r => ∃ a, r = .exn a
  | .extern, r => ∃ r', r = .extern r'
  | _, _ => False

theorem refOk_leaf {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    ∀ (a : AbsHeapType) (n : Bool) (hh : CHeapType), IsLeaf a → rt = .ref n hh →
      HeapDown a hh → r = .null ∨ LeafOf a r := by
  induction h with
  | null => intros; exact .inl rfl
  | i31 b =>
    intro a n hh ha e hd; cases e
    rcases ha with rfl | rfl | rfl <;> simp_all [HeapDown, LeafOf]
  | struct _ => intro a n hh _ e hd; cases e; simp [HeapDown, Ty.defHeap] at hd
  | array _ => intro a n hh _ e hd; cases e; simp [HeapDown, Ty.defHeap] at hd
  | func _ => intro a n hh _ e hd; cases e; simp [HeapDown, Ty.defHeap] at hd
  | exn _ =>
    intro a n hh ha e hd; cases e
    rcases ha with rfl | rfl | rfl <;> simp_all [HeapDown, LeafOf]
  | host _ =>
    intro a n hh ha e hd; cases e
    rcases ha with rfl | rfl | rfl <;> simp_all [HeapDown]
  | extern _ _ =>
    intro a n hh ha e hd; cases e
    rcases ha with rfl | rfl | rfl <;> simp_all [HeapDown, LeafOf]
  | sub _ _ hs ih =>
    intro a n hh ha e hd; subst e
    cases hs with
    | refNonNull h' =>
      have := sub_down h'; dsimp only [DownMotive] at this
      exact ih a _ _ ha rfl (this a ha hd)
    | refNull h' =>
      have := sub_down h'; dsimp only [DownMotive] at this
      exact ih a _ _ ha rfl (this a ha hd)

theorem frameOk_func {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {x : FuncIdx} {d : DefType} (hx : C.funcs[x.toNat]? = some d) :
    ∃ a, f.module.funcs[x.toNat]? = some a := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := h
  cases hm with
  | mk _ _ _ hfuncs =>
    have hl := hfuncs.length_eq
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hx
    exact ⟨_, List.getElem?_eq_getElem (by simp_all)⟩

theorem valOk_refv {s : Store H} {v : Val} {rt : CRefType} (h : ValOk s v (.refv rt)) :
    ∃ r, v = .ref r ∧ RefOk s r rt := by
  cases h with | ref h => exact ⟨_, rfl, h⟩

theorem valOk_i32 {s : Store H} {v : Val} (h : ValOk s v Ty.i32) : ∃ b, v = Val.i32 b := by
  generalize ht : (Ty.i32 : CValType) = t at h
  cases h with
  | num v =>
    obtain ⟨ty, b⟩ := v
    simp only [Ty.i32] at ht
    cases ht
    exact ⟨b, rfl⟩
  | vec b => cases ht
  | ref h => cases ht

end RefProgress

open RefProgress in
/-- **Progress (reference).** -/
theorem RefInstrOk.progress_ref' {P : Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    {vs : List Val} (hst : StateOk s f C) (hi : RefInstrOk C i ⟨t₁, xs, t₂⟩) (hna : ¬ i.IsAggregate)
    (hvs : List.Forall₂ (ValOk s) vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | refNull _ =>
    cases hvs
    exact ⟨_, .reference (.refNull _)⟩
  | refFunc hd _ =>
    cases hvs
    obtain ⟨a, ha⟩ := frameOk_func hst.2 hd
    exact ⟨_, .reference (.refFunc ha)⟩
  | refI31 =>
    obtain ⟨v, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v Ty.i32 := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨rfl, hv⟩ := hv
    obtain ⟨b, rfl⟩ := valOk_i32 hv
    exact ⟨_, .reference (.refI31 b)⟩
  | refIsNull _ =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT true _) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := valOk_refv hv
    by_cases hr : r = .null
    · subst hr; exact ⟨_, .reference .isNullTrue⟩
    · exact ⟨_, .reference (.isNullFalse hr)⟩
  | refAsNonNull _ =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT true _) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := valOk_refv hv
    by_cases hr : r = .null
    · subst hr; exact ⟨_, .reference .asNonNullNull⟩
    · exact ⟨_, .reference (.asNonNullAddr hr)⟩
  | refEq =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ : ∃ v₁ v₂, vs = [v₁, v₂] ∧
        ValOk s v₁ (Ty.refT true (.abs .eq)) ∧ ValOk s v₂ (Ty.refT true (.abs .eq)) := by
      cases hvs with
      | cons hv₁ h => cases h with | cons hv₂ hnil => cases hnil; exact ⟨_, _, rfl, hv₁, hv₂⟩
    obtain ⟨r₁, rfl, -⟩ := valOk_refv hv₁
    obtain ⟨r₂, rfl, -⟩ := valOk_refv hv₂
    by_cases he : r₁ = r₂
    · subst he
      by_cases hr : r₁ = .null
      · subst hr; exact ⟨_, .reference .eqNull⟩
      · exact ⟨_, .reference (.eqTrue hr)⟩
    · exact ⟨_, .reference (.eqFalse he)⟩
  | @refTest rt _ _ _ _ =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (.refv _) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := valOk_refv hv
    by_cases hr : RefOk s r (f.module.instRef rt)
    · exact ⟨_, .reference (.testTrue hr)⟩
    · exact ⟨_, .reference (.testFalse hr)⟩
  | @refCast rt _ _ _ _ =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (.refv _) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := valOk_refv hv
    by_cases hr : RefOk s r (f.module.instRef rt)
    · exact ⟨_, .reference (.castSucceed hr)⟩
    · exact ⟨_, .reference (.castFail hr)⟩
  | i31Get sx =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT true (.abs .i31)) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, hr⟩ := valOk_refv hv
    rcases refOk_leaf hr .i31 _ _ (.inl rfl) rfl (by simp [HeapDown]) with rfl | ⟨b, rfl⟩
    · exact ⟨_, .reference (.i31GetNull sx)⟩
    · exact ⟨_, .reference (.i31GetNum sx b)⟩
  | externConvertAny n =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT n (.abs .any)) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := valOk_refv hv
    by_cases hr : r = .null
    · subst hr; exact ⟨_, .reference .externConvertNull⟩
    · exact ⟨_, .reference (.externConvertAddr hr)⟩
  | anyConvertExtern n =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT n (.abs .extern)) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, hr⟩ := valOk_refv hv
    rcases refOk_leaf hr .extern _ _ (.inr (.inr rfl)) rfl (by simp [HeapDown]) with
      rfl | ⟨r', rfl⟩
    · exact ⟨_, .reference .anyConvertNull⟩
    · exact ⟨_, .reference (.anyConvertAddr r')⟩
  | _ => exact absurd trivial hna

end Silmaril.Wasm.Execution.Core
