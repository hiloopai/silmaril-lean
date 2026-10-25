module

public import Silmaril.Wasm.Validation.Subtyping.Closed

@[expose] public section

/-! # Weakening of type validity out of the empty context

A copy (under `wireCallRef_` names, to avoid clashing with
`Execution.Core.TyOk.of_empty`) of the weakening lemmas of
`Execution/Core/Soundness/TableMemoryTyping.lean`, placed in `Validation` so that
configuration typing (`Typing/Config.lean`) can use it.
-/

namespace Silmaril.Wasm.Validation

theorem wireCallRef_unrollUse_weakenE {Δ₁ Δ₂ : TypeCtx} (ht : Δ₁.types = [])
    (hr : ∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) {u : CTypeUse}
    {st : CSubType} (h : Δ₁.unrollUse u = some st) : Δ₂.unrollUse u = some st := by
  cases u with
  | dt d => exact h
  | idx x => simp [TypeCtx.unrollUse, ht] at h
  | recv i => exact hr _ _ h

mutual
theorem wireCallRef_tyOk_weakenE : ∀ {Δ₁ : TypeCtx} {k : TKind} {t : Ty k}, TyOk Δ₁ t → ∀ (Δ₂ : TypeCtx),
    Δ₁.types = [] → (∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) → TyOk Δ₂ t
  | _, _, _, .idx h, _, ht, _ => by simp [ht] at h
  | _, _, _, .recv h, _, _, hr => .recv (hr _ _ h)
  | _, _, _, .dt h, Δ₂, ht, hr => .dt (wireCallRef_tyOk_weakenE h Δ₂ ht hr)
  | _, _, _, .defn h hi, Δ₂, ht, _ =>
    .defn (wireCallRef_groupOk2_weakenE h (Δ₂.withRecs _) ht fun _ _ h => h) hi
  | _, _, _, .abs a, _, _, _ => .abs a
  | _, _, _, .bot, _, _, _ => .bot
  | _, _, _, .use h, Δ₂, ht, hr => .use (wireCallRef_tyOk_weakenE h Δ₂ ht hr)
  | _, _, _, .ref h, Δ₂, ht, hr => .ref (wireCallRef_tyOk_weakenE h Δ₂ ht hr)
  | _, _, _, .num t, _, _, _ => .num t
  | _, _, _, .vec t, _, _, _ => .vec t
  | _, _, _, .refv h, Δ₂, ht, hr => .refv (wireCallRef_tyOk_weakenE h Δ₂ ht hr)
  | _, _, _, .botv, _, _, _ => .botv
  | _, _, _, .val h, Δ₂, ht, hr => .val (wireCallRef_tyOk_weakenE h Δ₂ ht hr)
  | _, _, _, .pack p, _, _, _ => .pack p
  | _, _, _, .field h, Δ₂, ht, hr => .field (wireCallRef_tyOk_weakenE h Δ₂ ht hr)
  | _, _, _, .struct h, Δ₂, ht, hr => .struct (wireCallRef_tyOk_weakenE h Δ₂ ht hr)
  | _, _, _, .array h, Δ₂, ht, hr => .array (wireCallRef_tyOk_weakenE h Δ₂ ht hr)
  | _, _, _, .func hp hq, Δ₂, ht, hr =>
    .func (wireCallRef_tyOk_weakenE hp Δ₂ ht hr) (wireCallRef_tyOk_weakenE hq Δ₂ ht hr)
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons ha hl, Δ₂, ht, hr =>
    .cons (wireCallRef_tyOk_weakenE ha Δ₂ ht hr) (wireCallRef_tyOk_weakenE hl Δ₂ ht hr)

theorem wireCallRef_subOk2_weakenE : ∀ {Δ₁ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2 Δ₁ st i →
    ∀ (Δ₂ : TypeCtx), Δ₁.types = [] →
      (∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) → SubOk2 Δ₂ st i
  | _, _, _, .noSuper hct, Δ₂, ht, hr => .noSuper (wireCallRef_tyOk_weakenE hct Δ₂ ht hr)
  | _, _, _, .oneSuper hu hb hun hct hsub, Δ₂, ht, hr =>
    .oneSuper (wireCallRef_tyOk_weakenE hu Δ₂ ht hr) hb (wireCallRef_unrollUse_weakenE ht hr hun)
      (wireCallRef_tyOk_weakenE hct Δ₂ ht hr) (wireCallRef_sub_weakenE hsub Δ₂ ht hr)

theorem wireCallRef_groupOk2_weakenE : ∀ {Δ₁ : TypeCtx} {g : CRecType} {i : Nat}, GroupOk2 Δ₁ g i →
    ∀ (Δ₂ : TypeCtx), Δ₁.types = [] →
      (∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) → GroupOk2 Δ₂ g i
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons h hs, Δ₂, ht, hr =>
    .cons (wireCallRef_subOk2_weakenE h Δ₂ ht hr) (wireCallRef_groupOk2_weakenE hs Δ₂ ht hr)

theorem wireCallRef_sub_weakenE : ∀ {Δ₁ : TypeCtx} {k : TKind} {a b : Ty k}, Sub Δ₁ a b → ∀ (Δ₂ : TypeCtx),
    Δ₁.types = [] → (∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) → Sub Δ₂ a b
  | _, _, _, _, .heapRefl, _, _, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, Δ₂, ht, hr =>
    .heapTrans (wireCallRef_tyOk_weakenE hok Δ₂ ht hr) (wireCallRef_sub_weakenE h₁ Δ₂ ht hr) (wireCallRef_sub_weakenE h₂ Δ₂ ht hr)
  | _, _, _, _, .eqAny, _, _, _ => .eqAny
  | _, _, _, _, .i31Eq, _, _, _ => .i31Eq
  | _, _, _, _, .structEq, _, _, _ => .structEq
  | _, _, _, _, .arrayEq, _, _, _ => .arrayEq
  | _, _, _, _, .defStruct h, _, _, _ => .defStruct h
  | _, _, _, _, .defArray h, _, _, _ => .defArray h
  | _, _, _, _, .defFunc h, _, _, _ => .defFunc h
  | _, _, _, _, .defDef h, Δ₂, ht, hr => .defDef (wireCallRef_sub_weakenE h Δ₂ ht hr)
  | _, _, _, _, .idxL hx _, _, ht, _ => by simp [ht] at hx
  | _, _, _, _, .idxR hx _, _, ht, _ => by simp [ht] at hx
  | _, _, _, _, .recStruct h, _, _, hr => .recStruct (hr _ _ h)
  | _, _, _, _, .recArray h, _, _, hr => .recArray (hr _ _ h)
  | _, _, _, _, .recFunc h, _, _, hr => .recFunc (hr _ _ h)
  | _, _, _, _, .recSub h hj, _, _, hr => .recSub (hr _ _ h) hj
  | _, _, _, _, .none hs hb, Δ₂, ht, hr => .none (wireCallRef_sub_weakenE hs Δ₂ ht hr) hb
  | _, _, _, _, .nofunc hs hb, Δ₂, ht, hr => .nofunc (wireCallRef_sub_weakenE hs Δ₂ ht hr) hb
  | _, _, _, _, .noexn hs hb, Δ₂, ht, hr => .noexn (wireCallRef_sub_weakenE hs Δ₂ ht hr) hb
  | _, _, _, _, .noextern hs hb, Δ₂, ht, hr => .noextern (wireCallRef_sub_weakenE hs Δ₂ ht hr) hb
  | _, _, _, _, .bot, _, _, _ => .bot
  | _, _, _, _, .refNonNull h, Δ₂, ht, hr => .refNonNull (wireCallRef_sub_weakenE h Δ₂ ht hr)
  | _, _, _, _, .refNull h, Δ₂, ht, hr => .refNull (wireCallRef_sub_weakenE h Δ₂ ht hr)
  | _, _, _, _, .num, _, _, _ => .num
  | _, _, _, _, .vec, _, _, _ => .vec
  | _, _, _, _, .refv h, Δ₂, ht, hr => .refv (wireCallRef_sub_weakenE h Δ₂ ht hr)
  | _, _, _, _, .botv, _, _, _ => .botv
  | _, _, _, _, .val h, Δ₂, ht, hr => .val (wireCallRef_sub_weakenE h Δ₂ ht hr)
  | _, _, _, _, .pack, _, _, _ => .pack
  | _, _, _, _, .fieldConst h, Δ₂, ht, hr => .fieldConst (wireCallRef_sub_weakenE h Δ₂ ht hr)
  | _, _, _, _, .fieldVar h₁ h₂, Δ₂, ht, hr =>
    .fieldVar (wireCallRef_sub_weakenE h₁ Δ₂ ht hr) (wireCallRef_sub_weakenE h₂ Δ₂ ht hr)
  | _, _, _, _, .struct h, Δ₂, ht, hr => .struct (wireCallRef_sub_weakenE h Δ₂ ht hr)
  | _, _, _, _, .array h, Δ₂, ht, hr => .array (wireCallRef_sub_weakenE h Δ₂ ht hr)
  | _, _, _, _, .func hp hq, Δ₂, ht, hr =>
    .func (wireCallRef_sub_weakenE hp Δ₂ ht hr) (wireCallRef_sub_weakenE hq Δ₂ ht hr)
  | _, _, _, _, .defRefl h, _, ht, _ => by
    rw [ht, SubClosed.clos_nil, SubClosed.clos_nil] at h
    subst h
    exact .defRefl rfl
  | _, _, _, _, .defSuper h hj hs, Δ₂, ht, hr => .defSuper h hj (wireCallRef_sub_weakenE hs Δ₂ ht hr)
  | _, _, _, _, .nil, _, _, _ => .nil
  | _, _, _, _, .cons h hl, Δ₂, ht, hr => .cons (wireCallRef_sub_weakenE h Δ₂ ht hr) (wireCallRef_sub_weakenE hl Δ₂ ht hr)
end

theorem wireCallRef_tyOk_of_empty {k : TKind} {t : Ty k} (Δ : TypeCtx) (h : TyOk {} t) : TyOk Δ t :=
  wireCallRef_tyOk_weakenE h Δ rfl fun _ _ h => by simp at h

end Silmaril.Wasm.Validation
