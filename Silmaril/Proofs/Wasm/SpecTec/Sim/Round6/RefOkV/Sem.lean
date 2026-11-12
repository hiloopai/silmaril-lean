module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.Coh

/-!
# Round 6: SpecTec's subtyping in `{}` lands in Core's, on coherent types

`SubS {}` (SpecTec's `Heaptype_sub` on Core types) may pass through a middle type that is only
SpecTec-valid. It still relates only what Core relates, as long as the endpoints are coherent
(`CohH`): every `SubS {}` derivation lands in `Sem`, a fuel-free reading of Silmaril's checker
`TypeCtx.checkHeap` (abstract order, kinds of defined types, reachability along declared
supertypes), and `Sem` is sound for Core's `Sub {}`.

* `sem_trans`: `Sem` is transitive through a coherent middle type;
* `sem_of_subS`: `SubS {} a b → CohH a → CohH b → Sem a b` (middle types of
  `Heaptype_sub/trans` are `TyOkS {}`, hence coherent, `cohH_of_tyOkS`);
* `sub_of_sem`: `Sem a b → Sub {} a b`;
* `sub_of_subS_ref`: **`SubS {}` between coherent reference types is Core's `Sub {}`**.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Validation.DefInv (clos_nil)

/-- `u` is a defined type whose kind is below `b` in the abstract order. -/
def UseAbs (u : CTypeUse) (b : AbsHeapType) : Prop :=
  ∃ d k, u = .dt d ∧ defKind d = some k ∧ absSub k b = true

/-- **The heap subtyping of `{}`, without fuel**: Silmaril's `TypeCtx.checkHeap {}` with
`TypeCtx.Reach` in place of the bounded search. -/
def Sem : CHeapType → CHeapType → Prop
  | .bot, _ => True
  | .abs a, .abs b => absSub a b = true
  | .abs a, .use u => ∃ t, botTop a = some t ∧ UseAbs u t
  | .use u, .abs b => UseAbs u b
  | .use u₁, .use u₂ => u₁ = u₂ ∨ ∃ d₁ d₂, u₁ = .dt d₁ ∧ u₂ = .dt d₂ ∧ ({} : TypeCtx).Reach d₁ d₂
  | .abs _, .bot => False
  | .use _, .bot => False

theorem sem_refl : ∀ h : CHeapType, Sem h h
  | .bot => trivial
  | .abs a => absSub_refl a
  | .use _ => .inl rfl

/-- A kind fact passes down along `Reach` from a coherent type. -/
theorem useAbs_of_reach {d₁ d₂ : DefType} {b : AbsHeapType} (hc : Coh d₁)
    (hr : ({} : TypeCtx).Reach d₁ d₂) (h : UseAbs (.dt d₂) b) : UseAbs (.dt d₁) b := by
  obtain ⟨d, k, hd, hk, hb⟩ := h
  have e := Ty.dt.inj hd
  subst e
  exact ⟨d₁, k, rfl, (hc d₂ hr).symm.trans hk, hb⟩

/-- A kind fact passes up the abstract order. -/
theorem useAbs_up {u : CTypeUse} {b c : AbsHeapType} (h : UseAbs u b) (hbc : absSub b c = true) :
    UseAbs u c := by
  obtain ⟨d, k, hd, hk, hb⟩ := h
  exact ⟨d, k, hd, hk, absSub_trans hb hbc⟩

/-- No defined type is below an abstract bottom. -/
theorem not_useAbs_botTop {u : CTypeUse} {a t : AbsHeapType} (h : UseAbs u a)
    (ht : botTop a = some t) : False := by
  obtain ⟨d, k, -, hk, hb⟩ := h
  obtain ⟨c, rfl⟩ := defKind_compAbs hk
  exact compAbs_not_bot c hb ht

/-- `Sem` from an abstract type, through a defined type. -/
theorem sem_abs_use_trans {a : AbsHeapType} {v : CTypeUse} {c : CHeapType}
    (h₁ : ∃ t, botTop a = some t ∧ UseAbs v t) (h₂ : Sem (.use v) c) (hm : CohH (.use v)) :
    Sem (.abs a) c := by
  obtain ⟨t, ht, hv⟩ := h₁
  cases c with
  | bot => exact h₂.elim
  | abs z =>
    obtain ⟨d, k, rfl, hk, hkt⟩ := hv
    obtain ⟨d', k', hd', hk', hkz⟩ := (h₂ : UseAbs _ _)
    have e := Ty.dt.inj hd'
    subst e
    rw [hk] at hk'
    cases hk'
    exact absSub_botTop_trans ht hkt hkz
  | use w =>
    rcases (h₂ : _ ∨ _) with rfl | ⟨d₁, d₂, rfl, rfl, hr⟩
    · exact ⟨t, ht, hv⟩
    · obtain ⟨d, k, hd, hk, hkt⟩ := hv
      have e := Ty.dt.inj hd
      subst e
      exact ⟨t, ht, d₂, k, rfl, (hm d₂ hr).trans hk, hkt⟩

/-- `Sem` from a defined type, through a defined type. -/
theorem sem_use_use_trans {u v : CTypeUse} {c : CHeapType} (h₁ : Sem (.use u) (.use v))
    (h₂ : Sem (.use v) c) (ha : CohH (.use u)) : Sem (.use u) c := by
  rcases (h₁ : _ ∨ _) with rfl | ⟨d₁, d₂, rfl, rfl, hr⟩
  · exact h₂
  cases c with
  | bot => exact h₂.elim
  | abs z => exact useAbs_of_reach ha hr h₂
  | use w =>
    rcases (h₂ : _ ∨ _) with rfl | ⟨e₁, e₂, he, rfl, hr'⟩
    · exact .inr ⟨d₁, d₂, rfl, rfl, hr⟩
    · have e := Ty.dt.inj he
      subst e
      exact .inr ⟨d₁, e₂, rfl, rfl, hr.trans hr'⟩

/-- `Sem` from an abstract type, through an abstract type. -/
theorem sem_abs_abs_trans {x y : AbsHeapType} {c : CHeapType} (h₁ : absSub x y = true)
    (h₂ : Sem (.abs y) c) : Sem (.abs x) c := by
  cases c with
  | bot => exact h₂.elim
  | abs z => exact absSub_trans h₁ h₂
  | use w =>
    obtain ⟨t, ht, hw⟩ := (h₂ : ∃ t, botTop y = some t ∧ UseAbs w t)
    exact ⟨t, absSub_eq_of_botTop h₁ ht ▸ ht, hw⟩

/-- `Sem` from a defined type, through an abstract type. -/
theorem sem_use_abs_trans {u : CTypeUse} {y : AbsHeapType} {c : CHeapType} (h₁ : UseAbs u y)
    (h₂ : Sem (.abs y) c) : Sem (.use u) c := by
  cases c with
  | bot => exact h₂.elim
  | abs z => exact useAbs_up h₁ h₂
  | use w =>
    obtain ⟨t, ht, -⟩ := (h₂ : ∃ t, botTop y = some t ∧ UseAbs w t)
    exact (not_useAbs_botTop h₁ ht).elim

/-- **`Sem` is transitive through a coherent middle type** (from a coherent left end). -/
theorem sem_trans {a m c : CHeapType} (h₁ : Sem a m) (h₂ : Sem m c) (ha : CohH a)
    (hm : CohH m) : Sem a c := by
  match a, m, h₁ with
  | .bot, _, _ => trivial
  | .abs _, .bot, h₁ => exact h₁.elim
  | .use _, .bot, h₁ => exact h₁.elim
  | .abs _, .abs _, h₁ => exact sem_abs_abs_trans h₁ h₂
  | .abs _, .use _, h₁ => exact sem_abs_use_trans h₁ h₂ hm
  | .use _, .abs _, h₁ => exact sem_use_abs_trans h₁ h₂
  | .use _, .use _, h₁ => exact sem_use_use_trans h₁ h₂ ha

/-- What a `SubS {}` derivation says, by sort: heap types land in `Sem` between coherent
types, reference types too (with nullability), defined types reach each other. -/
def SemK : {k : TKind} → Ty k → Ty k → Prop
  | .heap, a, b => CohH a → CohH b → Sem a b
  | .ref, .ref n₁ h₁, .ref n₂ h₂ => (n₁ = true → n₂ = true) ∧ (CohH h₁ → CohH h₂ → Sem h₁ h₂)
  | .def, d₁, d₂ => Coh d₁ → Coh d₂ → ({} : TypeCtx).Reach d₁ d₂
  | _, _, _ => True

/-- `none` and its siblings: an abstract bottom is below what is below its top. -/
theorem sem_botTop {a t : AbsHeapType} (ht : botTop a = some t) {h : CHeapType}
    (hs : Sem h (.abs t)) (hb : h ≠ .bot) : Sem (.abs a) h := by
  cases h with
  | bot => exact (hb rfl).elim
  | abs y => exact absSub_of_botTop ht hs
  | use u => exact ⟨t, ht, hs⟩

/-- The kind of an expanding defined type. -/
theorem sem_expand {d : DefType} {ct : CCompType} (h : Expand d ct) :
    Sem (.use (.dt d)) (.abs (compAbs ct)) := by
  obtain ⟨hun⟩ := h
  exact ⟨d, _, rfl, defKind_of_unroll hun, absSub_refl _⟩

/-- A declared supertype of a coherent defined type that reaches `d₂` in `Sem`. -/
theorem reach_of_super {d₁ d₂ : DefType} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    {j : Nat} {u : CTypeUse} (h : unrolldt d₁ = some (.sub fin sups ct))
    (hj : sups.toList[j]? = some u) (hs : Sem (.use u) (.use (.dt d₂))) :
    ({} : TypeCtx).Reach d₁ d₂ := by
  have hu : u ∈ supersOf d₁ := by
    rw [supersOf_of_unroll h]
    exact List.mem_of_getElem? hj
  rcases (hs : _ ∨ _) with rfl | ⟨e₁, e₂, rfl, he, hr⟩
  · exact .step hu rfl (.refl _)
  · have e := Ty.dt.inj he
    subst e
    exact .step hu rfl hr

theorem types_nil_of {Δ : TypeCtx} (h : Δ = {}) : Δ.types = [] := by subst h; rfl

theorem recs_nil_of {Δ : TypeCtx} (h : Δ = {}) : Δ.recs = [] := by subst h; rfl

/-- A declared supertype of a coherent defined type is coherent. -/
theorem cohH_super {d₁ : DefType} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    {j : Nat} {u : CTypeUse} (ha : Coh d₁) (h : unrolldt d₁ = some (.sub fin sups ct))
    (hj : sups.toList[j]? = some u) : CohH (.use u) := by
  have hu : u ∈ supersOf d₁ := by
    rw [supersOf_of_unroll h]
    exact List.mem_of_getElem? hj
  cases u with
  | dt p => exact ha.reach (.step hu rfl (.refl _))
  | idx _ => trivial
  | recv _ => trivial

/-- **`SubS {}` lands in `SemK`.** -/
theorem semK_of_subS : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k}, SubS Δ a b → Δ = {} → SemK a b
  | _, _, _, _, .heapRefl, _ => fun _ _ => sem_refl _
  | _, _, _, _, .heapTrans hok h₁ h₂, hΔ => fun ha hc =>
    have hm := cohH_of_tyOkS (types_nil_of hΔ) hok
    sem_trans (semK_of_subS h₁ hΔ ha hm) (semK_of_subS h₂ hΔ hm hc) ha hm
  | _, _, _, _, .eqAny, _ => fun _ _ => rfl
  | _, _, _, _, .i31Eq, _ => fun _ _ => rfl
  | _, _, _, _, .structEq, _ => fun _ _ => rfl
  | _, _, _, _, .arrayEq, _ => fun _ _ => rfl
  | _, _, _, _, .defStruct h, _ => fun _ _ => sem_expand h
  | _, _, _, _, .defArray h, _ => fun _ _ => sem_expand h
  | _, _, _, _, .defFunc h, _ => fun _ _ => sem_expand h
  | _, _, _, _, .defDef h, hΔ => fun ha hb => .inr ⟨_, _, rfl, rfl, semK_of_subS h hΔ ha hb⟩
  | _, _, _, _, .idxL hx _, hΔ => absurd hx (by simp [types_nil_of hΔ])
  | _, _, _, _, .idxR hx _, hΔ => absurd hx (by simp [types_nil_of hΔ])
  | _, _, _, _, .recStruct h, hΔ => absurd h (by simp [recs_nil_of hΔ])
  | _, _, _, _, .recArray h, hΔ => absurd h (by simp [recs_nil_of hΔ])
  | _, _, _, _, .recFunc h, hΔ => absurd h (by simp [recs_nil_of hΔ])
  | _, _, _, _, .recSub h _, hΔ => absurd h (by simp [recs_nil_of hΔ])
  | _, _, _, _, .none hs hb, hΔ => fun _ hc => sem_botTop rfl (semK_of_subS hs hΔ hc trivial) hb
  | _, _, _, _, .nofunc hs hb, hΔ => fun _ hc => sem_botTop rfl (semK_of_subS hs hΔ hc trivial) hb
  | _, _, _, _, .noexn hs hb, hΔ => fun _ hc => sem_botTop rfl (semK_of_subS hs hΔ hc trivial) hb
  | _, _, _, _, .noextern hs hb, hΔ => fun _ hc =>
    sem_botTop rfl (semK_of_subS hs hΔ hc trivial) hb
  | _, _, _, _, .bot, _ => fun _ _ => trivial
  | _, _, _, _, .refNonNull h, hΔ => ⟨id, semK_of_subS h hΔ⟩
  | _, _, _, _, .refNull h, hΔ => ⟨fun _ => rfl, semK_of_subS h hΔ⟩
  | _, _, _, _, .defRefl h, hΔ => fun _ _ => by
    rw [types_nil_of hΔ, clos_nil, clos_nil] at h
    rw [h]
    exact .refl _
  | _, _, _, _, .defSuper (u := u) h hj hs, hΔ => fun ha hb =>
    reach_of_super h hj (semK_of_subS hs hΔ (cohH_super ha h hj) hb)
  | _, _, _, _, .num, _ => trivial
  | _, _, _, _, .vec, _ => trivial
  | _, _, _, _, .refv _, _ => trivial
  | _, _, _, _, .botv, _ => trivial
  | _, _, _, _, .val _, _ => trivial
  | _, _, _, _, .pack, _ => trivial
  | _, _, _, _, .fieldConst _, _ => trivial
  | _, _, _, _, .fieldVar _ _, _ => trivial
  | _, _, _, _, .struct _, _ => trivial
  | _, _, _, _, .array _, _ => trivial
  | _, _, _, _, .func _ _, _ => trivial
  | _, _, _, _, .nil, _ => trivial
  | _, _, _, _, .cons _ _, _ => trivial

/-- An abstract bottom below a defined type, in Core. -/
theorem sub_abs_use {x : AbsHeapType} {u : CTypeUse}
    (h : ∃ t, botTop x = some t ∧ UseAbs u t) : Sub {} (.abs x) (.use u) := by
  obtain ⟨t, ht, d, k, hu, hk, hkt⟩ := h
  have hs : Sub {} (.use u) (.abs t) := useAbs_sound (Δ := {}) (by simpa [hu] using hk) hkt
  cases x <;> simp [botTop] at ht <;> subst ht
  · exact .none hs nofun
  · exact .nofunc hs nofun
  · exact .noexn hs nofun
  · exact .noextern hs nofun

/-- A defined type below a defined type or an abstract type, in Core. -/
theorem sub_use_of_sem {u : CTypeUse} {b : CHeapType} (h : Sem (.use u) b) :
    Sub {} (.use u) b := by
  cases b with
  | bot => exact h.elim
  | abs y =>
    obtain ⟨d, k, hu, hk, hkb⟩ := (h : UseAbs u y)
    exact useAbs_sound (Δ := {}) (by simpa [hu] using hk) hkb
  | use w =>
    rcases (h : _ ∨ _) with rfl | ⟨d₁, d₂, rfl, rfl, hr⟩
    · exact .heapRefl
    · exact .defDef (hr.sub rfl)

/-- **`SubE` lands in `SemK`** (as `SubS {}` does, `semK_of_subS`). -/
theorem semK_of_subE : ∀ {k : TKind} {a b : Ty k}, SubE a b → SemK a b
  | _, _, _, .heapRefl => fun _ _ => sem_refl _
  | _, _, _, .heapTrans hm h₁ h₂ => fun ha hc =>
    sem_trans (semK_of_subE h₁ ha hm) (semK_of_subE h₂ hm hc) ha hm
  | _, _, _, .eqAny => fun _ _ => rfl
  | _, _, _, .i31Eq => fun _ _ => rfl
  | _, _, _, .structEq => fun _ _ => rfl
  | _, _, _, .arrayEq => fun _ _ => rfl
  | _, _, _, .defStruct h => fun _ _ => sem_expand h
  | _, _, _, .defArray h => fun _ _ => sem_expand h
  | _, _, _, .defFunc h => fun _ _ => sem_expand h
  | _, _, _, .defDef h => fun ha hb => .inr ⟨_, _, rfl, rfl, semK_of_subE h ha hb⟩
  | _, _, _, .none hs hb => fun _ hc => sem_botTop rfl (semK_of_subE hs hc trivial) hb
  | _, _, _, .nofunc hs hb => fun _ hc => sem_botTop rfl (semK_of_subE hs hc trivial) hb
  | _, _, _, .noexn hs hb => fun _ hc => sem_botTop rfl (semK_of_subE hs hc trivial) hb
  | _, _, _, .noextern hs hb => fun _ hc => sem_botTop rfl (semK_of_subE hs hc trivial) hb
  | _, _, _, .bot => fun _ _ => trivial
  | _, _, _, .refNonNull h => ⟨id, semK_of_subE h⟩
  | _, _, _, .refNull h => ⟨fun _ => rfl, semK_of_subE h⟩
  | _, _, _, .defRefl h => fun _ _ => by
    rw [clos_nil, clos_nil] at h
    rw [h]
    exact .refl _
  | _, _, _, .defSuper h hj hs => fun ha hb =>
    reach_of_super h hj (semK_of_subE hs (cohH_super ha h hj) hb)

/-- **`Sem` is sound for Core's `Sub {}`.** -/
theorem sub_of_sem {a b : CHeapType} (h : Sem a b) : Sub {} a b := by
  match a, b, h with
  | .bot, _, _ => exact .bot
  | .abs _, .bot, h => exact h.elim
  | .abs _, .abs _, h => exact absSub_sound h
  | .abs _, .use _, h => exact sub_abs_use h
  | .use _, _, h => exact sub_use_of_sem h

/-- **SpecTec's subtyping in `{}` between coherent heap types is Core's.** -/
theorem sub_of_subS_heap {a b : CHeapType} (h : SubS {} a b) (ha : CohH a) (hb : CohH b) :
    Sub {} a b :=
  sub_of_sem (semK_of_subS h rfl ha hb)

/-- **SpecTec's subtyping in `{}` between coherent reference types is Core's.** -/
theorem sub_of_subS_ref {n₁ n₂ : Bool} {h₁ h₂ : CHeapType} (h : SubS {} (.ref n₁ h₁) (.ref n₂ h₂))
    (ha : CohH h₁) (hb : CohH h₂) : Sub {} (Ty.ref n₁ h₁) (.ref n₂ h₂) := by
  obtain ⟨hn, hs⟩ := semK_of_subS h rfl
  have hs' := sub_of_sem (hs ha hb)
  cases n₂ with
  | true => exact .refNull hs'
  | false =>
    cases n₁ with
    | false => exact .refNonNull hs'
    | true => exact absurd (hn rfl) nofun

/-- **`SubE` between coherent reference types is Core's `Sub {}`.** -/
theorem sub_of_subE_ref {n₁ n₂ : Bool} {h₁ h₂ : CHeapType} (h : SubE (.ref n₁ h₁) (.ref n₂ h₂))
    (ha : CohH h₁) (hb : CohH h₂) : Sub {} (Ty.ref n₁ h₁) (.ref n₂ h₂) := by
  obtain ⟨hn, hs⟩ := semK_of_subE h
  have hs' := sub_of_sem (hs ha hb)
  cases n₂ with
  | true => exact .refNull hs'
  | false =>
    cases n₁ with
    | false => exact .refNonNull hs'
    | true => exact absurd (hn rfl) nofun

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
