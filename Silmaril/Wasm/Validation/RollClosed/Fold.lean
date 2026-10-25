module

public import Silmaril.Wasm.Validation.RollClosed.Basic
public import Silmaril.Wasm.Validation.Subtyping.Closed

@[expose] public section

/-! # Folding an algorithmic subtyping check back into a recursive group

For a group `REC s` whose members have leaves `REC j` (`j < |s|`) and small
`{}`-valid defined types (`OkS s`), a *successful algorithmic check* between the
unrolled images `U a`, `U b` (`U = unrollSubst s`) yields the declarative judgment
`a <: b` inside the group context `{}, RECS s`. The check is cut-free, so its only
"middle" types are declared supertypes, which fold back to `REC` references or stay
small closed types.
-/

namespace Silmaril.Wasm.Validation

namespace RollClosed

open DefInv

/-- Small defined types valid in the empty context (never a member of `REC s`). -/
def OkS (s : Ty (.list .sub)) (e : DefType) : Prop := TyOk {} e ∧ e.size ≤ s.size

/-- The members of `s` have `OkS s` leaves. -/
def GoodSubs (s : Ty (.list .sub)) : Prop :=
  ∀ fin sups b, Ty.sub fin sups b ∈ s.toList →
    Lv s.length (OkS s) sups ∧ Lv s.length (OkS s) b

theorem size_defn (s : Ty (.list .sub)) (j : Nat) :
    (Ty.defn (.group s) j).size = s.size + 2 := rfl

theorem OkS.ne_defn {s : Ty (.list .sub)} {e : DefType} (h : OkS s e) (j : Nat) :
    e ≠ .defn (.group s) j := by
  rintro rfl; have := h.2; rw [size_defn] at this; omega

theorem OkS.closed {s : Ty (.list .sub)} {e : DefType} (h : OkS s e) : e.Closed :=
  SubClosed.closed_of_empty h.1

theorem freeIdx_list_nil {k : TKind} :
    ∀ {l : Ty (.list k)}, (∀ a ∈ l.toList, a.freeIdx = []) → l.freeIdx = []
  | .nil, _ => rfl
  | .cons a l, h => by
    have h1 : a.freeIdx = [] := h a (by simp)
    have h2 : l.freeIdx = [] := freeIdx_list_nil (fun b hb => h b (by simp [hb]))
    simp only [Ty.freeIdx, h1, h2, List.append_nil]

theorem GoodSubs.defn_closed {s : Ty (.list .sub)} (hs : GoodSubs s) (j : Nat) :
    (Ty.defn (.group s) j).Closed := by
  show s.freeIdx = []
  apply freeIdx_list_nil
  intro st hst
  cases st with
  | sub fin sups b =>
    obtain ⟨h1, h2⟩ := hs fin sups b hst
    simp [Ty.freeIdx, Lv.closed (fun _ h => OkS.closed h) _ h1,
      Lv.closed (fun _ h => OkS.closed h) _ h2]

theorem clos_of_closed {T : List DefType} (hT : ∀ d ∈ T, d.Closed) {k : TKind} {t : Ty k}
    (ht : t.Closed) : t.clos T = t := by
  simp only [Ty.clos, closDefTypes_closed hT]
  exact Ty.substAll_closed ht _

/-- Declared supertypes of an unrolled defined type are no larger. -/
theorem super_size {d : DefType} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    (hu : unrolldt d = some (.sub fin sups ct)) {d' : DefType} (hm : Ty.dt d' ∈ sups.toList) :
    d'.size ≤ d.size := by
  cases d with
  | defn g i =>
    cases g with
    | group s' =>
      rw [unrolldt_defn] at hu
      cases hst : s'.toList[i]? with
      | none => rw [hst] at hu; simp at hu
      | some st =>
        rw [hst] at hu
        cases st with
        | sub fin0 sups0 ct0 =>
          simp only [Option.map_some, Option.some.injEq, Ty.subst, Ty.sub.injEq] at hu
          obtain ⟨-, rfl, -⟩ := hu
          rw [Ty.toList_subst, List.mem_map] at hm
          obtain ⟨w, hw, hwe⟩ := hm
          have h1 := Ty.size_lt_of_mem hw
          have h2 := Ty.size_lt_of_mem (List.mem_of_getElem? hst)
          simp only [Ty.size] at h2 ⊢
          cases w with
          | idx x => simp [Ty.subst, unrollSubst] at hwe
          | recv m =>
            simp only [Ty.subst, unrollSubst] at hwe
            split at hwe
            · simp only [Option.getD_some, Ty.dt.injEq] at hwe
              subst hwe; simp [Ty.size]
            · simp at hwe
          | dt d'' =>
            simp only [Ty.subst, subst_def_u, Ty.dt.injEq] at hwe
            subst hwe
            simp only [Ty.size] at h1
            omega

section

variable {s : Ty (.list .sub)}

theorem tyOk_recv {i : Nat} (hi : i < s.length) : TyOk (gctx s) (Ty.use (.recv i)) :=
  .use (.recv (List.getElem?_eq_getElem (by simpa [Ty.length, TypeCtx.withRecs] using hi)))

theorem tyOk_dt {e : DefType} (he : TyOk {} e) : TyOk (gctx s) (Ty.use (.dt e)) :=
  .use (.dt (TyOk.def_congr (Δ₁ := {}) (Δ₂ := gctx s) rfl he))

theorem member {i : Nat} (hi : i < s.length) :
    ∃ fin sups b, s.toList[i]? = some (Ty.sub fin sups b) := by
  have hi' : i < s.toList.length := by simpa [Ty.length] using hi
  generalize hst : s.toList[i] = st
  cases st with
  | sub fin sups b => exact ⟨fin, sups, b, by rw [List.getElem?_eq_getElem hi', hst]⟩

theorem gctx_recs (s : Ty (.list .sub)) (i : Nat) : (gctx s).recs[i]? = s.toList[i]? := rfl

/-- Along declared supertypes: small types stay small, and group members fold back
to `REC` references. -/
theorem reach_fold (hs : GoodSubs s) {Δ : TypeCtx} {d e : DefType} (h : Δ.Reach d e) :
    (OkS s d → OkS s e ∧ Sub (gctx s) (.use (.dt d)) (.use (.dt e))) ∧
    (∀ i, i < s.length → d = .defn (.group s) i →
      (∃ j < s.length, e = .defn (.group s) j ∧
        Sub (gctx s) (.use (.recv i)) (.use (.recv j))) ∨
      (OkS s e ∧ Sub (gctx s) (.use (.recv i)) (.use (.dt e)))) := by
  induction h with
  | refl d => exact ⟨fun h => ⟨h, .heapRefl⟩, fun i hi hd => .inl ⟨i, hi, hd, .heapRefl⟩⟩
  | @step d d' e u hu hr _ ih =>
    obtain ⟨fin, sups, ct, j, hun, hj⟩ := supersOf_mem hu
    refine ⟨fun hO => ?_, fun i hi hd => ?_⟩
    · obtain ⟨-, hsu⟩ := unroll_ok hO.1 hun
      obtain ⟨e₀, rfl, he₀⟩ := hsu u (List.mem_of_getElem? hj)
      simp only [TypeCtx.resolve, Option.some.injEq] at hr
      subst hr
      have hsz := super_size hun (List.mem_of_getElem? hj)
      obtain ⟨hOe, hsub⟩ := ih.1 ⟨he₀, by have := hO.2; omega⟩
      exact ⟨hOe, .defDef (.defSuper hun hj hsub)⟩
    · subst hd
      obtain ⟨fin0, sups0, b0, hst⟩ := member hi
      rw [unroll_of_get hst] at hun
      simp only [Option.some.injEq, Ty.subst, Ty.sub.injEq] at hun
      obtain ⟨-, rfl, -⟩ := hun
      rw [Ty.toList_subst, List.getElem?_map] at hj
      cases hw : sups0.toList[j]? with
      | none => rw [hw] at hj; simp at hj
      | some w =>
        rw [hw] at hj
        simp only [Option.map_some, Option.some.injEq] at hj
        subst hj
        have hLv := Lv.of_mem (hs fin0 sups0 b0 (List.mem_of_getElem? hst)).1 w
          (List.mem_of_getElem? hw)
        have hrec : Sub (gctx s) (.use (.recv i)) (.use w) := .recSub (by rw [gctx_recs]; exact hst) hw
        cases w with
        | idx _ => exact hLv.elim
        | recv m =>
          simp only [Lv] at hLv
          rw [subst_recv hLv] at hr
          simp only [TypeCtx.resolve, Option.some.injEq] at hr
          subst hr
          rcases ih.2 m hLv rfl with ⟨j', hj', rfl, hs'⟩ | ⟨hO, hs'⟩
          · exact .inl ⟨j', hj', rfl, .heapTrans (tyOk_recv hLv) hrec hs'⟩
          · exact .inr ⟨hO, .heapTrans (tyOk_recv hLv) hrec hs'⟩
        | dt e' =>
          simp only [Ty.subst, subst_def_u, TypeCtx.resolve, Option.some.injEq] at hr
          subst hr
          obtain ⟨hOe, hs'⟩ := ih.1 hLv
          exact .inr ⟨hOe, .heapTrans (tyOk_dt hLv.1) hrec hs'⟩

theorem use_cases {n : Nat} {O : DefType → Prop} {v : CTypeUse} (h : Lv n O v) :
    (∃ i, i < n ∧ v = .recv i) ∨ (∃ e, v = .dt e ∧ O e) := by
  cases v with
  | idx _ => exact h.elim
  | recv i => exact .inl ⟨i, h, rfl⟩
  | dt e => exact .inr ⟨e, rfl, h⟩

theorem recAbs {i : Nat} (_hi : i < s.length) {fin : Bool} {sups : Ty (.list .use)} {b : CCompType}
    (hst : s.toList[i]? = some (.sub fin sups b)) {t : AbsHeapType}
    (h : absSub (compAbs b) t = true) : Sub (gctx s) (.use (.recv i)) (.abs t) := by
  have hr : (gctx s).recs[i]? = some (.sub fin sups b) := by rw [gctx_recs]; exact hst
  cases b with
  | struct fs => exact .heapTrans (.abs _) (.recStruct hr) (absSub_sound h)
  | array f => exact .heapTrans (.abs _) (.recArray hr) (absSub_sound h)
  | func ps rs => exact .heapTrans (.abs _) (.recFunc hr) (absSub_sound h)

theorem useAbs_fold {Δ : TypeCtx} {v : CTypeUse} (hv : Lv s.length (OkS s) v) {t : AbsHeapType}
    (h : Δ.checkUseAbs (v.subst (unrollSubst s)) t = true) :
    Sub (gctx s) (.use v) (.abs t) := by
  rcases use_cases hv with ⟨i, hi, rfl⟩ | ⟨e, rfl, _⟩
  · rw [subst_recv hi] at h
    obtain ⟨fin, sups, b, hst⟩ := member hi
    obtain ⟨k, hk, hkt⟩ := (TypeCtx.checkUseAbs_iff (TypeCtx.resolve_dt Δ _)).1 h
    rw [defKind_of_unroll (by rw [unroll_of_get hst]; rfl), compAbs_subst] at hk
    cases hk
    exact recAbs hi hst hkt
  · simp only [Ty.subst, subst_def_u] at h
    obtain ⟨k, hk, hkt⟩ := (TypeCtx.checkUseAbs_iff (TypeCtx.resolve_dt Δ _)).1 h
    exact (gctx s).checkUseAbs_sound
      ((TypeCtx.checkUseAbs_iff (TypeCtx.resolve_dt _ _)).2 ⟨k, hk, hkt⟩)

theorem use_image {v : CTypeUse} (hv : Lv s.length (OkS s) v) :
    ∃ d, v.subst (unrollSubst s) = .dt d ∧
      ((∃ i, i < s.length ∧ v = .recv i ∧ d = .defn (.group s) i) ∨ (v = .dt d ∧ OkS s d)) := by
  rcases use_cases hv with ⟨i, hi, rfl⟩ | ⟨e, rfl, he⟩
  · exact ⟨_, subst_recv hi, .inl ⟨i, hi, rfl, rfl⟩⟩
  · exact ⟨e, by simp only [Ty.subst, subst_def_u], .inr ⟨rfl, he⟩⟩

theorem heap_fold (hs : GoodSubs s) {Δ : TypeCtx} (hΔ : ∀ d ∈ Δ.types, d.Closed) :
    ∀ {h₁ h₂ : CHeapType}, Lv s.length (OkS s) h₁ → Lv s.length (OkS s) h₂ →
      Δ.checkHeap (h₁.subst (unrollSubst s)) (h₂.subst (unrollSubst s)) = true →
      Sub (gctx s) h₁ h₂
  | .bot, _, _, _, _ => .bot
  | .abs a, .abs b, _, _, h => absSub_sound h
  | .abs a, .bot, _, _, h => by simp [Ty.subst, TypeCtx.checkHeap] at h
  | .use _, .bot, _, _, h => by simp [Ty.subst, TypeCtx.checkHeap] at h
  | .abs a, .use v, _, hv, h => by
    simp only [Ty.subst, TypeCtx.checkHeap] at h
    split at h
    · next t ht =>
      have hs' := useAbs_fold hv h
      cases a <;> simp [botTop] at ht <;> subst ht
      · exact .none hs' nofun
      · exact .nofunc hs' nofun
      · exact .noexn hs' nofun
      · exact .noextern hs' nofun
    · simp at h
  | .use v, .abs b, hv, _, h => useAbs_fold hv h
  | .use v₁, .use v₂, hv₁, hv₂, h => by
    obtain ⟨d₁, e₁, c₁⟩ := use_image hv₁
    obtain ⟨d₂, e₂, c₂⟩ := use_image hv₂
    simp only [Ty.subst, e₁, e₂, TypeCtx.checkHeap, TypeCtx.resolve] at h
    obtain ⟨e, he, hc⟩ := TypeCtx.checkDef_exists h
    have hcl₂ : d₂.Closed := by
      rcases c₂ with ⟨j, _, _, rfl⟩ | ⟨_, hO⟩
      · exact hs.defn_closed j
      · exact hO.closed
    have R := reach_fold hs he
    rcases c₁ with ⟨i, hi, rfl, rfl⟩ | ⟨rfl, hO₁⟩
    · rcases R.2 i hi rfl with ⟨j, hj, rfl, hsub⟩ | ⟨hO, hsub⟩
      · rw [clos_of_closed hΔ (hs.defn_closed j), clos_of_closed hΔ hcl₂] at hc
        subst hc
        rcases c₂ with ⟨j', _, rfl, hj'⟩ | ⟨_, hO₂⟩
        · simp only [Ty.defn.injEq, true_and] at hj'; subst hj'; exact hsub
        · exact absurd rfl (hO₂.ne_defn j)
      · rw [clos_of_closed hΔ hO.closed, clos_of_closed hΔ hcl₂] at hc
        subst hc
        rcases c₂ with ⟨j', _, rfl, hj'⟩ | ⟨rfl, _⟩
        · exact absurd hj' (hO.ne_defn j')
        · exact hsub
    · obtain ⟨hO, hsub⟩ := R.1 hO₁
      rw [clos_of_closed hΔ hO.closed, clos_of_closed hΔ hcl₂] at hc
      subst hc
      rcases c₂ with ⟨j', _, rfl, hj'⟩ | ⟨rfl, _⟩
      · exact absurd hj' (hO.ne_defn j')
      · exact hsub

theorem ref_fold (hs : GoodSubs s) {Δ : TypeCtx} (hΔ : ∀ d ∈ Δ.types, d.Closed)
    {a b : CRefType} (ha : Lv s.length (OkS s) a) (hb : Lv s.length (OkS s) b)
    (h : Δ.checkRef (a.subst (unrollSubst s)) (b.subst (unrollSubst s)) = true) :
    Sub (gctx s) a b := by
  cases a with
  | ref n₁ h₁ =>
    cases b with
    | ref n₂ h₂ =>
      simp only [Ty.subst, TypeCtx.checkRef, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at h
      obtain ⟨hn, hh⟩ := h
      have hs' := heap_fold hs hΔ ha hb hh
      cases n₂ with
      | true => exact .refNull hs'
      | false =>
        rcases hn with rfl | hn
        · exact .refNonNull hs'
        · cases hn

theorem val_fold (hs : GoodSubs s) {Δ : TypeCtx} (hΔ : ∀ d ∈ Δ.types, d.Closed) :
    ∀ {a b : CValType}, Lv s.length (OkS s) a → Lv s.length (OkS s) b →
      Δ.checkVal (a.subst (unrollSubst s)) (b.subst (unrollSubst s)) = true → Sub (gctx s) a b
  | .num t₁, .num t₂, _, _, h => by simp [Ty.subst, TypeCtx.checkVal] at h; subst h; exact .num
  | .vec .v128, .vec .v128, _, _, _ => .vec
  | .refv _, .refv _, ha, hb, h => .refv (ref_fold hs hΔ ha hb h)
  | .botv, _, _, _, _ => .botv
  | .num _, .vec _, _, _, h | .num _, .refv _, _, _, h | .num _, .botv, _, _, h
  | .vec _, .num _, _, _, h | .vec _, .refv _, _, _, h | .vec _, .botv, _, _, h
  | .refv _, .num _, _, _, h | .refv _, .vec _, _, _, h | .refv _, .botv, _, _, h => by
    simp [Ty.subst, TypeCtx.checkVal] at h

theorem storage_fold (hs : GoodSubs s) {Δ : TypeCtx} (hΔ : ∀ d ∈ Δ.types, d.Closed)
    {a b : CStorageType} (ha : Lv s.length (OkS s) a) (hb : Lv s.length (OkS s) b)
    (h : Δ.checkStorage (a.subst (unrollSubst s)) (b.subst (unrollSubst s)) = true) :
    Sub (gctx s) a b := by
  cases a <;> cases b <;> simp [Ty.subst, TypeCtx.checkStorage] at h
  · exact .val (val_fold hs hΔ ha hb h)
  · subst h; exact .pack

theorem field_fold (hs : GoodSubs s) {Δ : TypeCtx} (hΔ : ∀ d ∈ Δ.types, d.Closed) :
    ∀ {a b : CFieldType}, Lv s.length (OkS s) a → Lv s.length (OkS s) b →
      Δ.checkField (a.subst (unrollSubst s)) (b.subst (unrollSubst s)) = true → Sub (gctx s) a b
  | .field .const _, .field .const _, ha, hb, h => .fieldConst (storage_fold hs hΔ ha hb h)
  | .field .var _, .field .var _, ha, hb, h => by
    simp only [Ty.subst, TypeCtx.checkField, Bool.and_eq_true] at h
    exact .fieldVar (storage_fold hs hΔ ha hb h.1) (storage_fold hs hΔ hb ha h.2)
  | .field .const _, .field .var _, _, _, h | .field .var _, .field .const _, _, _, h => by
    simp [Ty.subst, TypeCtx.checkField] at h

theorem list_fold {k : TKind} {f : Ty k → Ty k → Bool}
    (hf : ∀ {a b : Ty k}, Lv s.length (OkS s) a → Lv s.length (OkS s) b →
      f (a.subst (unrollSubst s)) (b.subst (unrollSubst s)) = true → Sub (gctx s) a b) :
    ∀ {l₁ l₂ : Ty (.list k)}, Lv s.length (OkS s) l₁ → Lv s.length (OkS s) l₂ →
      forall2B f (l₁.subst (unrollSubst s)).toList (l₂.subst (unrollSubst s)).toList = true →
      Sub (gctx s) l₁ l₂
  | .nil, .nil, _, _, _ => .nil
  | .cons a l, .cons b l', ha, hb, h => by
    simp only [Ty.subst, Ty.toList_cons, forall2B, Bool.and_eq_true] at h
    exact .cons (hf ha.1 hb.1 h.1) (list_fold hf ha.2 hb.2 h.2)
  | .nil, .cons _ _, _, _, h => by simp [Ty.subst, forall2B] at h
  | .cons _ _, .nil, _, _, h => by simp [Ty.subst, forall2B] at h

theorem prefix_fold {k : TKind} {f : Ty k → Ty k → Bool}
    (hf : ∀ {a b : Ty k}, Lv s.length (OkS s) a → Lv s.length (OkS s) b →
      f (a.subst (unrollSubst s)) (b.subst (unrollSubst s)) = true → Sub (gctx s) a b) :
    ∀ {l₂ l₁ : Ty (.list k)}, Lv s.length (OkS s) l₁ → Lv s.length (OkS s) l₂ →
      forall2B f ((l₁.subst (unrollSubst s)).toList.take (l₂.subst (unrollSubst s)).toList.length)
        (l₂.subst (unrollSubst s)).toList = true →
      Sub (gctx s) (Ty.ofList (l₁.toList.take l₂.toList.length)) l₂
  | .nil, _, _, _, _ => by simp; exact .nil
  | .cons b l₂, .cons a l₁, ha, hb, h => by
    simp only [Ty.subst, Ty.toList_cons, List.length_cons, List.take_succ_cons, forall2B,
      Bool.and_eq_true] at h
    simp only [Ty.toList_cons, List.length_cons, List.take_succ_cons, Ty.ofList_cons]
    exact .cons (hf ha.1 hb.1 h.1) (prefix_fold hf ha.2 hb.2 (by simpa [Ty.toList_subst] using h.2))
  | .cons _ _, .nil, _, _, h => by simp [Ty.subst, forall2B] at h

theorem comp_fold (hs : GoodSubs s) {Δ : TypeCtx} (hΔ : ∀ d ∈ Δ.types, d.Closed)
    {a b : CCompType} (ha : Lv s.length (OkS s) a) (hb : Lv s.length (OkS s) b)
    (h : Δ.checkComp (a.subst (unrollSubst s)) (b.subst (unrollSubst s)) = true) :
    Sub (gctx s) a b := by
  cases a <;> cases b <;> simp only [Ty.subst, TypeCtx.checkComp, Bool.false_eq_true] at h
  · next fs₁ fs₂ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hs' := prefix_fold (fun ha hb h => field_fold hs hΔ ha hb h) ha hb h.2
    have := Sub.struct (extra := Ty.ofList (fs₁.toList.drop fs₂.toList.length)) hs'
    have e : (Ty.ofList (fs₁.toList.take fs₂.toList.length)).app
        (Ty.ofList (fs₁.toList.drop fs₂.toList.length)) = fs₁ := by
      simp [Ty.app]
    rwa [e] at this
  · exact .array (field_fold hs hΔ ha hb h)
  · simp only [Bool.and_eq_true] at h
    exact .func (list_fold (fun ha hb h => val_fold hs hΔ ha hb h) hb.1 ha.1 h.1)
      (list_fold (fun ha hb h => val_fold hs hΔ ha hb h) ha.2 hb.2 h.2)

end

end RollClosed

end Silmaril.Wasm.Validation
