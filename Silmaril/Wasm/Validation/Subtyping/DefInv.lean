module

public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Inversion of subtyping between defined types (empty context)

In the empty context, `deftype₁ <: deftype₂` between valid defined types means
that `deftype₁` reaches `deftype₂` along declared supertypes. Each step along a
declared supertype preserves the kind of the expansion and makes the expansion a
composite subtype. The key ingredient is a substitution lemma
(`DefInv.sub_unroll`): a `Comptype_sub` derivation checked inside a recursive
group (`C, RECS subtype*`) survives unrolling (`REC j ↦ _DEF rectype j`) into the
empty context.

Main results:

* `Sub.defHeap_expand`: expansions are covariant along `Heaptype_sub` between
  defined types;
* `Sub.func_inv`, `Sub.not_struct_func`, …: composite-type inversions;
* `Sub.defHeap_func`: the corollary for `call_ref` (parameters contravariant).
-/

namespace Silmaril.Wasm.Validation

namespace DefInv

theorem clos_nil {k : TKind} (t : Ty k) : t.clos [] = t := by
  have : Subst.all [] = fun _ => none := by funext v; cases v <;> rfl
  simp only [Ty.clos, closDefTypes, List.foldl_nil, List.map_nil, Ty.substAll, this]
  exact Ty.subst_none t

theorem okEmpty : TypeCtx.Ok {} := by
  intro d hd
  simp at hd

/-- The context of a recursive group, checked from the empty context. -/
abbrev gctx (subs : Ty (.list .sub)) : TypeCtx := ({} : TypeCtx).withRecs subs.toList

theorem subst_def (σ : Subst) (hσ : ∀ x, σ (.idx x) = none) (d : DefType) : d.subst σ = d :=
  Ty.recFree_def d σ hσ

theorem unrollSubst_idx (subs : Ty (.list .sub)) (x : Nat) : unrollSubst subs (.idx x) = none :=
  rfl

theorem subst_def_u (subs : Ty (.list .sub)) (d : DefType) : d.subst (unrollSubst subs) = d :=
  subst_def _ (unrollSubst_idx subs) d

theorem len_of_get {subs : Ty (.list .sub)} {i : Nat} {st : CSubType}
    (h : subs.toList[i]? = some st) : i < subs.length := by
  have := (List.getElem?_eq_some_iff.1 h).1
  simpa [Ty.length] using this

theorem subst_recv {subs : Ty (.list .sub)} {i : Nat} (hi : i < subs.length) :
    (Ty.recv i : CTypeUse).subst (unrollSubst subs) = .dt (.defn (.group subs) i) := by
  simp [Ty.subst, unrollSubst, hi]

theorem subst_recv' {subs : Ty (.list .sub)} {i : Nat} (hi : i < subs.length) :
    (unrollSubst subs (.recv i)).getD (.recv i) = .dt (.defn (.group subs) i) := by
  simp [unrollSubst, hi]

theorem unroll_of_get {subs : Ty (.list .sub)} {i : Nat} {st : CSubType}
    (h : subs.toList[i]? = some st) :
    unrolldt (.defn (.group subs) i) = some (st.subst (unrollSubst subs)) := by
  rw [unrolldt_defn, h]; rfl

/-- Weakening of validity out of the empty context into one with no `TYPES`. -/
theorem tyOk_wk {Δ : TypeCtx} (hΔ : Δ.types = []) {k : TKind} (t : Ty k) :
    TyOk {} t → TyOk Δ t := by
  induction t with
  | idx x => intro h; cases h with | idx h => simp at h
  | recv i => intro h; cases h with | recv h => simp at h
  | dt d ih => intro h; exact .dt (ih h.dt_inv)
  | defn g i _ => intro h; exact TyOk.def_congr (by simp [hΔ]) h
  | abs a => intro _; exact .abs a
  | bot => intro _; exact .bot
  | use u ih => intro h; exact .use (ih h.use_inv)
  | ref n h ih => intro hh; exact .ref (ih hh.ref_inv)
  | num t => intro _; exact .num t
  | vec t => intro _; exact .vec t
  | refv r ih => intro h; exact .refv (ih h.refv_inv)
  | botv => intro _; exact .botv
  | val t ih => intro h; exact .val (ih h.val_inv)
  | pack p => intro _; exact .pack p
  | field m s ih => intro h; exact .field (ih h.field_inv)
  | struct fs ih => intro h; exact .struct (ih h.struct_inv)
  | array f ih => intro h; exact .array (ih h.array_inv)
  | func ps rs ihp ihr => intro h; exact .func (ihp h.func_inv.1) (ihr h.func_inv.2)
  | nil => intro _; exact .nil
  | cons a l iha ihl => intro h; exact .cons (iha h.cons_inv.1) (ihl h.cons_inv.2)
  | sub _ _ _ _ _ => intro h; cases h
  | group _ _ => intro h; cases h

/-- Valid types of the empty context have no free variables a `REC`-only
substitution could touch. -/
theorem subst_of_ok {k : TKind} (t : Ty k) (σ : Subst) (hσ : ∀ x, σ (.idx x) = none) :
    TyOk {} t → t.subst σ = t := by
  induction t with
  | idx x => intro h; cases h with | idx h => simp at h
  | recv i => intro h; cases h with | recv h => simp at h
  | dt d _ => intro _; exact Ty.recFree_dt d σ hσ
  | defn g i _ => intro _; exact Ty.recFree_def _ σ hσ
  | use u ih => intro h; simp only [Ty.subst, ih h.use_inv]
  | ref n h ih => intro hh; simp only [Ty.subst, ih hh.ref_inv]
  | refv r ih => intro h; simp only [Ty.subst, ih h.refv_inv]
  | val t ih => intro h; simp only [Ty.subst, ih h.val_inv]
  | field m s ih => intro h; simp only [Ty.subst, ih h.field_inv]
  | struct fs ih => intro h; simp only [Ty.subst, ih h.struct_inv]
  | array f ih => intro h; simp only [Ty.subst, ih h.array_inv]
  | func ps rs ihp ihr => intro h; simp only [Ty.subst, ihp h.func_inv.1, ihr h.func_inv.2]
  | cons a l iha ihl => intro h; simp only [Ty.subst, iha h.cons_inv.1, ihl h.cons_inv.2]
  | sub _ _ _ _ _ => intro h; cases h
  | group _ _ => intro h; cases h
  | _ => intro _; rfl

/-- Validity survives unrolling a valid group into the empty context. -/
theorem tyOk_unroll {subs : Ty (.list .sub)} (hg : GroupOk2 (gctx subs) (.group subs) 0)
    {k : TKind} (t : Ty k) : TyOk (gctx subs) t → TyOk {} (t.subst (unrollSubst subs)) := by
  induction t with
  | idx x => intro h; cases h with | idx h => simp [TypeCtx.withRecs] at h
  | recv i =>
    intro h
    cases h with
    | recv h =>
      have hi : i < subs.length := len_of_get (by simpa [TypeCtx.withRecs] using h)
      rw [subst_recv hi]
      exact .dt (.defn hg hi)
  | dt d _ =>
    intro h
    simp only [Ty.subst, subst_def_u]
    exact .dt (TyOk.def_congr (Δ₁ := gctx subs) (Δ₂ := {}) rfl h.dt_inv)
  | defn g i _ =>
    intro h
    rw [subst_def_u]
    exact TyOk.def_congr (Δ₁ := gctx subs) (Δ₂ := {}) rfl h
  | abs a => intro _; exact .abs a
  | bot => intro _; exact .bot
  | use u ih => intro h; exact .use (ih h.use_inv)
  | ref n h ih => intro hh; exact .ref (ih hh.ref_inv)
  | num t => intro _; exact .num t
  | vec t => intro _; exact .vec t
  | refv r ih => intro h; exact .refv (ih h.refv_inv)
  | botv => intro _; exact .botv
  | val t ih => intro h; exact .val (ih h.val_inv)
  | pack p => intro _; exact .pack p
  | field m s ih => intro h; exact .field (ih h.field_inv)
  | struct fs ih => intro h; exact .struct (ih h.struct_inv)
  | array f ih => intro h; exact .array (ih h.array_inv)
  | func ps rs ihp ihr => intro h; exact .func (ihp h.func_inv.1) (ihr h.func_inv.2)
  | nil => intro _; exact .nil
  | cons a l iha ihl => intro h; exact .cons (iha h.cons_inv.1) (ihl h.cons_inv.2)
  | sub _ _ _ _ _ => intro h; cases h
  | group _ _ => intro h; cases h

/-- Unrolling a valid defined type of the empty context: the body is valid and
every declared supertype is a (valid) defined type. -/
theorem unroll_ok {d : DefType} (hd : TyOk {} d) {fin : Bool} {sups : Ty (.list .use)}
    {ct : CCompType} (hu : unrolldt d = some (.sub fin sups ct)) :
    TyOk {} ct ∧ ∀ u ∈ sups.toList, ∃ e, u = .dt e ∧ TyOk {} e := by
  cases hd with
  | @defn _ subs i hg hi =>
    rw [unrolldt_defn] at hu
    cases hst : subs.toList[i]? with
    | none => simp [hst] at hu
    | some st =>
      rw [hst] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      have hso := GroupOk2.get subs hg hst
      cases st with
      | sub fin0 sups0 ct0 =>
        simp only [Ty.subst, Ty.sub.injEq] at hu
        obtain ⟨-, rfl, rfl⟩ := hu
        have hct0 : TyOk (gctx subs) ct0 := by
          cases hso with
          | noSuper hct => exact hct
          | oneSuper _ _ _ hct _ => exact hct
        refine ⟨tyOk_unroll hg ct0 hct0, ?_⟩
        intro u hmem
        rw [Ty.toList_subst, List.mem_map] at hmem
        obtain ⟨u0, hu0, rfl⟩ := hmem
        have h := tyOk_unroll hg u0 (hso.super_ok u0 hu0)
        generalize u0.subst (unrollSubst subs) = w at h
        cases h with
        | idx h => simp at h
        | recv h => simp at h
        | dt h => exact ⟨_, rfl, h⟩

theorem expand_ok {d : DefType} (hd : TyOk {} d) {ct : CCompType} (he : Expand d ct) :
    TyOk {} ct := by
  cases he with
  | mk hu => exact (unroll_ok hd hu).1

theorem subst_ne_bot (σ : Subst) {h : CHeapType} (hb : h ≠ .bot) : h.subst σ ≠ .bot := by
  cases h <;> simp_all [Ty.subst]

theorem subst_app (σ : Subst) {k : TKind} (a b : Ty (.list k)) :
    (a.app b).subst σ = (a.subst σ).app (b.subst σ) := by
  rw [← Ty.ofList_toList ((a.app b).subst σ), ← Ty.ofList_toList ((a.subst σ).app (b.subst σ))]
  simp [Ty.toList_subst, Ty.toList_app]

/-- **Substitution lemma for unrolling.** A subtyping derivation between valid
types inside a valid recursive group survives unrolling into the empty context. -/
theorem sub_unroll {subs : Ty (.list .sub)} (hg : GroupOk2 (gctx subs) (.group subs) 0)
    {Δ : TypeCtx} {k : TKind} {a b : Ty k} (h : Sub Δ a b) :
    Δ = gctx subs → TyOk Δ a → TyOk Δ b →
      Sub {} (a.subst (unrollSubst subs)) (b.subst (unrollSubst subs)) := by
  apply Silmaril.Wasm.Validation.Sub.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun Δ _ a b _ => Δ = gctx subs → TyOk Δ a → TyOk Δ b →
      Sub {} (a.subst (unrollSubst subs)) (b.subst (unrollSubst subs))) (t := h)
  all_goals try (intros; trivial)
  case heapRefl => intros; exact .heapRefl
  case heapTrans =>
    intro Δ _ _ _ hok _ _ _ ih1 ih2 e ha hb
    subst e
    exact .heapTrans (tyOk_unroll hg _ hok) (ih1 rfl ha hok) (ih2 rfl hok hb)
  case eqAny => intros; exact .eqAny
  case i31Eq => intros; exact .i31Eq
  case structEq => intros; exact .structEq
  case arrayEq => intros; exact .arrayEq
  case defStruct =>
    intro Δ d fs he _ _ _
    simp only [Ty.subst, subst_def_u]
    exact .defStruct he
  case defArray =>
    intro Δ d fs he _ _ _
    simp only [Ty.subst, subst_def_u]
    exact .defArray he
  case defFunc =>
    intro Δ d ps rs he _ _ _
    simp only [Ty.subst, subst_def_u]
    exact .defFunc he
  case defDef =>
    intro Δ d₁ d₂ _ ih e ha hb
    exact .defDef (ih e ha.use_inv.dt_inv hb.use_inv.dt_inv)
  case idxL =>
    intro Δ x _ _ hx _ _ e _ _
    subst e; simp [TypeCtx.withRecs] at hx
  case idxR =>
    intro Δ x _ _ hx _ _ e _ _
    subst e; simp [TypeCtx.withRecs] at hx
  case recStruct =>
    intro Δ i fin sups fs hr e _ _
    subst e
    have hr' : subs.toList[i]? = some (.sub fin sups (.struct fs)) := by simpa [TypeCtx.withRecs] using hr
    simp only [Ty.subst]
    rw [subst_recv' (len_of_get hr')]
    exact .defStruct (.mk (unroll_of_get hr'))
  case recArray =>
    intro Δ i fin sups fs hr e _ _
    subst e
    have hr' : subs.toList[i]? = some (.sub fin sups (.array fs)) := by simpa [TypeCtx.withRecs] using hr
    simp only [Ty.subst]
    rw [subst_recv' (len_of_get hr')]
    exact .defArray (.mk (unroll_of_get hr'))
  case recFunc =>
    intro Δ i fin sups ps rs hr e _ _
    subst e
    have hr' : subs.toList[i]? = some (.sub fin sups (.func ps rs)) := by simpa [TypeCtx.withRecs] using hr
    simp only [Ty.subst]
    rw [subst_recv' (len_of_get hr')]
    exact .defFunc (.mk (unroll_of_get hr'))
  case recSub =>
    intro Δ i j fin sups ct u hr hj e _ _
    subst e
    have hr' : subs.toList[i]? = some (.sub fin sups ct) := by simpa [TypeCtx.withRecs] using hr
    have hso := GroupOk2.get subs hg hr'
    have hu := tyOk_unroll hg u (hso.super_ok u (List.mem_of_getElem? hj))
    have hj' : (sups.subst (unrollSubst subs)).toList[j]? = some (u.subst (unrollSubst subs)) := by
      rw [Ty.toList_subst, List.getElem?_map, hj]; rfl
    simp only [Ty.subst]
    rw [subst_recv' (len_of_get hr')]
    generalize u.subst (unrollSubst subs) = w at hu hj'
    cases hu with
    | idx h => simp at h
    | recv h => simp at h
    | dt _ =>
      exact .defDef (.defSuper (unroll_of_get hr') hj' .heapRefl)
  case none =>
    intro Δ h _ hb ih e _ hh
    exact .none (ih e hh (.abs _)) (subst_ne_bot _ hb)
  case nofunc =>
    intro Δ h _ hb ih e _ hh
    exact .nofunc (ih e hh (.abs _)) (subst_ne_bot _ hb)
  case noexn =>
    intro Δ h _ hb ih e _ hh
    exact .noexn (ih e hh (.abs _)) (subst_ne_bot _ hb)
  case noextern =>
    intro Δ h _ hb ih e _ hh
    exact .noextern (ih e hh (.abs _)) (subst_ne_bot _ hb)
  case bot => intros; exact .bot
  case refNonNull =>
    intro Δ _ _ _ ih e ha hb
    exact .refNonNull (ih e ha.ref_inv hb.ref_inv)
  case refNull =>
    intro Δ _ _ _ _ ih e ha hb
    exact .refNull (ih e ha.ref_inv hb.ref_inv)
  case num => intros; exact .num
  case vec => intros; exact .vec
  case refv =>
    intro Δ _ _ _ ih e ha hb
    exact .refv (ih e ha.refv_inv hb.refv_inv)
  case botv => intros; exact .botv
  case val =>
    intro Δ _ _ _ ih e ha hb
    exact .val (ih e ha.val_inv hb.val_inv)
  case pack => intros; exact .pack
  case fieldConst =>
    intro Δ _ _ _ ih e ha hb
    exact .fieldConst (ih e ha.field_inv hb.field_inv)
  case fieldVar =>
    intro Δ _ _ _ _ ih1 ih2 e ha hb
    exact .fieldVar (ih1 e ha.field_inv hb.field_inv) (ih2 e hb.field_inv ha.field_inv)
  case struct =>
    intro Δ fs₁ extra fs₂ _ ih e ha hb
    simp only [Ty.subst, subst_app]
    exact .struct (ih e ha.struct_inv.app_left hb.struct_inv)
  case array =>
    intro Δ _ _ _ ih e ha hb
    exact .array (ih e ha.array_inv hb.array_inv)
  case func =>
    intro Δ _ _ _ _ _ _ ihp ihr e ha hb
    exact .func (ihp e hb.func_inv.1 ha.func_inv.1) (ihr e ha.func_inv.2 hb.func_inv.2)
  case defRefl =>
    intro Δ d₁ d₂ hc e _ _
    subst e
    simp only [TypeCtx.withRecs, clos_nil] at hc
    subst hc
    exact .defRefl rfl
  case defSuper =>
    intro Δ d₁ d₂ fin sups ct j u hu hj _ ih e ha hb
    subst e
    have ha0 : TyOk {} d₁ := TyOk.def_congr (Δ₁ := gctx subs) (Δ₂ := {}) rfl ha
    obtain ⟨e0, rfl, he0⟩ := (unroll_ok ha0 hu).2 u (List.mem_of_getElem? hj)
    have := ih rfl (.use (.dt (TyOk.def_congr (Δ₁ := {}) (Δ₂ := gctx subs) rfl he0))) (.use (.dt hb))
    simp only [Ty.subst, subst_def_u] at this ⊢
    exact .defSuper hu hj this
  case nil => intros; exact .nil
  case cons =>
    intro Δ _ _ _ _ _ _ _ ih1 ih2 e ha hb
    exact .cons (ih1 e ha.cons_inv.1 hb.cons_inv.1) (ih2 e ha.cons_inv.2 hb.cons_inv.2)

/-- One step along a declared supertype: expansions are composite subtypes. -/
theorem super_step_expand {d d' : DefType} {u : CTypeUse} (hd : TyOk {} d)
    (hu : u ∈ supersOf d) (hr : ({} : TypeCtx).resolve u = some d') {ct' : CCompType}
    (he : Expand d' ct') : ∃ ct, Expand d ct ∧ Sub {} ct ct' := by
  cases hd with
  | @defn _ subs i hg hi =>
    have hi' : i < subs.toList.length := by simpa [Ty.length] using hi
    have hst : subs.toList[i]? = some subs.toList[i] := List.getElem?_eq_getElem hi'
    generalize subs.toList[i] = st at hst
    have hso := GroupOk2.get subs hg hst
    rw [Nat.zero_add] at hso
    have hun := unroll_of_get hst
    rw [supersOf_of_unroll hun] at hu
    cases hso with
    | noSuper hct => simp [Ty.subst, Ty.supers] at hu
    | @oneSuper _ fin u0 ct _ sups' ct'0 hu0 hb hunroll hct hsub =>
      simp only [Ty.subst, Ty.supers, Ty.toList_cons, Ty.toList_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hu
      subst hu
      refine ⟨ct.subst (unrollSubst subs), .mk hun, ?_⟩
      cases u0 with
      | idx x => cases hu0 with | idx h => simp [TypeCtx.withRecs] at h
      | recv j =>
        have hj : subs.toList[j]? = some (.sub false sups' ct'0) := by
          simpa [TypeCtx.unrollUse, TypeCtx.withRecs] using hunroll
        rw [subst_recv (len_of_get hj)] at hr
        simp only [TypeCtx.resolve, Option.some.injEq] at hr
        subst hr
        have e2 := unroll_of_get hj
        cases he with
        | mk h2 =>
          rw [e2] at h2
          simp only [Ty.subst, Option.some.injEq, Ty.sub.injEq] at h2
          obtain ⟨-, -, rfl⟩ := h2
          have hct' : TyOk (gctx subs) ct'0 := by
            have hso' := GroupOk2.get subs hg hj
            cases hso' with
            | noSuper hct => exact hct
            | oneSuper _ _ _ hct _ => exact hct
          exact sub_unroll hg hsub rfl hct hct'
      | dt e =>
        simp only [Ty.subst, subst_def_u, TypeCtx.resolve, Option.some.injEq] at hr
        subst hr
        simp only [TypeCtx.unrollUse] at hunroll
        cases he with
        | mk h2 =>
          rw [hunroll] at h2
          simp only [Option.some.injEq, Ty.sub.injEq] at h2
          obtain ⟨-, -, rfl⟩ := h2
          have he0 : TyOk {} e := TyOk.def_congr (Δ₁ := gctx subs) (Δ₂ := {}) rfl hu0.dt_inv
          have hct' := (unroll_ok he0 hunroll).1
          have := sub_unroll hg hsub rfl hct (tyOk_wk rfl _ hct')
          rwa [subst_of_ok _ _ (unrollSubst_idx subs) hct'] at this

theorem reach_expand {d e : DefType} (h : ({} : TypeCtx).Reach d e) :
    TyOk {} d → ∀ {ct : CCompType}, Expand e ct → ∃ ct₁, Expand d ct₁ ∧ Sub {} ct₁ ct := by
  induction h with
  | refl d => intro _ ct he; exact ⟨ct, he, Sub.refl {} (k := .comp) trivial ct⟩
  | step hu hr _ ih =>
    intro hd ct he
    obtain ⟨hok, -, -⟩ := TypeCtx.super_step okEmpty hd hu hr
    obtain ⟨c', he', hs'⟩ := ih hok he
    obtain ⟨c, hec, hs⟩ := super_step_expand hd hu hr he'
    exact ⟨c, hec, Sub.trans okEmpty (expand_ok hok he') hs hs'⟩

end DefInv

open DefInv in
/-- **Expansions are covariant along subtyping of defined heap types** (empty
context, valid endpoints). -/
theorem Sub.defHeap_expand {d₁ d₂ : DefType} (h : Sub {} (Ty.defHeap d₁) (Ty.defHeap d₂))
    (h₁ : TyOk {} d₁) (h₂ : TyOk {} d₂) {ct₂ : CCompType} (he₂ : Expand d₂ ct₂) :
    ∃ ct₁, Expand d₁ ct₁ ∧ Sub {} ct₁ ct₂ := by
  have c := Sub.check_complete okEmpty rfl h (.use (.dt h₁)) (.use (.dt h₂))
  change TypeCtx.checkDef {} d₁ d₂ = true at c
  obtain ⟨e, hr, hc⟩ := TypeCtx.checkDef_exists c
  simp only [clos_nil] at hc
  subst hc
  exact reach_expand hr h₁ he₂

/-! ## Composite-type inversions -/

theorem Sub.func_inv {Δ : TypeCtx} {ps₁ rs₁ ps₂ rs₂ : Ty (.list .val)}
    (h : Sub Δ (Ty.func ps₁ rs₁) (Ty.func ps₂ rs₂)) : Sub Δ ps₂ ps₁ ∧ Sub Δ rs₁ rs₂ := by
  cases h with
  | func hp hr => exact ⟨hp, hr⟩

theorem Sub.not_struct_func {Δ : TypeCtx} {fs : Ty (.list .field)} {ps rs : Ty (.list .val)} :
    ¬ Sub Δ (Ty.struct fs) (Ty.func ps rs) := by
  intro h; cases h

theorem Sub.not_array_func {Δ : TypeCtx} {f : CFieldType} {ps rs : Ty (.list .val)} :
    ¬ Sub Δ (Ty.array f) (Ty.func ps rs) := by
  intro h; cases h

theorem Sub.not_func_struct {Δ : TypeCtx} {fs : Ty (.list .field)} {ps rs : Ty (.list .val)} :
    ¬ Sub Δ (Ty.func ps rs) (Ty.struct fs) := by
  intro h; cases h

theorem Sub.not_func_array {Δ : TypeCtx} {f : CFieldType} {ps rs : Ty (.list .val)} :
    ¬ Sub Δ (Ty.func ps rs) (Ty.array f) := by
  intro h; cases h

theorem Sub.not_struct_array {Δ : TypeCtx} {fs : Ty (.list .field)} {f : CFieldType} :
    ¬ Sub Δ (Ty.struct fs) (Ty.array f) := by
  intro h; cases h

theorem Sub.not_array_struct {Δ : TypeCtx} {fs : Ty (.list .field)} {f : CFieldType} :
    ¬ Sub Δ (Ty.array f) (Ty.struct fs) := by
  intro h; cases h

/-- A composite subtype of a function type is a function type (contravariant
parameters, covariant results). -/
theorem Sub.func_right_inv {Δ : TypeCtx} {ct : CCompType} {ps rs : Ty (.list .val)}
    (h : Sub Δ ct (Ty.func ps rs)) :
    ∃ ps' rs', ct = Ty.func ps' rs' ∧ Sub Δ ps ps' ∧ Sub Δ rs' rs := by
  cases h with
  | func hp hr => exact ⟨_, _, rfl, hp, hr⟩

/-! ## The `call_ref` corollary -/

/-- Along subtyping of valid defined heap types in the empty context, a function
supertype has a function subtype whose parameters are above the supertype's. -/
theorem Sub.defHeap_func_full {d₁ d₂ : DefType} {ps rs : Ty (.list .val)}
    (h : Sub {} (Ty.defHeap d₁) (Ty.defHeap d₂)) (h₁ : TyOk {} d₁) (h₂ : TyOk {} d₂)
    (he : Expand d₂ (.func ps rs)) :
    ∃ ps' rs', Expand d₁ (.func ps' rs') ∧ Sub {} ps ps' ∧ Sub {} rs' rs := by
  obtain ⟨ct, hct, hs⟩ := Sub.defHeap_expand h h₁ h₂ he
  obtain ⟨ps', rs', rfl, hp, hr⟩ := Sub.func_right_inv hs
  exact ⟨ps', rs', hct, hp, hr⟩

theorem Sub.defHeap_func {d₁ d₂ : DefType} {ps rs : Ty (.list .val)}
    (h : Sub {} (Ty.defHeap d₁) (Ty.defHeap d₂)) (h₁ : TyOk {} d₁) (h₂ : TyOk {} d₂)
    (he : Expand d₂ (.func ps rs)) :
    ∃ ps' rs', Expand d₁ (.func ps' rs') ∧ Sub {} ps ps' := by
  obtain ⟨ps', rs', h1, h2, -⟩ := Sub.defHeap_func_full h h₁ h₂ he
  exact ⟨ps', rs', h1, h2⟩

/-- List form (`ResultSub`) of `Sub.defHeap_func`. -/
theorem Sub.defHeap_func_list {d₁ d₂ : DefType} {ps rs : Ty (.list .val)}
    (h : Sub {} (Ty.defHeap d₁) (Ty.defHeap d₂)) (h₁ : TyOk {} d₁) (h₂ : TyOk {} d₂)
    (he : Expand d₂ (.func ps rs)) :
    ∃ ps' rs', Expand d₁ (.func ps' rs') ∧ List.Forall₂ (Sub {}) ps.toList ps'.toList := by
  obtain ⟨ps', rs', h1, h2⟩ := Sub.defHeap_func h h₁ h₂ he
  exact ⟨ps', rs', h1, (Sub.list_iff {} ps ps').1 h2⟩

end Silmaril.Wasm.Validation
