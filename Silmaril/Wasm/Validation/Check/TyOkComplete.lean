module

public import Silmaril.Wasm.Validation.Check.TyOkDerivedComplete
public import Silmaril.Wasm.Validation.Subtyping.DefInv

@[expose] public section

/-! # Completeness of the core type checker

`TyOk.check` is complete in any well-formed context (`TyOk.check_complete'`), in
particular `TyOkComplete Δ` holds (`TyOk.check_complete`). The mode-`true`
companions `SubOk2.check_complete` / `GroupOk2.check_complete` hold in a
well-formed context whose `RECS` form a valid group (`Δ.RecsOk`).

The declared-supertype premise is decided by `Sub.checkRWith (recOracle Δ)`,
complete by `Sub.checkRWith_complete`: `recOracle Δ` accepts every `_DEF`
supertype of a `RECS` entry by construction (`TypeCtx.OracleOk`), and
`Δ.RecsOk` comes from the group derivation itself (`TypeCtx.recsOk_withRecs`).
-/

namespace Silmaril.Wasm.Validation

/-- Validity survives unrolling a valid group (general context). -/
theorem tyOk_unroll_gen {Δ Δ₂ : TypeCtx} (ht : Δ₂.types = Δ.types) {subs : Ty (.list .sub)}
    (hg : GroupOk2 (Δ.withRecs subs.toList) (.group subs) 0)
    {k : TKind} (t : Ty k) :
    TyOk (Δ.withRecs subs.toList) t → TyOk Δ₂ (t.subst (unrollSubst subs)) := by
  induction t with
  | idx x =>
    intro h
    cases h with
    | idx h =>
      simp only [Ty.subst, DefInv.unrollSubst_idx, Option.getD_none]
      exact .idx (by rw [ht]; simpa [TypeCtx.withRecs] using h)
  | recv i =>
    intro h
    cases h with
    | recv h =>
      have hi : i < subs.length := DefInv.len_of_get (by simpa [TypeCtx.withRecs] using h)
      rw [DefInv.subst_recv hi]
      exact .dt (TyOk.def_congr (Δ₁ := Δ) (Δ₂ := Δ₂) ht.symm (.defn hg hi))
  | dt d _ =>
    intro h
    simp only [Ty.subst, DefInv.subst_def_u]
    exact .dt (TyOk.def_congr (by simp [TypeCtx.withRecs, ht]) h.dt_inv)
  | defn g i _ =>
    intro h
    rw [DefInv.subst_def_u]
    exact TyOk.def_congr (by simp [TypeCtx.withRecs, ht]) h
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

/-- The body of the unrolling of a valid defined type is valid. -/
theorem TyOk.unroll_body {Δ : TypeCtx} {d : DefType} (hd : TyOk Δ d) {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} (hu : unrolldt d = some (.sub fin sups ct)) :
    TyOk Δ ct := by
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
        obtain ⟨-, -, rfl⟩ := hu
        have hct0 : TyOk (Δ.withRecs subs.toList) ct0 := by
          cases hso with
          | noSuper hct => exact hct
          | oneSuper _ _ _ hct _ => exact hct
        exact tyOk_unroll_gen rfl hg ct0 hct0

/-- The body of the unrolling of a valid type use is valid (with valid `RECS`). -/
theorem TyOk.unrollUse_body {Δ : TypeCtx} (hΔ : Δ.Ok) (hR : Δ.RecsOk) {u : CTypeUse}
    (hu : TyOk Δ u) {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    (hun : Δ.unrollUse u = some (.sub fin sups ct)) : TyOk Δ ct := by
  cases hu with
  | idx h =>
    simp only [TypeCtx.unrollUse, h] at hun
    exact TyOk.unroll_body (hΔ _ (List.mem_of_getElem? h)).2 hun
  | recv h =>
    simp only [TypeCtx.unrollUse] at hun
    rw [h] at hun
    cases hun
    cases hR _ _ h with
    | noSuper hct => exact hct
    | oneSuper _ _ _ hct _ => exact hct
  | dt h => exact TyOk.unroll_body h hun

theorem recOracle_ok (Δ : TypeCtx) : Δ.OracleOk (recOracle Δ) := by
  intro i st d hi hm
  simp only [recOracle, List.any_eq_true, decide_eq_true_eq]
  exact ⟨st, List.mem_of_getElem? hi, hm⟩

mutual

theorem tyChk_complete_ty : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k}, TyOk Δ t → Δ.Ok →
    tyChk Δ false t 0 = true
  | _, _, _, .idx h, _ => by simp [tyChk, h]
  | _, _, _, .recv h, _ => by simp [tyChk, h]
  | _, _, _, .dt h, hΔ => by simpa [tyChk] using tyChk_complete_ty h hΔ
  | Δ, _, _, @TyOk.defn _ subs _ h hi, hΔ => by
    simp only [tyChk, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨tyChk_complete_group h (hΔ.withRecs _) (TypeCtx.recsOk_withRecs h), hi⟩
  | _, _, _, .abs _, _ => rfl
  | _, _, _, .bot, _ => rfl
  | _, _, _, .use h, hΔ => by simpa [tyChk] using tyChk_complete_ty h hΔ
  | _, _, _, .ref h, hΔ => by simpa [tyChk] using tyChk_complete_ty h hΔ
  | _, _, _, .num _, _ => rfl
  | _, _, _, .vec _, _ => rfl
  | _, _, _, .refv h, hΔ => by simpa [tyChk] using tyChk_complete_ty h hΔ
  | _, _, _, .botv, _ => rfl
  | _, _, _, .val h, hΔ => by simpa [tyChk] using tyChk_complete_ty h hΔ
  | _, _, _, .pack _, _ => rfl
  | _, _, _, .field h, hΔ => by simpa [tyChk] using tyChk_complete_ty h hΔ
  | _, _, _, .struct h, hΔ => by simpa [tyChk] using tyChk_complete_ty h hΔ
  | _, _, _, .array h, hΔ => by simpa [tyChk] using tyChk_complete_ty h hΔ
  | _, _, _, .func hp hr, hΔ => by
    simp only [tyChk, Bool.and_eq_true]
    exact ⟨tyChk_complete_ty hp hΔ, tyChk_complete_ty hr hΔ⟩
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons ha hl, hΔ => by
    simp only [tyChk, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
    exact ⟨tyChk_complete_ty ha hΔ, tyChk_complete_ty hl hΔ⟩

theorem tyChk_complete_sub : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2 Δ st i →
    Δ.Ok → Δ.RecsOk → tyChk Δ true st i = true
  | _, _, _, .noSuper hct, hΔ, _ => by
    simp only [tyChk, Bool.true_and]
    exact tyChk_complete_ty hct hΔ
  | Δ, _, _, .oneSuper hu hb hun hct hsub, hΔ, hR => by
    simp only [tyChk, Bool.true_and, Bool.and_eq_true]
    refine ⟨⟨⟨tyChk_complete_ty hu hΔ, hb⟩, tyChk_complete_ty hct hΔ⟩, ?_⟩
    simp only [superChk, hun]
    exact Sub.checkRWith_complete hΔ hR (recOracle_ok Δ) hsub hct
      (TyOk.unrollUse_body hΔ hR hu hun)

theorem tyChk_complete_group : ∀ {Δ : TypeCtx} {subs : Ty (.list .sub)} {i : Nat},
    GroupOk2 Δ (.group subs) i → Δ.Ok → Δ.RecsOk → tyChk Δ true subs i = true
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons h hs, hΔ, hR => by
    simp only [tyChk, ↓reduceIte, Bool.and_eq_true]
    exact ⟨tyChk_complete_sub h hΔ hR, tyChk_complete_group hs hΔ hR⟩

end

/-- **Completeness** of `TyOk.check` in any well-formed context. -/
theorem TyOk.check_complete' {Δ : TypeCtx} (hΔ : Δ.Ok) {k : TKind} {t : Ty k}
    (h : TyOk Δ t) : TyOk.check Δ t = true :=
  tyChk_complete_ty h hΔ

/-- **Completeness** of the core type checker. -/
theorem TyOk.check_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (_hr : Δ.recs = []) : TyOkComplete Δ :=
  fun h => TyOk.check_complete' hΔ h

theorem recSupChk_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hR : Δ.RecsOk) : recSupChk Δ = true := by
  simp only [recSupChk, List.all_eq_true]
  intro st hst u hu
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hst
  exact tyChk_complete_ty (hR.super hi hu).1 hΔ

/-- **Completeness** of the `Subtype_ok2` checker (valid `RECS`). -/
theorem SubOk2.check_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hR : Δ.RecsOk) {st : CSubType}
    {i : Nat} (h : SubOk2 Δ st i) : SubOk2.check Δ st i = true := by
  simp only [SubOk2.check, Bool.and_eq_true]
  exact ⟨recSupChk_complete hΔ hR, tyChk_complete_sub h hΔ hR⟩

/-- **Completeness** of the `Rectype_ok2` checker (valid `RECS`). -/
theorem GroupOk2.check_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hR : Δ.RecsOk) {rt : CRecType}
    {i : Nat} (h : GroupOk2 Δ rt i) : GroupOk2.check Δ rt i = true := by
  cases rt with
  | group subs =>
    simp only [GroupOk2.check, Bool.and_eq_true]
    exact ⟨recSupChk_complete hΔ hR, tyChk_complete_group h hΔ hR⟩

/-- The group premise of `Deftype_ok` is decided by `GroupOk2.check`. -/
theorem GroupOk2.check_iff_withRecs {Δ : TypeCtx} (hΔ : Δ.Ok) {subs : Ty (.list .sub)} :
    GroupOk2.check (Δ.withRecs subs.toList) (.group subs) 0 = true ↔
      GroupOk2 (Δ.withRecs subs.toList) (.group subs) 0 :=
  ⟨GroupOk2.check_sound, fun h =>
    GroupOk2.check_complete (hΔ.withRecs _) (TypeCtx.recsOk_withRecs h) h⟩

theorem TyOk.check_iff {Δ : TypeCtx} (hΔ : Δ.Ok) {k : TKind} {t : Ty k} :
    TyOk.check Δ t = true ↔ TyOk Δ t :=
  ⟨TyOk.check_sound, TyOk.check_complete' hΔ⟩

end Silmaril.Wasm.Validation
