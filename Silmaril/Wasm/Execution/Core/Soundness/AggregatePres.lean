module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Per-rule preservation lemmas for the aggregate (GC struct/array) family

Self-contained (suffix `Agg`) so that it does not depend on the in-progress
reference-family helper files.

* redex inversion for `vals vs ++ [plain i]` under the general `Instrs_ok2/seq`
  (`redexAgg`), with a replacement certificate;
* store facts for struct/array allocation and field update;
* the per-rule preservation lemmas used by `AggregateStep.preservation`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Lists -/

theorem forall₂_split_rightAgg {α β : Type _} {R : α → β → Prop} {l : List α}
    {l₁ l₂ : List β} (h : List.Forall₂ R l (l₁ ++ l₂)) :
    ∃ a b, l = a ++ b ∧ List.Forall₂ R a l₁ ∧ List.Forall₂ R b l₂ :=
  ⟨l.take l₁.length, l.drop l₁.length, (List.take_append_drop _ _).symm,
    List.forall₂_take_append l l₁ l₂ h, List.forall₂_drop_append l l₁ l₂ h⟩

theorem forall₂_split_leftAgg {α β : Type _} {R : α → β → Prop} {l₁ l₂ : List α}
    {l : List β} (h : List.Forall₂ R (l₁ ++ l₂) l) :
    ∃ a b, l = a ++ b ∧ List.Forall₂ R l₁ a ∧ List.Forall₂ R l₂ b := by
  have h' : List.Forall₂ (flip R) l (l₁ ++ l₂) := List.Forall₂.flip (by simpa [flip] using h)
  obtain ⟨a, b, e, ha, hb⟩ := forall₂_split_rightAgg h'
  exact ⟨a, b, e, List.Forall₂.flip ha, List.Forall₂.flip hb⟩

/-! ## Subtyping chains -/

theorem SubEqR.thenAgg {Δ : TypeCtx} (hΔ : Δ.Ok) {a b c : CValType} (h₁ : SubEqR Δ a b)
    (h₂ : Sub Δ b c) : Sub Δ a c := by
  rcases h₁ with rfl | ⟨h₁, hb⟩
  · exact h₂
  · exact Sub.trans hΔ hb h₁ h₂

theorem forall₂_subEqR_thenAgg {Δ : TypeCtx} (hΔ : Δ.Ok) {l₁ l₂ l₃ : List CValType}
    (h₁ : List.Forall₂ (SubEqR Δ) l₁ l₂) (h₂ : List.Forall₂ (Sub Δ) l₂ l₃) :
    List.Forall₂ (Sub Δ) l₁ l₃ :=
  forall₂_comp h₁ h₂ fun _ _ _ _ _ _ hab hbc => hab.thenAgg hΔ hbc

theorem forall₂_sub_okAgg {Δ : TypeCtx} {l₁ l₂ : List CValType}
    (h : List.Forall₂ (Sub Δ) l₁ l₂) (hok : ResultOk Δ l₂) : List.Forall₂ (SubEqR Δ) l₁ l₂ :=
  forall₂_subEqR_of_sub h hok

theorem forall₂_sub_okLAgg {Δ : TypeCtx} {l₁ l₂ : List CValType}
    (h : List.Forall₂ (Sub Δ) l₁ l₂) (hok : ResultOk Δ l₁) : List.Forall₂ (SubEqL Δ) l₁ l₂ :=
  forall₂_comp (forall₂_self (R := Eq) (fun _ => rfl) l₁) h
    fun a _ _ ha _ _ (e : a = _) hbc => by subst e; exact .inr ⟨hbc, hok _ ha⟩

theorem SubEqL.thenAgg {Δ : TypeCtx} (hΔ : Δ.Ok) {a b c : CValType} (h₁ : Sub Δ a b)
    (h₂ : SubEqL Δ b c) : Sub Δ a c := by
  rcases h₂ with rfl | ⟨h₂, hb⟩
  · exact h₁
  · exact Sub.trans hΔ hb h₁ h₂

theorem resultSub_reflAgg (Δ : TypeCtx) (l : List CValType) : ResultSub Δ l l :=
  ResultSub.refl Δ l

/-! ## Weakening from the empty context -/

theorem Subst.all_nilAgg : Subst.all [] = fun _ => none := by
  funext v; cases v <;> rfl

theorem Ty.clos_nilAgg {k : TKind} (t : Ty k) : t.clos [] = t := by
  simp only [Ty.clos, closDefTypes, List.foldl_nil, List.map_nil, Ty.substAll, Subst.all_nilAgg]
  exact Ty.subst_none t

theorem TypeCtx.unrollUse_wkAgg {Δ : TypeCtx} {u : CTypeUse} (hu : TyOk Δ u) (hΔ : Δ.types = [])
    (T : List DefType) : ({ Δ with types := T } : TypeCtx).unrollUse u = Δ.unrollUse u := by
  cases u with
  | idx x => cases hu with | idx h => simp [hΔ] at h
  | recv i => rfl
  | dt d => rfl

mutual

theorem TyOk.wkTypesAgg (T : List DefType) : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k},
    TyOk Δ t → Δ.types = [] → TyOk { Δ with types := T } t
  | _, _, _, .idx h, hΔ => by simp [hΔ] at h
  | _, _, _, .recv h, _ => .recv h
  | _, _, _, .dt h, hΔ => .dt (TyOk.wkTypesAgg T h hΔ)
  | _, _, _, .defn h hi, hΔ => .defn (GroupOk2.wkTypesAgg T h hΔ) hi
  | _, _, _, .abs a, _ => .abs a
  | _, _, _, .bot, _ => .bot
  | _, _, _, .use h, hΔ => .use (TyOk.wkTypesAgg T h hΔ)
  | _, _, _, .ref h, hΔ => .ref (TyOk.wkTypesAgg T h hΔ)
  | _, _, _, .num t, _ => .num t
  | _, _, _, .vec t, _ => .vec t
  | _, _, _, .refv h, hΔ => .refv (TyOk.wkTypesAgg T h hΔ)
  | _, _, _, .botv, _ => .botv
  | _, _, _, .val h, hΔ => .val (TyOk.wkTypesAgg T h hΔ)
  | _, _, _, .pack p, _ => .pack p
  | _, _, _, .field h, hΔ => .field (TyOk.wkTypesAgg T h hΔ)
  | _, _, _, .struct h, hΔ => .struct (TyOk.wkTypesAgg T h hΔ)
  | _, _, _, .array h, hΔ => .array (TyOk.wkTypesAgg T h hΔ)
  | _, _, _, .func hp hr, hΔ => .func (TyOk.wkTypesAgg T hp hΔ) (TyOk.wkTypesAgg T hr hΔ)
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ha hl, hΔ => .cons (TyOk.wkTypesAgg T ha hΔ) (TyOk.wkTypesAgg T hl hΔ)

theorem SubOk2.wkTypesAgg (T : List DefType) : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat},
    SubOk2 Δ st i → Δ.types = [] → SubOk2 { Δ with types := T } st i
  | _, _, _, .noSuper hct, hΔ => .noSuper (TyOk.wkTypesAgg T hct hΔ)
  | _, _, _, .oneSuper hu hb hunroll hct hsub, hΔ =>
    .oneSuper (TyOk.wkTypesAgg T hu hΔ) hb (by rw [TypeCtx.unrollUse_wkAgg hu hΔ]; exact hunroll)
      (TyOk.wkTypesAgg T hct hΔ) (Sub.wkTypesAgg T hsub hΔ)

theorem GroupOk2.wkTypesAgg (T : List DefType) : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat},
    GroupOk2 Δ g i → Δ.types = [] → GroupOk2 { Δ with types := T } g i
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons h hs, hΔ => .cons (SubOk2.wkTypesAgg T h hΔ) (GroupOk2.wkTypesAgg T hs hΔ)

theorem Sub.wkTypesAgg (T : List DefType) : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k},
    Sub Δ a b → Δ.types = [] → Sub { Δ with types := T } a b
  | _, _, _, _, .heapRefl, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, hΔ =>
    .heapTrans (TyOk.wkTypesAgg T hok hΔ) (Sub.wkTypesAgg T h₁ hΔ) (Sub.wkTypesAgg T h₂ hΔ)
  | _, _, _, _, .eqAny, _ => .eqAny
  | _, _, _, _, .i31Eq, _ => .i31Eq
  | _, _, _, _, .structEq, _ => .structEq
  | _, _, _, _, .arrayEq, _ => .arrayEq
  | _, _, _, _, .defStruct h, _ => .defStruct h
  | _, _, _, _, .defArray h, _ => .defArray h
  | _, _, _, _, .defFunc h, _ => .defFunc h
  | _, _, _, _, .defDef h, hΔ => .defDef (Sub.wkTypesAgg T h hΔ)
  | _, _, _, _, .idxL hx _, hΔ => by simp [hΔ] at hx
  | _, _, _, _, .idxR hx _, hΔ => by simp [hΔ] at hx
  | _, _, _, _, .recStruct h, _ => .recStruct h
  | _, _, _, _, .recArray h, _ => .recArray h
  | _, _, _, _, .recFunc h, _ => .recFunc h
  | _, _, _, _, .recSub h hj, _ => .recSub h hj
  | _, _, _, _, .none hs hb, hΔ => .none (Sub.wkTypesAgg T hs hΔ) hb
  | _, _, _, _, .nofunc hs hb, hΔ => .nofunc (Sub.wkTypesAgg T hs hΔ) hb
  | _, _, _, _, .noexn hs hb, hΔ => .noexn (Sub.wkTypesAgg T hs hΔ) hb
  | _, _, _, _, .noextern hs hb, hΔ => .noextern (Sub.wkTypesAgg T hs hΔ) hb
  | _, _, _, _, .bot, _ => .bot
  | _, _, _, _, .refNonNull h, hΔ => .refNonNull (Sub.wkTypesAgg T h hΔ)
  | _, _, _, _, .refNull h, hΔ => .refNull (Sub.wkTypesAgg T h hΔ)
  | _, _, _, _, .num, _ => .num
  | _, _, _, _, .vec, _ => .vec
  | _, _, _, _, .refv h, hΔ => .refv (Sub.wkTypesAgg T h hΔ)
  | _, _, _, _, .botv, _ => .botv
  | _, _, _, _, .val h, hΔ => .val (Sub.wkTypesAgg T h hΔ)
  | _, _, _, _, .pack, _ => .pack
  | _, _, _, _, .fieldConst h, hΔ => .fieldConst (Sub.wkTypesAgg T h hΔ)
  | _, _, _, _, .fieldVar h₁ h₂, hΔ => .fieldVar (Sub.wkTypesAgg T h₁ hΔ) (Sub.wkTypesAgg T h₂ hΔ)
  | _, _, _, _, .struct h, hΔ => .struct (Sub.wkTypesAgg T h hΔ)
  | _, _, _, _, .array h, hΔ => .array (Sub.wkTypesAgg T h hΔ)
  | _, _, _, _, .func hp hr, hΔ => .func (Sub.wkTypesAgg T hp hΔ) (Sub.wkTypesAgg T hr hΔ)
  | _, _, _, _, .defRefl h, hΔ => .defRefl (by rw [hΔ, Ty.clos_nilAgg, Ty.clos_nilAgg] at h; rw [h])
  | _, _, _, _, .defSuper h hj hs, hΔ => .defSuper h hj (Sub.wkTypesAgg T hs hΔ)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons h hl, hΔ => .cons (Sub.wkTypesAgg T h hΔ) (Sub.wkTypesAgg T hl hΔ)

end

theorem TyOk.wkRecsAgg (R : List CSubType) : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k},
    TyOk Δ t → Δ.recs = [] → TyOk { Δ with recs := R } t
  | _, _, _, .idx h, _ => .idx h
  | _, _, _, .recv h, hΔ => by simp [hΔ] at h
  | _, _, _, .dt h, hΔ => .dt (TyOk.wkRecsAgg R h hΔ)
  | _, _, _, .defn h hi, _ => .defn h hi
  | _, _, _, .abs a, _ => .abs a
  | _, _, _, .bot, _ => .bot
  | _, _, _, .use h, hΔ => .use (TyOk.wkRecsAgg R h hΔ)
  | _, _, _, .ref h, hΔ => .ref (TyOk.wkRecsAgg R h hΔ)
  | _, _, _, .num t, _ => .num t
  | _, _, _, .vec t, _ => .vec t
  | _, _, _, .refv h, hΔ => .refv (TyOk.wkRecsAgg R h hΔ)
  | _, _, _, .botv, _ => .botv
  | _, _, _, .val h, hΔ => .val (TyOk.wkRecsAgg R h hΔ)
  | _, _, _, .pack p, _ => .pack p
  | _, _, _, .field h, hΔ => .field (TyOk.wkRecsAgg R h hΔ)
  | _, _, _, .struct h, hΔ => .struct (TyOk.wkRecsAgg R h hΔ)
  | _, _, _, .array h, hΔ => .array (TyOk.wkRecsAgg R h hΔ)
  | _, _, _, .func hp hr, hΔ => .func (TyOk.wkRecsAgg R hp hΔ) (TyOk.wkRecsAgg R hr hΔ)
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ha hl, hΔ => .cons (TyOk.wkRecsAgg R ha hΔ) (TyOk.wkRecsAgg R hl hΔ)

/-- Runtime (closed-context) validity holds in every context. -/
theorem TyOk.ofEmptyAgg {k : TKind} {t : Ty k} (h : TyOk {} t) (Δ : TypeCtx) : TyOk Δ t := by
  have h1 := TyOk.wkRecsAgg Δ.recs (TyOk.wkTypesAgg Δ.types h rfl) rfl
  cases Δ; exact h1

theorem ResultOk.ofEmptyAgg {ts : List CValType} (h : ResultOk {} ts) (Δ : TypeCtx) :
    ResultOk Δ ts := fun t ht => TyOk.ofEmptyAgg (h t ht) Δ

/-! ## Redex inversion under the general `seq` rule -/

/-- All locals in `X` are already set. -/
def XSetAgg (C : Context) (X : List Nat) : Prop := ∀ x ∈ X, ∃ t, C.locals[x]? = some ⟨.set, t⟩

theorem XSetAgg.append {C : Context} {X₁ X₂ : List Nat} (h₁ : XSetAgg C X₁)
    (h₂ : XSetAgg (C.initLocals X₁) X₂) : XSetAgg C (X₁ ++ X₂) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ x hx
  · rw [Context.initLocals_of_set h₁] at h₂; exact h₂ x hx

theorem AdminOk.toAdmin_initsAgg {s : Store H} {C : Context} {v : Val} {it : InstrType}
    (h : AdminOk s C v.toAdmin it) : it.inits = [] := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r
  · cases h with
    | plain h => cases h <;> ((try (rename_i hh; cases hh)); all_goals rfl)
  · cases h with
    | plain h => cases h <;> ((try (rename_i hh; cases hh)); all_goals rfl)
  · cases h with
    | plain h => cases h <;> ((try (rename_i hh; cases hh)); all_goals rfl)
  · cases h with
    | ref h => rfl

/-- Inversion for a value sequence, also recording that its initialised locals
are already set. -/
theorem AdminsOk.valsAgg {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → ∀ vs, as = vals vs →
      C.toTypeCtx.Ok →
      ResultOk C.toTypeCtx it.params ∧ XSetAgg C it.inits ∧ ∃ ts, List.Forall₂ (ValOk s) vs ts ∧
        List.Forall₂ (SubEqR C.toTypeCtx) (it.params ++ ts) it.results
  | _, _, _, .nil, vs, e, _ => by
    have : vs = [] := List.map_eq_nil_iff.mp e.symm
    subst this
    exact ⟨by simp [ResultOk], by simp [XSetAgg], [], .nil, .nil⟩
  | _, _, _, .single h, vs, e, _ => by
    obtain ⟨v, rfl, hv⟩ := List.map_eq_singleton_iff.mp e.symm
    subst hv
    have hi := AdminOk.toAdmin_initsAgg h
    obtain ⟨hp, t, hv, hr⟩ := AdminOk.toAdmin_inv h
    refine ⟨by simp [hp, ResultOk], by simp [hi, XSetAgg], [t], .cons hv .nil, ?_⟩
    rw [hp, hr]
    exact forall₂_self (fun _ => .inl rfl) _
  | C, _, _, .cons (xs₁ := xs₁) ha _ hs, vs, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    obtain ⟨v, vs', rfl, hv, e'⟩ := List.map_eq_cons_iff.mp e.symm
    subst hv
    have hi := AdminOk.toAdmin_initsAgg ha
    obtain ⟨hp, t, hv, hr⟩ := AdminOk.toAdmin_inv ha
    obtain ⟨_, hx', ts', hv', r⟩ := AdminsOk.valsAgg hs vs' e'.symm hΔ'
    simp only at hp hr hi
    subst hp hr hi
    rw [Context.initLocals_toTypeCtx] at r
    exact ⟨by simp [ResultOk], by simpa using hx', t :: ts', .cons hv hv', r⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, vs, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    obtain ⟨vs₁, vs₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp e.symm
    obtain ⟨p₁, x₁, ts₁, v₁, r₁⟩ := AdminsOk.valsAgg h₁ vs₁ e₁.symm hΔ
    obtain ⟨_, x₂, ts₂, v₂, r₂⟩ := AdminsOk.valsAgg h₂ vs₂ e₂.symm hΔ'
    rw [Context.initLocals_toTypeCtx] at r₂
    refine ⟨p₁, XSetAgg.append x₁ x₂, ts₁ ++ ts₂, forall₂_append v₁ v₂, ?_⟩
    rw [← List.append_assoc]
    exact forall₂_comp (forall₂_append r₁ (forall₂_self (fun _ => .inl rfl) ts₂)) r₂
      fun _ _ _ _ _ _ hab hbc => hab.trans hΔ hbc
  | _, _, _, .sub (it := it₀) h hs hok, vs, e, hΔ => by
    obtain ⟨p, hx, ts, hv, r⟩ := AdminsOk.valsAgg h vs e hΔ
    refine ⟨hok.1, ?_, ts, hv, ?_⟩
    · intro x hx'
      by_cases hm : x ∈ it₀.inits
      · exact hx x hm
      · exact hs.2.2 x hx' hm
    have h1 : List.Forall₂ (SubEqR _) _ _ :=
      forall₂_append (forall₂_subEqR_of_sub hs.1 p) (forall₂_self (fun _ => .inl rfl) ts)
    exact forall₂_comp (forall₂_comp h1 r fun _ _ _ _ _ _ hab hbc => hab.trans hΔ hbc) hs.2.1
      fun _ _ c _ _ hc hab hbc => SubEqR.sub_right hΔ hab hbc (hok.2.1 c hc)
  | _, _, _, .frame (ts := F) h hok, vs, e, hΔ => by
    obtain ⟨p, hx, ts, hv, r⟩ := AdminsOk.valsAgg h vs e hΔ
    refine ⟨ResultOk.append hok p, hx, ts, hv, ?_⟩
    rw [List.append_assoc]
    exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) r

/-- The canonical shape of a typing `P →_X R` of a redex whose principal type,
after dropping its value operands, is `A → t₂`. -/
def CanonAgg (C : Context) (P : List CValType) (X : List Nat) (R A t₂ : List CValType) : Prop :=
  ∃ F A', P = F ++ A' ∧ ResultSub C.toTypeCtx A' A ∧ ResultSub C.toTypeCtx (F ++ t₂) R ∧
    XSetAgg C X ∧ ResultOk C.toTypeCtx P ∧ ResultOk C.toTypeCtx R ∧ ResultOk C.toTypeCtx t₂

/-- Principal typings of the redex instruction: no initialised locals, `N`
parameters, well-formed parameters and results. -/
def HiAgg (C : Context) (i : Instr) (N : Nat) : Prop :=
  ∀ it', InstrOk C i it' → it'.inits = [] ∧ it'.params.length = N ∧
    ResultOk C.toTypeCtx it'.params ∧ ResultOk C.toTypeCtx it'.results

/-- The result of inverting a redex typing. -/
def RedexResAgg (s : Store H) (C : Context) (i : Instr) (vs : List Val) (it : InstrType) : Prop :=
  ∃ A B t₂ ts, InstrOk C i ⟨A ++ B, [], t₂⟩ ∧ List.Forall₂ (ValOk s) vs ts ∧
    ResultSub C.toTypeCtx ts B ∧ CanonAgg C it.params it.inits it.results A t₂

theorem redexSingleAgg {s : Store H} {C : Context} {i : Instr} {N : Nat} {it : InstrType}
    (hI : HiAgg C i N) (hi : InstrOk C i it) : RedexResAgg s C i [] it := by
  obtain ⟨hx, -, hp, hr⟩ := hI it hi
  obtain ⟨P, X, R⟩ := it
  simp only at hx hp hr
  subst hx
  refine ⟨P, [], R, [], by simpa using hi, .nil, .nil, [], P, rfl, resultSub_reflAgg _ _,
    by simpa using resultSub_reflAgg _ R, by simp [XSetAgg], hp, hr, hr⟩

theorem redexNilTailAgg {s : Store H} {C : Context} {i : Instr} {vs : List Val}
    {P M R : List CValType} {X₁ X₂ : List Nat} (hΔ : C.toTypeCtx.Ok)
    (h₁ : RedexResAgg s C i vs ⟨P, X₁, M⟩)
    (h₂ : AdminsOk s (C.initLocals X₁) [] ⟨M, X₂, R⟩) :
    RedexResAgg s C i vs ⟨P, X₁ ++ X₂, R⟩ := by
  obtain ⟨A, B, t₂, ts, hi, hvs, hB, F, A', hP, hA', hF, hX, hPok, hMok, ht₂⟩ := h₁
  have hΔ' : (C.initLocals X₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
  obtain ⟨-, hRok, hMR, hX₂⟩ := AdminsOk.nil_aux h₂ rfl hΔ'
  rw [Context.initLocals_toTypeCtx] at hRok hMR
  refine ⟨A, B, t₂, ts, hi, hvs, hB, F, A', hP, hA', ?_, XSetAgg.append hX hX₂, hPok, hRok, ht₂⟩
  exact forall₂_sub_trans hΔ hF hMR hMok

theorem redexSubAgg {s : Store H} {C : Context} {i : Instr} {vs : List Val}
    {it it' : InstrType} (hΔ : C.toTypeCtx.Ok) (h : RedexResAgg s C i vs it)
    (hs : InstrTypeSub C it it') (hok : InstrTypeOk C it') : RedexResAgg s C i vs it' := by
  obtain ⟨A, B, t₂, ts, hi, hvs, hB, F, A', hP, hA', hF, hX, hPok, hRok, ht₂⟩ := h
  obtain ⟨hs₁, hs₂, hs₃⟩ := hs
  rw [hP] at hs₁ hPok
  obtain ⟨P₁, P₂, hP', h₁, h₂⟩ := forall₂_split_rightAgg hs₁
  have hFok : ResultOk C.toTypeCtx F := fun t ht => hPok t (List.mem_append_left _ ht)
  have hA'ok : ResultOk C.toTypeCtx A' := fun t ht => hPok t (List.mem_append_right _ ht)
  refine ⟨A, B, t₂, ts, hi, hvs, hB, P₁, P₂, hP', forall₂_sub_trans hΔ h₂ hA' hA'ok, ?_, ?_,
    hok.1, hok.2.1, ht₂⟩
  · have e1 : List.Forall₂ (Sub C.toTypeCtx) (P₁ ++ t₂) (F ++ t₂) :=
      forall₂_append h₁ (resultSub_reflAgg _ t₂)
    exact forall₂_sub_trans hΔ (forall₂_sub_trans hΔ e1 hF (ResultOk.append hFok ht₂)) hs₂ hRok
  · intro x hx'
    by_cases hm : x ∈ it.inits
    · exact hX x hm
    · exact hs₃ x hx' hm

theorem redexFrameAgg {s : Store H} {C : Context} {i : Instr} {vs : List Val}
    {G P R : List CValType} {X : List Nat} (h : RedexResAgg s C i vs ⟨P, X, R⟩)
    (hok : ResultOk C.toTypeCtx G) : RedexResAgg s C i vs ⟨G ++ P, X, G ++ R⟩ := by
  obtain ⟨A, B, t₂, ts, hi, hvs, hB, F, A', hP, hA', hF, hX, hPok, hRok, ht₂⟩ := h
  simp only at hP hF hX hPok hRok
  refine ⟨A, B, t₂, ts, hi, hvs, hB, G ++ F, A', by simp [hP], hA', ?_, hX,
    ResultOk.append hok hPok, ResultOk.append hok hRok, ht₂⟩
  rw [List.append_assoc]
  exact forall₂_append (resultSub_reflAgg _ G) hF

theorem redexValsHeadAgg {s : Store H} {C : Context} {i : Instr} {N : Nat} {w₁ w₂ : List Val}
    {P M R : List CValType} {X₁ X₂ : List Nat} (hΔ : C.toTypeCtx.Ok) (hI : HiAgg C i N)
    (hlen : w₁.length + w₂.length ≤ N)
    (hV : ResultOk C.toTypeCtx P ∧ XSetAgg C X₁ ∧ ∃ ts, List.Forall₂ (ValOk s) w₁ ts ∧
        List.Forall₂ (SubEqR C.toTypeCtx) (P ++ ts) M)
    (h₂ : RedexResAgg s C i w₂ ⟨M, X₂, R⟩) :
    RedexResAgg s C i (w₁ ++ w₂) ⟨P, X₁ ++ X₂, R⟩ := by
  obtain ⟨hPok, hX₁, ts₁, hv₁, hPM⟩ := hV
  obtain ⟨A₂, B₂, t₂, ts₂, hi, hv₂, hB₂, F, A'', hM, hA'', hF, hX₂, hMok, hRok, ht₂⟩ := h₂
  simp only at hM hF hX₂ hMok hRok
  subst hM
  obtain ⟨-, hN, hpok, -⟩ := hI _ hi
  simp only [List.length_append] at hN
  have l₁ := hv₁.length_eq
  have l₂ := hv₂.length_eq
  have lB₂ := hB₂.length_eq
  have lA'' := hA''.length_eq
  -- split A₂ = A ++ B₁ with |B₁| = |w₁|
  obtain ⟨A, B₁, rfl, hB₁⟩ : ∃ A B₁, A₂ = A ++ B₁ ∧ B₁.length = w₁.length :=
    ⟨A₂.take (A₂.length - w₁.length), A₂.drop (A₂.length - w₁.length),
      (List.take_append_drop _ _).symm, by simp; omega⟩
  obtain ⟨Aa, Ab, rfl, hAa, hAb⟩ := forall₂_split_rightAgg hA''
  have lAb := hAb.length_eq
  rw [← List.append_assoc] at hPM
  -- split P ++ ts₁ against (F ++ Aa) ++ Ab
  obtain ⟨Q, Qb, hQ, hQ₁, hQ₂⟩ := forall₂_split_rightAgg hPM
  have lQb := hQ₂.length_eq
  have hPl : P.length = Q.length := by
    have := congrArg List.length hQ
    simp only [List.length_append] at this lA'' lAb
    omega
  obtain ⟨rfl, rfl⟩ := List.append_inj hQ hPl
  obtain ⟨P₁, P₂, rfl, hP₁, hP₂⟩ := forall₂_split_rightAgg hQ₁
  have hFok : ResultOk C.toTypeCtx F := fun t ht => hMok t (List.mem_append_left _ ht)
  have hpA : ResultOk C.toTypeCtx (A ++ B₁ ++ B₂) := hpok
  refine ⟨A, B₁ ++ B₂, t₂, ts₁ ++ ts₂, by simpa using hi, forall₂_append hv₁ hv₂,
    forall₂_append (forall₂_subEqR_thenAgg hΔ hQ₂ hAb) hB₂, P₁, P₂, rfl,
    forall₂_subEqR_thenAgg hΔ hP₂ hAa, ?_, XSetAgg.append hX₁ (by
      rw [Context.initLocals_of_set hX₁]; exact hX₂), hPok, hRok, ht₂⟩
  have e1 : List.Forall₂ (SubEqR C.toTypeCtx) (P₁ ++ t₂) (F ++ t₂) :=
    forall₂_append hP₁ (forall₂_self (fun _ => .inl rfl) t₂)
  exact forall₂_subEqR_thenAgg hΔ e1 hF

/-- **Redex inversion** by induction on the typing derivation. -/
theorem redexAuxAgg {s : Store H} {i : Instr} {N : Nat} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it →
      C.toTypeCtx.Ok → HiAgg C i N →
      ∀ vs : List Val, as = vals vs ++ [.plain i] → vs.length ≤ N → RedexResAgg s C i vs it
  | _, _, _, .nil, _, _, vs, e, _ => by simp at e
  | _, _, _, .single ha, _, hI, vs, e, _ => by
    have hl := congrArg List.length e
    simp only [List.length_singleton, List.length_append, vals_length] at hl
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [vals, List.map_nil, List.nil_append, List.cons.injEq, and_true] at e
    subst e
    cases ha.plain_cases with
    | inr h => obtain ⟨rfl, -⟩ := h; exact (InstrOk.throwRef_arity_absurd fun it h => (hI it h).2.1).elim
    | inl hi => exact redexSingleAgg hI hi
  | C, _, _, .cons (a := a) (as := as') (xs₁ := xs₁) ha hx hs, hΔ, hI, vs, e, hlen => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    cases vs with
    | nil =>
      simp only [vals, List.map_nil, List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      cases ha.plain_cases with
      | inr h => obtain ⟨rfl, -⟩ := h; exact (InstrOk.throwRef_arity_absurd fun it h => (hI it h).2.1).elim
      | inl hi =>
        exact redexNilTailAgg hΔ (redexSingleAgg hI hi) hs
    | cons v vs' =>
      simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e'⟩ := e
      have hV := AdminsOk.valsAgg (.single ha) [v] rfl hΔ
      have hC : C.initLocals xs₁ = C := Context.initLocals_of_set hV.2.1
      have hI' : HiAgg (C.initLocals xs₁) i N := by rw [hC]; exact hI
      have ih := redexAuxAgg hs hΔ' hI' vs' e' (by simp at hlen; omega)
      rw [hC] at ih
      have := redexValsHeadAgg (w₁ := [v]) hΔ hI (by simp at hlen ⊢; omega) hV ih
      simpa using this
  | C, _, _, .seq (as₁ := as₁) (as₂ := as₂) (xs₁ := xs₁) h₁ hx h₂, hΔ, hI, vs, e, hlen => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    by_cases hne : as₂ = []
    · subst hne
      rw [List.append_nil] at e
      exact redexNilTailAgg hΔ (redexAuxAgg h₁ hΔ hI vs e hlen) h₂
    · obtain ⟨as₂', hl⟩ : ∃ l, as₂ = l ++ [.plain i] := by
        obtain ⟨l, y, hl⟩ : ∃ l y, as₂ = l ++ [y] :=
          ⟨as₂.dropLast, as₂.getLast hne, (List.dropLast_append_getLast hne).symm⟩
        refine ⟨l, ?_⟩
        rw [hl] at e ⊢
        rw [← List.append_assoc] at e
        have := (List.append_inj' e rfl).2
        simp only [List.cons.injEq, and_true] at this
        rw [this]
      rw [hl, ← List.append_assoc] at e
      have e' := (List.append_inj' e rfl).1
      obtain ⟨w₁, w₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp e'.symm
      have hV := AdminsOk.valsAgg h₁ w₁ e₁.symm hΔ
      have hC : C.initLocals xs₁ = C := Context.initLocals_of_set hV.2.1
      have hI' : HiAgg (C.initLocals xs₁) i N := by rw [hC]; exact hI
      have ih := redexAuxAgg h₂ hΔ' hI' w₂ (by rw [hl, ← e₂]; rfl) (by simp at hlen; omega)
      rw [hC] at ih
      exact redexValsHeadAgg hΔ hI (by simpa using hlen) hV ih
  | _, _, _, .sub h hs hok, hΔ, hI, vs, e, hlen =>
    redexSubAgg hΔ (redexAuxAgg h hΔ hI vs e hlen) hs hok
  | _, _, _, .frame h hok, hΔ, hI, vs, e, hlen => by
    exact redexFrameAgg (redexAuxAgg h hΔ hI vs e hlen) hok

/-- **Redex inversion and replacement** for a redex whose instruction consumes
exactly the given operands. -/
theorem redexAgg {s : Store H} {C : Context} {i : Instr} {vs : List Val} {it : InstrType}
    (hΔ : C.toTypeCtx.Ok) (hI : HiAgg C i vs.length)
    (h : AdminsOk s C (vals vs ++ [.plain i]) it) :
    ∃ t₁ t₂ ts, InstrOk C i ⟨t₁, [], t₂⟩ ∧ List.Forall₂ (ValOk s) vs ts ∧
      ResultSub C.toTypeCtx ts t₁ ∧ ResultOk C.toTypeCtx t₁ ∧ ResultOk C.toTypeCtx t₂ ∧
      ∀ (s' : Store H) (out : List Admin), AdminsOk s' C out ⟨[], [], t₂⟩ → AdminsOk s' C out it := by
  obtain ⟨A, B, t₂, ts, hi, hvs, hB, F, A', hP, hA', hF, hX, hPok, hRok, ht₂⟩ :=
    redexAuxAgg h hΔ hI vs rfl le_rfl
  obtain ⟨-, hN, hp, -⟩ := hI _ hi
  have := hB.length_eq
  have := hvs.length_eq
  simp only [List.length_append] at hN
  obtain rfl : A = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain rfl : A' = [] := by cases hA'; rfl
  rw [List.append_nil] at hP
  refine ⟨B, t₂, ts, by simpa using hi, hvs, hB, by simpa using hp, ht₂, fun s' out hout => ?_⟩
  obtain ⟨P, X, R⟩ := it
  simp only at hP hF hX hPok hRok
  subst hP
  have h1 : AdminsOk s' C out ⟨P ++ [], [], P ++ t₂⟩ := .frame hout hPok
  refine .sub h1 ⟨by simpa using resultSub_reflAgg _ P, hF, fun x hx _ => hX x hx⟩
    ⟨hPok, hRok, fun x hx => by obtain ⟨t, ht⟩ := hX x hx; exact ⟨_, ht⟩⟩

/-! ## Weakening subtyping from the empty context -/

theorem Sub.wkRecsAgg (R : List CSubType) : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k},
    Sub Δ a b → Δ.recs = [] → Sub { Δ with recs := R } a b
  | _, _, _, _, .heapRefl, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, hΔ =>
    .heapTrans (TyOk.wkRecsAgg R hok hΔ) (Sub.wkRecsAgg R h₁ hΔ) (Sub.wkRecsAgg R h₂ hΔ)
  | _, _, _, _, .eqAny, _ => .eqAny
  | _, _, _, _, .i31Eq, _ => .i31Eq
  | _, _, _, _, .structEq, _ => .structEq
  | _, _, _, _, .arrayEq, _ => .arrayEq
  | _, _, _, _, .defStruct h, _ => .defStruct h
  | _, _, _, _, .defArray h, _ => .defArray h
  | _, _, _, _, .defFunc h, _ => .defFunc h
  | _, _, _, _, .defDef h, hΔ => .defDef (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .idxL hx h, hΔ => .idxL hx (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .idxR hx h, hΔ => .idxR hx (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .recStruct h, hΔ => by simp [hΔ] at h
  | _, _, _, _, .recArray h, hΔ => by simp [hΔ] at h
  | _, _, _, _, .recFunc h, hΔ => by simp [hΔ] at h
  | _, _, _, _, .recSub h _, hΔ => by simp [hΔ] at h
  | _, _, _, _, .none hs hb, hΔ => .none (Sub.wkRecsAgg R hs hΔ) hb
  | _, _, _, _, .nofunc hs hb, hΔ => .nofunc (Sub.wkRecsAgg R hs hΔ) hb
  | _, _, _, _, .noexn hs hb, hΔ => .noexn (Sub.wkRecsAgg R hs hΔ) hb
  | _, _, _, _, .noextern hs hb, hΔ => .noextern (Sub.wkRecsAgg R hs hΔ) hb
  | _, _, _, _, .bot, _ => .bot
  | _, _, _, _, .refNonNull h, hΔ => .refNonNull (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .refNull h, hΔ => .refNull (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .num, _ => .num
  | _, _, _, _, .vec, _ => .vec
  | _, _, _, _, .refv h, hΔ => .refv (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .botv, _ => .botv
  | _, _, _, _, .val h, hΔ => .val (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .pack, _ => .pack
  | _, _, _, _, .fieldConst h, hΔ => .fieldConst (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .fieldVar h₁ h₂, hΔ => .fieldVar (Sub.wkRecsAgg R h₁ hΔ) (Sub.wkRecsAgg R h₂ hΔ)
  | _, _, _, _, .struct h, hΔ => .struct (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .array h, hΔ => .array (Sub.wkRecsAgg R h hΔ)
  | _, _, _, _, .func hp hr, hΔ => .func (Sub.wkRecsAgg R hp hΔ) (Sub.wkRecsAgg R hr hΔ)
  | _, _, _, _, .defRefl h, _ => .defRefl h
  | _, _, _, _, .defSuper h hj hs, hΔ => .defSuper h hj (Sub.wkRecsAgg R hs hΔ)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons h hl, hΔ => .cons (Sub.wkRecsAgg R h hΔ) (Sub.wkRecsAgg R hl hΔ)

/-- Runtime (closed-context) subtyping holds in every context. -/
theorem Sub.ofEmptyAgg {k : TKind} {a b : Ty k} (h : Sub {} a b) (Δ : TypeCtx) : Sub Δ a b := by
  have h1 := Sub.wkRecsAgg Δ.recs (Sub.wkTypesAgg Δ.types h rfl) rfl
  cases Δ; exact h1

/-! ## Typed states -/

/-- Validity of the defined types of struct and array instances. `Store_ok` (as in
SpecTec 3.0) does not require it, but aggregate preservation is false without
it: a struct instance of an invalid defined type can claim an arbitrary declared
supertype with different field types, and `struct.get` at that supertype would
return a value of the wrong type. -/
def StoreDefsOkAgg (s : Store H) : Prop :=
  (∀ si ∈ s.structs, TyOk {} si.type) ∧ (∀ ai ∈ s.arrays, TyOk {} ai.type)

theorem InstrOk.aggAgg {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    (hi : i.IsAggregate) : RefInstrOk C i it := by
  cases h with
  | reference h => exact h
  | parametric h => cases h <;> simp [Instr.IsAggregate] at hi
  | numeric h => cases h <;> simp [Instr.IsAggregate] at hi
  | vector h => cases h <;> simp [Instr.IsAggregate] at hi
  | «variable» h => cases h <;> simp [Instr.IsAggregate] at hi
  | memory h => cases h <;> simp [Instr.IsAggregate] at hi
  | table h => cases h <;> simp [Instr.IsAggregate] at hi
  | _ => simp [Instr.IsAggregate] at hi

theorem forall₂_getElem?_rightAgg {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (_ : List.Forall₂ R l₁ l₂) {i : Nat} {b : β},
      l₂[i]? = some b → ∃ a, l₁[i]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab hl, i, b, h => by
    cases i with
    | zero => simp at h; subst h; exact ⟨_, rfl, hab⟩
    | succ i => simpa using forall₂_getElem?_rightAgg hl (by simpa using h)

theorem TyOk.closed_of_emptyAgg {k : TKind} {t : Ty k} (h : TyOk {} t) : t.Closed := by
  unfold Ty.Closed
  rcases hf : t.freeIdx with _ | ⟨y, l⟩
  · rfl
  · have := TyOk.freeIdx_lt h y (by simp [hf])
    simp at this

theorem StateOk.typesAgg {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C) :
    C.types = f.module.types ∧ ∀ d ∈ C.types, TyOk {} d := by
  obtain ⟨-, C₀, lts, hm, -, rfl⟩ := hst
  cases hm with
  | mk htypes => exact ⟨rfl, htypes⟩

theorem StateOk.deltaOkAgg {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C) :
    C.toTypeCtx.Ok := by
  intro d hd
  have h := hst.typesAgg.2 d hd
  exact ⟨TyOk.closed_of_emptyAgg h, TyOk.ofEmptyAgg h _⟩

theorem StateOk.typeAgg {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    {x : TypeIdx} {d : DefType} (hx : C.type? x = some d) : f.type? x = some d ∧ TyOk {} d := by
  obtain ⟨he, hok⟩ := hst.typesAgg
  refine ⟨by simpa [Context.type?, Frame.type?, he] using hx, hok d (List.mem_of_getElem? hx)⟩

theorem StateOk.elemAgg {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    {y : ElemIdx} {rt : CRefType} (hy : C.elems[y.toNat]? = some rt) :
    ∃ ea ei, s.elem? f y = some (ea, ei) ∧ ei.type = rt ∧ ElemInstOk s ei := by
  obtain ⟨hs, C₀, lts, hmi, _, rfl⟩ := hst
  cases hmi with
  | mk _ _ _ _ _ _ _ helems =>
    obtain ⟨ea, hea, ei, hget, hok, hty⟩ := forall₂_getElem?_rightAgg helems hy
    exact ⟨ea, ei, by simp [Store.elem?, hea, hget], hty, hok⟩

theorem ResultOk.ofMemAgg {Δ : TypeCtx} {ts : List CValType} (h : ∀ t ∈ ts, TyOk Δ t) :
    ResultOk Δ ts := h

theorem Expand.fieldAgg {Δ : TypeCtx} {d : DefType} {fs : Ty (.list .field)} (hd : TyOk Δ d)
    (he : Expand d (.struct fs)) {i : Nat} {m : Mutability} {z : CStorageType}
    (hi : fs.toList[i]? = some (.field m z)) : TyOk Δ z := by
  have := Expand.struct_ok hd he _ (List.mem_of_getElem? hi)
  cases this with | field h => exact h

/-- Regularity of aggregate instruction typings in a typed state. -/
theorem _root_.Silmaril.Wasm.Validation.RefInstrOk.regAgg {s : Store H} {f : Frame} {C : Context}
    {i : Instr} {it : InstrType}
    (hst : StateOk s f C) (h : RefInstrOk C i it) (ha : i.IsAggregate) :
    it.inits = [] ∧ ResultOk {} it.params ∧ ResultOk {} it.results := by
  have hT : ∀ {x : TypeIdx} {d : DefType}, C.type? x = some d → TyOk {} d :=
    fun hx => (hst.typeAgg hx).2
  have hR : ∀ {x : TypeIdx} {d : DefType} (n : Bool), C.type? x = some d →
      TyOk {} (Ty.refT n (Ty.defHeap d)) := fun n hx => .refv (.ref (.use (.dt (hT hx))))
  have hI : TyOk {} Ty.i32 := .num _
  cases h <;> simp [Instr.IsAggregate] at ha
  case structNew hd he =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [List.mem_map] at ht
      obtain ⟨ft, hft, rfl⟩ := ht
      exact TyOk.fieldUnpack (Expand.struct_ok (hT hd) he ft hft)
    · simp only [List.mem_singleton] at ht; subst ht; exact hR _ hd
  case structNewDefault hd _ _ =>
    refine ⟨rfl, fun t ht => by simp at ht, fun t ht => ?_⟩
    simp only [List.mem_singleton] at ht; subst ht; exact hR _ hd
  case structGet hd he hi _ =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [List.mem_singleton] at ht; subst ht; exact hR _ hd
    · simp only [List.mem_singleton] at ht; subst ht
      exact TyOk.unpack (Expand.fieldAgg (hT hd) he hi)
  case structSet hd he hi =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => by simp at ht⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl
    · exact hR _ hd
    · exact TyOk.unpack (Expand.fieldAgg (hT hd) he hi)
  case arrayNew hd he =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil,
        or_false] at ht
      rcases ht with rfl | rfl
      · exact TyOk.unpack (Expand.array_ok (hT hd) he)
      · exact hI
    · simp only [List.mem_singleton] at ht; subst ht; exact hR _ hd
  case arrayNewDefault hd _ _ =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [List.mem_singleton] at ht; subst ht; exact hI
    · simp only [List.mem_singleton] at ht; subst ht; exact hR _ hd
  case arrayNewFixed hd he =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [List.mem_replicate] at ht
      rw [ht.2]; exact TyOk.unpack (Expand.array_ok (hT hd) he)
    · simp only [List.mem_singleton] at ht; subst ht; exact hR _ hd
  case arrayNewElem hd _ _ _ =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil,
        or_false] at ht
      rcases ht with rfl | rfl <;> exact hI
    · simp only [List.mem_singleton] at ht; subst ht; exact hR _ hd
  case arrayNewData hd _ _ _ =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil,
        or_false] at ht
      rcases ht with rfl | rfl <;> exact hI
    · simp only [List.mem_singleton] at ht; subst ht; exact hR _ hd
  case arrayGet hd he _ =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil,
        or_false] at ht
      rcases ht with rfl | rfl
      · exact hR _ hd
      · exact hI
    · simp only [List.mem_singleton] at ht; subst ht
      exact TyOk.unpack (Expand.array_ok (hT hd) he)
  case arraySet hd he =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => by simp at ht⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact hR _ hd
    · exact hI
    · exact TyOk.unpack (Expand.array_ok (hT hd) he)
  case arrayLen =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [List.mem_singleton] at ht; subst ht; exact .refv (.ref (.abs _))
    · simp only [List.mem_singleton] at ht; subst ht; exact hI
  case arrayFill hd he =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => by simp at ht⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hR _ hd
    · exact hI
    · exact TyOk.unpack (Expand.array_ok (hT hd) he)
    · exact hI
  case arrayCopy hd₁ _ hd₂ _ _ =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => by simp at ht⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact hR _ hd₁
    · exact hI
    · exact hR _ hd₂
    · exact hI
    · exact hI
  case arrayInitElem hd _ _ _ =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => by simp at ht⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hR _ hd
    all_goals exact hI
  case arrayInitData hd _ _ _ =>
    refine ⟨rfl, fun t ht => ?_, fun t ht => by simp at ht⟩
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hR _ hd
    all_goals exact hI

/-- The principal-typing premise of `redexAgg` for aggregate instructions. -/
theorem hiAgg {s : Store H} {f : Frame} {C : Context} {i : Instr} {N : Nat}
    (hst : StateOk s f C) (ha : i.IsAggregate)
    (hlen : ∀ it', RefInstrOk C i it' → it'.params.length = N) : HiAgg C i N := by
  intro it' h
  have hr := InstrOk.aggAgg h ha
  obtain ⟨h1, h2, h3⟩ := hr.regAgg hst ha
  exact ⟨h1, hlen _ hr, ResultOk.ofEmptyAgg h2 _, ResultOk.ofEmptyAgg h3 _⟩

/-! ## Subtyping of expansions (struct/array subtyping soundness) -/

theorem Ty.subst_appAgg {k : TKind} (σ : Subst) (l e : Ty (.list k)) :
    (l.app e).subst σ = (l.subst σ).app (e.subst σ) := by
  simp only [Ty.app, Ty.subst_ofList, List.map_append, Ty.toList_subst]

/-- Closed-context validity: substitutions leaving `_IDX` alone do not change the type. -/
theorem TyOk.subst_emptyAgg {σ : Subst} (hidx : ∀ x, σ (.idx x) = none) :
    ∀ {k : TKind} (t : Ty k), TyOk {} t → t.subst σ = t := by
  have hminus : ∀ v, σ.minusRecs v = none := Subst.minusRecs_of_idx_none hidx
  intro k t
  induction t with
  | nil => intro _; rfl
  | cons a l iha ihl => intro h; cases h with | cons ha hl => simp [Ty.subst, iha ha, ihl hl]
  | idx x => intro h; cases h with | idx hx => simp at hx
  | recv i => intro h; cases h with | recv hi => simp at hi
  | dt d ih => intro h; cases h with | dt h => simp [Ty.subst, ih h]
  | defn g i _ =>
    intro _
    cases g with
    | group subs => simp only [Ty.subst]; rw [Ty.subst_of_none _ _ hminus]
  | abs a => intro _; rfl
  | bot => intro _; rfl
  | use u ih => intro h; cases h with | use h => simp [Ty.subst, ih h]
  | ref n hh ih => intro h; cases h with | ref h => simp [Ty.subst, ih h]
  | num t => intro _; rfl
  | vec t => intro _; rfl
  | refv r ih => intro h; cases h with | refv h => simp [Ty.subst, ih h]
  | botv => intro _; rfl
  | val t ih => intro h; cases h with | val h => simp [Ty.subst, ih h]
  | pack p => intro _; rfl
  | field m s ih => intro h; cases h with | field h => simp [Ty.subst, ih h]
  | struct fs ih => intro h; cases h with | struct h => simp [Ty.subst, ih h]
  | array f ih => intro h; cases h with | array h => simp [Ty.subst, ih h]
  | func ps rs ihp ihr => intro h; cases h with | func hp hr => simp [Ty.subst, ihp hp, ihr hr]
  | sub fin sups b => intro h; cases h
  | group subs => intro h; cases h

theorem unrollSubst_idxAgg (subs : Ty (.list .sub)) (x : Nat) : unrollSubst subs (.idx x) = none :=
  rfl

/-- The declared supertypes of a valid defined type (after unrolling) are not `REC`. -/
theorem TyOk.unroll_super_not_recvAgg {Δ : TypeCtx} {b : DefType} (hb : TyOk Δ b) {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType}
    (hu : unrolldt b = some (.sub fin sups ct)) {u : CTypeUse} (hmem : u ∈ sups.toList) :
    ∀ i, u ≠ .recv i := by
  cases hb with
  | @defn _ subs i hg hi =>
    simp only [unrolldt, unrollrt, Ty.subs] at hu
    rw [Ty.toList_subst, List.getElem?_map] at hu
    cases hst : subs.toList[i]? with
    | none => simp [hst] at hu
    | some st =>
      rw [hst] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      have hso := GroupOk2.get subs hg hst
      cases st with
      | sub fin0 sups0 ct0 =>
        simp only [Ty.subst, Ty.sub.injEq] at hu
        obtain ⟨-, hsups, -⟩ := hu
        subst hsups
        rw [Ty.toList_subst, List.mem_map] at hmem
        obtain ⟨u0, hu0, rfl⟩ := hmem
        have hok := hso.super_ok u0 hu0
        intro j
        cases u0 with
        | idx x => simp [Ty.subst]
        | recv j' =>
          cases hok with
          | recv h =>
            have hj : j' < subs.length := by
              have := (List.getElem?_eq_some_iff.1 h).1
              simpa [TypeCtx.withRecs, Ty.length] using this
            simp [Ty.subst, hj]
        | dt e => rw [Ty.recFree_dt e _ (fun _ => rfl)]; simp

theorem tyOk_substAgg {subs : Ty (.list .sub)}
    (hg : GroupOk2 (({} : TypeCtx).withRecs subs.toList) (.group subs) 0) {k : TKind} {t : Ty k}
    (h : TyOk (({} : TypeCtx).withRecs subs.toList) t) : TyOk {} (t.subst (unrollSubst subs)) :=
  TyOk.subst_recs (Δ := {}) (R := subs.toList) (fun _ => rfl) (fun j hj => by
    have hj' : j < subs.length := by simpa [Ty.length] using hj
    exact ⟨_, by simp [unrollSubst, hj'], .dt (.defn hg hj')⟩) t h

/-- **Substitution for subtyping** at the unrolling substitution of a valid
group, for valid types (validity rules out ill-scoped `REC` supertypes). -/
theorem Sub.substRecsAgg {subs : Ty (.list .sub)}
    (hg : GroupOk2 (({} : TypeCtx).withRecs subs.toList) (.group subs) 0) :
    ∀ {Δ₀ : TypeCtx} {k : TKind} {a b : Ty k}, Sub Δ₀ a b →
      Δ₀ = ({} : TypeCtx).withRecs subs.toList → TyOk Δ₀ a → TyOk Δ₀ b →
      Sub {} (a.subst (unrollSubst subs)) (b.subst (unrollSubst subs))
  | _, _, _, _, .heapRefl, hΔ, _, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, hΔ, ha, hb =>
    .heapTrans (tyOk_substAgg hg (hΔ ▸ hok)) (Sub.substRecsAgg hg h₁ hΔ ha hok)
      (Sub.substRecsAgg hg h₂ hΔ hok hb)
  | _, _, _, _, .eqAny, hΔ, _, _ => .eqAny
  | _, _, _, _, .i31Eq, hΔ, _, _ => .i31Eq
  | _, _, _, _, .structEq, hΔ, _, _ => .structEq
  | _, _, _, _, .arrayEq, hΔ, _, _ => .arrayEq
  | _, _, _, _, @Sub.defStruct _ d _ h, hΔ, _, _ => by
    simp only [Ty.subst, Ty.recFree_def d _ (unrollSubst_idxAgg subs)]; exact .defStruct h
  | _, _, _, _, @Sub.defArray _ d _ h, hΔ, _, _ => by
    simp only [Ty.subst, Ty.recFree_def d _ (unrollSubst_idxAgg subs)]; exact .defArray h
  | _, _, _, _, @Sub.defFunc _ d _ _ h, hΔ, _, _ => by
    simp only [Ty.subst, Ty.recFree_def d _ (unrollSubst_idxAgg subs)]; exact .defFunc h
  | _, _, _, _, .defDef h, hΔ, ha, hb => by
    have ih := Sub.substRecsAgg hg h hΔ ha.use_inv.dt_inv hb.use_inv.dt_inv
    simp only [Ty.subst] at ih ⊢
    exact .defDef ih
  | _, _, _, _, .idxL hx _, hΔ, _, _ => by subst hΔ; simp [TypeCtx.withRecs] at hx
  | _, _, _, _, .idxR hx _, hΔ, _, _ => by subst hΔ; simp [TypeCtx.withRecs] at hx
  | _, _, _, _, @Sub.recStruct _ i fin sups fs h, hΔ, _, _ => by
    subst hΔ
    have hi : i < subs.length := by
      have := (List.getElem?_eq_some_iff.1 h).1
      simpa [TypeCtx.withRecs, Ty.length] using this
    simp only [Ty.subst, unrollSubst, hi, ↓reduceIte, Option.getD_some]
    refine .defStruct (fs := fs.subst (unrollSubst subs)) (.mk (fin := fin)
      (sups := sups.subst (unrollSubst subs)) ?_)
    rw [unrolldt_defn]; simp only [TypeCtx.withRecs] at h; rw [h]; rfl
  | _, _, _, _, @Sub.recArray _ i fin sups f h, hΔ, _, _ => by
    subst hΔ
    have hi : i < subs.length := by
      have := (List.getElem?_eq_some_iff.1 h).1
      simpa [TypeCtx.withRecs, Ty.length] using this
    simp only [Ty.subst, unrollSubst, hi, ↓reduceIte, Option.getD_some]
    refine .defArray (f := f.subst (unrollSubst subs)) (.mk (fin := fin)
      (sups := sups.subst (unrollSubst subs)) ?_)
    rw [unrolldt_defn]; simp only [TypeCtx.withRecs] at h; rw [h]; rfl
  | _, _, _, _, @Sub.recFunc _ i fin sups ps rs h, hΔ, _, _ => by
    subst hΔ
    have hi : i < subs.length := by
      have := (List.getElem?_eq_some_iff.1 h).1
      simpa [TypeCtx.withRecs, Ty.length] using this
    simp only [Ty.subst, unrollSubst, hi, ↓reduceIte, Option.getD_some]
    refine .defFunc (ps := ps.subst (unrollSubst subs)) (rs := rs.subst (unrollSubst subs))
      (.mk (fin := fin) (sups := sups.subst (unrollSubst subs)) ?_)
    rw [unrolldt_defn]; simp only [TypeCtx.withRecs] at h; rw [h]; rfl
  | _, _, _, _, @Sub.recSub _ i j fin sups ct u h hj, hΔ, _, hb => by
    subst hΔ
    have hi : i < subs.length := by
      have := (List.getElem?_eq_some_iff.1 h).1
      simpa [TypeCtx.withRecs, Ty.length] using this
    obtain ⟨D', hD'⟩ : ∃ D', u.subst (unrollSubst subs) = .dt D' := by
      have hu := hb.use_inv
      cases u with
      | idx x => cases hu with | idx hx => simp [TypeCtx.withRecs] at hx
      | recv j' =>
        cases hu with
        | recv hj' =>
          have : j' < subs.length := by
            have := (List.getElem?_eq_some_iff.1 hj').1
            simpa [TypeCtx.withRecs, Ty.length] using this
          exact ⟨.defn (.group subs) j', by simp [Ty.subst, unrollSubst, this]⟩
      | dt e => exact ⟨e, Ty.recFree_dt e _ (unrollSubst_idxAgg subs)⟩
    simp only [Ty.subst, unrollSubst, hi, ↓reduceIte, Option.getD_some]
    rw [show u.subst (unrollSubst subs) = .dt D' from hD']
    refine .defDef (.defSuper (fin := fin) (sups := sups.subst (unrollSubst subs))
      (ct := ct.subst (unrollSubst subs)) (j := j) (u := .dt D') ?_ ?_ .heapRefl)
    · rw [unrolldt_defn]; simp only [TypeCtx.withRecs] at h; rw [h]; rfl
    · rw [Ty.toList_subst, List.getElem?_map, hj]; simp [hD']
  | _, _, _, _, @Sub.none _ h' hs hbot, hΔ, _, hb => by
    have ih := Sub.substRecsAgg hg hs hΔ hb (.abs _)
    refine .none ih ?_
    cases h' <;> simp [Ty.subst] at hbot ⊢
  | _, _, _, _, @Sub.nofunc _ h' hs hbot, hΔ, _, hb => by
    have ih := Sub.substRecsAgg hg hs hΔ hb (.abs _)
    refine .nofunc ih ?_
    cases h' <;> simp [Ty.subst] at hbot ⊢
  | _, _, _, _, @Sub.noexn _ h' hs hbot, hΔ, _, hb => by
    have ih := Sub.substRecsAgg hg hs hΔ hb (.abs _)
    refine .noexn ih ?_
    cases h' <;> simp [Ty.subst] at hbot ⊢
  | _, _, _, _, @Sub.noextern _ h' hs hbot, hΔ, _, hb => by
    have ih := Sub.substRecsAgg hg hs hΔ hb (.abs _)
    refine .noextern ih ?_
    cases h' <;> simp [Ty.subst] at hbot ⊢
  | _, _, _, _, .bot, hΔ, _, _ => .bot
  | _, _, _, _, .refNonNull h, hΔ, ha, hb => .refNonNull (Sub.substRecsAgg hg h hΔ ha.ref_inv hb.ref_inv)
  | _, _, _, _, .refNull h, hΔ, ha, hb => .refNull (Sub.substRecsAgg hg h hΔ ha.ref_inv hb.ref_inv)
  | _, _, _, _, .num, hΔ, _, _ => .num
  | _, _, _, _, .vec, hΔ, _, _ => .vec
  | _, _, _, _, .refv h, hΔ, ha, hb => .refv (Sub.substRecsAgg hg h hΔ ha.refv_inv hb.refv_inv)
  | _, _, _, _, .botv, hΔ, _, _ => .botv
  | _, _, _, _, .val h, hΔ, ha, hb => .val (Sub.substRecsAgg hg h hΔ ha.val_inv hb.val_inv)
  | _, _, _, _, .pack, hΔ, _, _ => .pack
  | _, _, _, _, .fieldConst h, hΔ, ha, hb =>
    .fieldConst (Sub.substRecsAgg hg h hΔ ha.field_inv hb.field_inv)
  | _, _, _, _, .fieldVar h₁ h₂, hΔ, ha, hb =>
    .fieldVar (Sub.substRecsAgg hg h₁ hΔ ha.field_inv hb.field_inv)
      (Sub.substRecsAgg hg h₂ hΔ hb.field_inv ha.field_inv)
  | _, _, _, _, @Sub.struct _ fs₁ extra fs₂ h, hΔ, ha, hb => by
    have ih := Sub.substRecsAgg hg h hΔ (TyOk.app_left ha.struct_inv) hb.struct_inv
    simp only [Ty.subst, Ty.subst_appAgg]
    exact .struct ih
  | _, _, _, _, .array h, hΔ, ha, hb => .array (Sub.substRecsAgg hg h hΔ ha.array_inv hb.array_inv)
  | _, _, _, _, .func hp hr, hΔ, ha, hb =>
    .func (Sub.substRecsAgg hg hp hΔ hb.func_inv.1 ha.func_inv.1)
      (Sub.substRecsAgg hg hr hΔ ha.func_inv.2 hb.func_inv.2)
  | _, _, _, _, @Sub.defRefl _ d₁ d₂ h, hΔ, _, _ => by
    subst hΔ
    simp only [TypeCtx.withRecs] at h
    have e : d₁ = d₂ := by
      have h' : d₁.clos [] = d₂.clos [] := h
      rwa [Ty.clos_nilAgg, Ty.clos_nilAgg] at h'
    subst e
    exact .defRefl rfl
  | _, _, _, _, @Sub.defSuper _ d₁ d₂ fin sups ct j u h hj hs, hΔ, ha, hb => by
    have hu := TyOk.unroll_super ha h (List.mem_of_getElem? hj)
    have ih := Sub.substRecsAgg hg hs hΔ hu (.use (.dt hb))
    have hnr := TyOk.unroll_super_not_recvAgg ha h (List.mem_of_getElem? hj)
    have hus : u.subst (unrollSubst subs) = u := by
      cases u with
      | idx x => rfl
      | recv i => exact absurd rfl (hnr i)
      | dt e => exact Ty.recFree_dt e _ (unrollSubst_idxAgg subs)
    simp only [Ty.subst, hus, Ty.recFree_def d₂ _ (unrollSubst_idxAgg subs)] at ih
    rw [Ty.recFree_def d₁ _ (unrollSubst_idxAgg subs), Ty.recFree_def d₂ _ (unrollSubst_idxAgg subs)]
    exact .defSuper h hj ih
  | _, _, _, _, .nil, hΔ, _, _ => .nil
  | _, _, _, _, .cons h hl, hΔ, ha, hb =>
    .cons (Sub.substRecsAgg hg h hΔ ha.cons_inv.1 hb.cons_inv.1)
      (Sub.substRecsAgg hg hl hΔ ha.cons_inv.2 hb.cons_inv.2)

/-- One declared-supertype step of a valid defined type: its expansion is a
subtype of the supertype's. -/
theorem expand_super_subAgg {d d' : DefType} {u : CTypeUse} (hd : TyOk {} d)
    (hu : u ∈ supersOf d) (hr : ({} : TypeCtx).resolve u = some d') {c c' : CCompType}
    (hc : Expand d c) (hc' : Expand d' c') : Sub {} c c' := by
  cases hd with
  | @defn _ subs i hg hi =>
    have hi' : i < subs.toList.length := by simpa [Ty.length] using hi
    have hst : subs.toList[i]? = some subs.toList[i] := List.getElem?_eq_getElem hi'
    generalize subs.toList[i] = st at hst
    have hso := GroupOk2.get subs hg hst
    rw [Nat.zero_add] at hso
    have hun := unrolldt_defn subs i
    rw [hst, Option.map_some] at hun
    rw [supersOf_of_unroll hun] at hu
    cases hso with
    | noSuper hct => simp [Ty.subst, Ty.supers] at hu
    | @oneSuper _ fin u0 ct₀ _ sups' ct'₀ hu0 hb hunroll hct hsub =>
      simp only [Ty.subst, Ty.supers, Ty.toList_cons, Ty.toList_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hu
      have hc₀ : Expand (.defn (.group subs) i) (ct₀.subst (unrollSubst subs)) := .mk hun
      cases Expand.func_eq hc hc₀
      subst hu
      cases u0 with
      | idx x => cases hu0 with | idx hx => simp [TypeCtx.withRecs] at hx
      | recv j =>
        cases hu0 with
        | recv hj =>
          have hjl : j < subs.length := by
            have := (List.getElem?_eq_some_iff.1 hj).1
            simpa [TypeCtx.withRecs, Ty.length] using this
          simp only [Ty.subst, unrollSubst, hjl, ↓reduceIte, Option.getD_some,
            TypeCtx.resolve, Option.some.injEq] at hr
          subst hr
          simp only [TypeCtx.unrollUse, TypeCtx.withRecs] at hunroll
          have h2 := unrolldt_defn subs j
          rw [hunroll, Option.map_some] at h2
          have hc₁ : Expand (.defn (.group subs) j) (ct'₀.subst (unrollSubst subs)) := .mk h2
          cases Expand.func_eq hc' hc₁
          have hso' := GroupOk2.get subs hg hunroll
          exact Sub.substRecsAgg hg hsub rfl hct (SubOk2.body hso')
      | dt e =>
        rw [Ty.recFree_dt e _ (fun _ => rfl)] at hr
        simp only [TypeCtx.resolve, Option.some.injEq] at hr
        subst hr
        have he : TyOk {} e :=
          TyOk.def_congr (Δ₁ := ({} : TypeCtx).withRecs subs.toList) (Δ₂ := {}) rfl hu0.dt_inv
        simp only [TypeCtx.unrollUse] at hunroll
        rw [Expand.func_eq hc' (.mk hunroll)]
        have hok : TyOk {} ct'₀ := Expand.tyOk he (.mk hunroll)
        have hok' : TyOk (({} : TypeCtx).withRecs subs.toList) ct'₀ :=
          TyOk.wkRecsAgg subs.toList hok rfl
        have := Sub.substRecsAgg hg hsub rfl hct hok'
        rwa [TyOk.subst_emptyAgg (unrollSubst_idxAgg subs) ct'₀ hok] at this

theorem reach_expand_subAgg {d e : DefType} (h : ({} : TypeCtx).Reach d e) :
    TyOk {} d → ∀ {c c' : CCompType}, Expand d c → Expand e c' → Sub {} c c' := by
  induction h with
  | refl d =>
    intro _ c c' hc hc'
    cases Expand.func_eq hc hc'
    exact Sub.refl {} (k := .comp) trivial c
  | @step d d' e u hu hr _ ih =>
    intro hd c c' hc hc'
    obtain ⟨hok', -, hk⟩ := TypeCtx.super_step TypeCtx.ok_empty hd hu hr
    obtain ⟨st, hst⟩ : ∃ st, unrolldt d' = some st := by
      cases hc with
      | mk hu' =>
        have : defKind d' = some (compAbs c) := by rw [hk]; exact defKind_of_unroll hu'
        simp only [defKind, Option.map_eq_some_iff] at this
        obtain ⟨st, hst, -⟩ := this
        exact ⟨st, hst⟩
    cases st with
    | sub fin sups c'' =>
      have hc'' : Expand d' c'' := .mk hst
      exact Sub.trans TypeCtx.ok_empty (Expand.tyOk hok' hc'')
        (expand_super_subAgg hd hu hr hc hc'') (ih hok' hc'' hc')

/-- Subtyping between valid defined types (as heap types) implies subtyping of
their expansions. -/
theorem heap_def_subAgg {d₁ d₂ : DefType}
    (h : Sub {} (Ty.use (.dt d₁) : CHeapType) (.use (.dt d₂))) (h₁ : TyOk {} d₁)
    (h₂ : TyOk {} d₂) {c₁ c₂ : CCompType} (hc₁ : Expand d₁ c₁) (hc₂ : Expand d₂ c₂) :
    Sub {} c₁ c₂ := by
  have hck := Sub.complete TypeCtx.ok_empty rfl h (.use (.dt h₁)) (.use (.dt h₂))
  have hdef : ({} : TypeCtx).checkDef d₁ d₂ = true := by
    simpa [Sub.checkK, TypeCtx.checkHeap, TypeCtx.resolve] using hck
  obtain ⟨e, he, hce⟩ := TypeCtx.checkDef_exists hdef
  have : e = d₂ := by
    have h' : e.clos [] = d₂.clos [] := hce
    rwa [Ty.clos_nilAgg, Ty.clos_nilAgg] at h'
  subst this
  exact reach_expand_subAgg he h₁ hc₁ hc₂

theorem RefOk.def_subAgg {s : Store H} {r : Ref} {d₀ d : DefType} {n : Bool}
    (hr : RefOk s r (.ref n (Ty.defHeap d))) (h₀ : Ref.type? s r = some (.ref false (Ty.defHeap d₀)))
    (hd₀ : TyOk {} d₀) (hd : TyOk {} d) {c₀ c : CCompType} (hc₀ : Expand d₀ c₀)
    (hc : Expand d c) : Sub {} c₀ c := by
  obtain ⟨rt₀, e, hrt, -⟩ := hr.principal
  rw [h₀] at e; cases e
  rcases hrt with h | ⟨-, hsub⟩
  · simp only [Ty.ref.injEq, Ty.defHeap, Ty.use.injEq, Ty.dt.injEq] at h
    obtain ⟨-, rfl⟩ := h
    cases Expand.func_eq hc₀ hc
    exact Sub.refl {} (k := .comp) trivial _
  · cases hsub with
    | refNonNull h => exact heap_def_subAgg h hd₀ hd hc₀ hc
    | refNull h => exact heap_def_subAgg h hd₀ hd hc₀ hc

/-! ## Heap-type classes (copied from the reference-family helpers) -/

/-! ## Composite kinds of defined types -/

/-- The abstract heap type directly above a composite type. -/
def compKindAgg : CCompType → AbsHeapType
  | .struct _ => .struct
  | .array _ => .array
  | .func _ _ => .func

theorem compKind_substAgg (σ : Subst) (ct : CCompType) : compKindAgg (ct.subst σ) = compKindAgg ct := by
  cases ct <;> rfl

/-- The kind of a defined type (`struct`, `array` or `func`), if it unrolls. -/
def defKindAgg (d : DefType) : Option AbsHeapType := (unrolldt d).map fun st => compKindAgg st.body

theorem expand_defKindAgg {d : DefType} {ct : CCompType} (h : Expand d ct) :
    defKindAgg d = some (compKindAgg ct) := by
  cases h with | mk h => simp [defKindAgg, h, Ty.body]

theorem defKind_substAgg (σ : Subst) (hσ : ∀ i, σ (.recv i) = none)
    (hσu : ∀ x u, σ (.idx x) = some u → u.RecFree) (d : DefType) :
    defKindAgg (d.subst σ) = defKindAgg d := by
  simp only [defKindAgg, unrolldt_subst σ hσ hσu, Option.map_map]
  cases unrolldt d with
  | none => rfl
  | some st =>
    cases st with
    | sub fin sups b => simp [Ty.subst, Ty.body, compKind_substAgg]

theorem defKind_closAgg (T : List DefType) (d : DefType) : defKindAgg (d.clos T) = defKindAgg d :=
  defKind_substAgg _ (fun _ => rfl)
    (fun x u h => by
      simp only [Subst.all, List.getElem?_map] at h
      cases hx : (closDefTypes T)[x]? with
      | none => simp [hx] at h
      | some e => simp [hx] at h; subst h; exact Ty.recFree_dt e) d

/-- The kind of a type use; `REC` uses have none (they never occur above a
runtime type). -/
def useKindAgg (Δ : TypeCtx) : CTypeUse → Option AbsHeapType
  | .dt d => defKindAgg d
  | .idx x => Δ.types[x]? >>= defKindAgg
  | .recv _ => none

/-- `absUpAgg c a`: `a` is an abstract heap type above the class `c`. -/
def absUpAgg : AbsHeapType → AbsHeapType → Bool
  | .i31, .i31 | .i31, .eq | .i31, .any => true
  | .struct, .struct | .struct, .eq | .struct, .any => true
  | .array, .array | .array, .eq | .array, .any => true
  | .eq, .eq | .eq, .any => true
  | .any, .any => true
  | .func, .func => true
  | .exn, .exn => true
  | .extern, .extern => true
  | _, _ => false

/-- The heap types above class `c`. -/
def HeapUpAgg (Δ : TypeCtx) (c : AbsHeapType) : CHeapType → Prop
  | .abs a => absUpAgg c a = true
  | .use u => useKindAgg Δ u = some c
  | .bot => False

/-- `HeapUpAgg` with validity of a defined type at the source (needed to follow
declared supertypes). -/
def HeapUpVAgg (Δ : TypeCtx) (c : AbsHeapType) (h : CHeapType) : Prop :=
  HeapUpAgg Δ c h ∧ ∀ d, h = .use (.dt d) → TyOk Δ d

theorem HeapUpVAgg.of_ok {Δ : TypeCtx} {c : AbsHeapType} {h : CHeapType} (hu : HeapUpAgg Δ c h)
    (hok : TyOk Δ h) : HeapUpVAgg Δ c h := by
  refine ⟨hu, fun d hd => ?_⟩
  subst hd
  cases hok with | use h => cases h with | dt h => exact h

/-- A valid defined type's declared supertypes are valid and of the same kind. -/
theorem TyOk.super_kindAgg {Δ : TypeCtx} {d : DefType} (hd : TyOk Δ d) {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} (hu : unrolldt d = some (.sub fin sups ct))
    {j : Nat} {u : CTypeUse} (hj : sups.toList[j]? = some u) :
    useKindAgg Δ u = some (compKindAgg ct) ∧ TyOk Δ (.use u) := by
  cases hd with
  | @defn _ subs i hg hi =>
    simp only [unrolldt, unrollrt, Ty.subs] at hu
    rw [Ty.toList_subst, List.getElem?_map] at hu
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
        cases hso with
        | noSuper =>
          have := (List.getElem?_eq_some_iff.1 hj).1
          exact absurd this (Nat.not_lt_zero _)
        | @oneSuper _ _ u0 _ _ sups' ct' hu0 hb hunroll hct hsub =>
          simp only [Ty.subst, Ty.toList_cons, Ty.toList_nil] at hj
          have hj0 : j = 0 := by
            rcases j with _ | j
            · rfl
            · simp at hj
          subst hj0
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          have hk : compKindAgg ct0 = compKindAgg ct' := by cases hsub <;> rfl
          rw [compKind_substAgg, hk]
          cases u0 with
          | idx x =>
            cases hu0 with
            | idx hx =>
              try simp only [Ty.subst, Option.getD_none]
              refine ⟨?_, .use (.idx hx)⟩
              obtain ⟨e, hx'⟩ : ∃ e, Δ.types[x]? = some e := ⟨_, hx⟩
              have h2 : (Δ.withRecs subs.toList).unrollUse (.idx x) = unrolldt e := by
                simp [TypeCtx.unrollUse, TypeCtx.withRecs, hx']
              rw [h2] at hunroll
              simp only [useKindAgg, hx']
              show defKindAgg e = _
              simp [defKindAgg, hunroll, Ty.body]
          | recv j' =>
            cases hu0 with
            | recv hr =>
              have hj' : j' < subs.length := by
                have := (List.getElem?_eq_some_iff.1 hr).1
                simpa [TypeCtx.withRecs, Ty.length] using this
              simp only [Ty.subst, hj', ite_true, Option.getD_some]
              refine ⟨?_, .use (.dt (.defn hg hj'))⟩
              simp only [TypeCtx.unrollUse, TypeCtx.withRecs] at hunroll
              simp only [useKindAgg, defKindAgg, unrolldt, unrollrt, Ty.subs, Ty.toList_subst,
                List.getElem?_map, hunroll, Option.map_some, Ty.subst, Ty.body, compKind_substAgg]
          | dt e =>
            rw [Ty.recFree_dt e _ (fun _ => rfl)]
            cases hu0 with
            | dt he =>
              refine ⟨?_, .use (.dt (TyOk.def_congr (Δ₁ := Δ.withRecs subs.toList) (Δ₂ := Δ) rfl he))⟩
              simp only [TypeCtx.unrollUse] at hunroll
              simp [useKindAgg, defKindAgg, hunroll, Ty.body]

/-- Motive of `Sub.up`, by sort. -/
def UpMotiveAgg (Δ : TypeCtx) : (k : TKind) → Ty k → Ty k → Prop
  | .heap, a, b => ∀ c, HeapUpVAgg Δ c a → HeapUpAgg Δ c b
  | .def, a, b => TyOk Δ a → ∀ c, defKindAgg a = some c → defKindAgg b = some c
  | _, _, _ => True

/-- **The hierarchy is respected by subtyping.** In a context whose defined
types are valid, the heap types above a valid member of class `c` stay in `c`'s
upward set. -/
theorem Sub.upAgg {Δ : TypeCtx} (hT : ∀ (x : Nat) (d : DefType), Δ.types[x]? = some d → TyOk Δ d) :
    ∀ {k : TKind} {a b : Ty k}, Sub Δ a b → UpMotiveAgg Δ k a b
  | _, _, _, .heapRefl => by intro c hc; exact hc.1
  | _, _, _, .heapTrans hok h₁ h₂ => by
    have ih₁ := Sub.upAgg hT h₁
    have ih₂ := Sub.upAgg hT h₂
    dsimp only [UpMotiveAgg] at ih₁ ih₂ ⊢
    intro c hc
    exact ih₂ c (HeapUpVAgg.of_ok (ih₁ c hc) hok)
  | _, _, _, .eqAny => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .i31Eq => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .structEq => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .arrayEq => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .defStruct h => by
    intro c hc; have := hc.1
    simp only [HeapUpAgg, useKindAgg, expand_defKindAgg h, compKindAgg, Option.some.injEq] at this
    subst this; rfl
  | _, _, _, .defArray h => by
    intro c hc; have := hc.1
    simp only [HeapUpAgg, useKindAgg, expand_defKindAgg h, compKindAgg, Option.some.injEq] at this
    subst this; rfl
  | _, _, _, .defFunc h => by
    intro c hc; have := hc.1
    simp only [HeapUpAgg, useKindAgg, expand_defKindAgg h, compKindAgg, Option.some.injEq] at this
    subst this; rfl
  | _, _, _, .defDef h => by
    have ih := Sub.upAgg hT h
    dsimp only [UpMotiveAgg] at ih ⊢
    intro c hc
    exact ih (hc.2 _ rfl) c hc.1
  | _, _, _, .idxL hx hs => by
    have ih := Sub.upAgg hT hs
    dsimp only [UpMotiveAgg] at ih ⊢
    intro c hc
    refine ih c ⟨?_, fun d hd => ?_⟩
    · have := hc.1
      simp only [HeapUpAgg, useKindAgg, hx] at this ⊢
      exact this
    · cases hd; exact hT _ _ hx
  | _, _, _, .idxR hx hs => by
    have ih := Sub.upAgg hT hs
    dsimp only [UpMotiveAgg] at ih ⊢
    intro c hc
    have := ih c hc
    simp only [HeapUpAgg, useKindAgg, hx] at this ⊢
    exact this
  | _, _, _, .recStruct _ => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg, useKindAgg])
  | _, _, _, .recArray _ => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg, useKindAgg])
  | _, _, _, .recFunc _ => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg, useKindAgg])
  | _, _, _, .recSub _ _ => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg, useKindAgg])
  | _, _, _, .none _ _ => by intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .nofunc _ _ => by intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .noexn _ _ => by intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .noextern _ _ => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .bot => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg])
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
  | _, _, _, .defRefl h => by
    intro _ c hc
    rw [← defKind_closAgg Δ.types, ← h, defKind_closAgg]
    exact hc
  | _, _, _, @Sub.defSuper _ _ _ _ _ ct _ _ hu hj hs => by
    intro hd c hc
    obtain ⟨hk, hok⟩ := TyOk.super_kindAgg hd hu hj
    have ih := Sub.upAgg hT hs
    dsimp only [UpMotiveAgg] at ih
    have hc' : compKindAgg ct = c := by simpa [defKindAgg, hu, Ty.body] using hc
    have := ih _ (HeapUpVAgg.of_ok hk hok)
    rw [← hc']
    simpa [HeapUpAgg, useKindAgg] using this
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ => trivial


/-! ## Removing `RECS` from subtyping derivations between runtime types -/

/-- Motive of `Sub.noRecsAgg`, by sort. -/
def NoRecMotiveAgg (Δ : TypeCtx) : (k : TKind) → Ty k → Ty k → Prop
  | .heap, a, b => ∀ c, HeapUpVAgg Δ c a → Sub { Δ with recs := [] } a b
  | .def, a, b => TyOk Δ a → Sub { Δ with recs := [] } a b
  | _, _, _ => True

theorem TyOk.noRecs_heapAgg {Δ : TypeCtx} {c : AbsHeapType} {h : CHeapType}
    (hu : HeapUpAgg Δ c h) (hok : TyOk Δ h) : TyOk { Δ with recs := [] } h := by
  cases h with
  | abs a => exact .abs a
  | bot => exact absurd hu (by simp [HeapUpAgg])
  | use u =>
    cases u with
    | idx x => cases hok with | use h => cases h with | idx hx => exact .use (.idx hx)
    | recv i => simp [HeapUpAgg, useKindAgg] at hu
    | dt d =>
      cases hok with
      | use h => cases h with | dt h => exact .use (.dt (TyOk.def_congr (Δ₁ := Δ) (Δ₂ := { Δ with recs := [] }) rfl h))

/-- Subtyping from a valid type in a heap-type class never uses `RECS`. -/
theorem Sub.noRecsAgg {Δ : TypeCtx}
    (hT : ∀ (x : Nat) (d : DefType), Δ.types[x]? = some d → TyOk Δ d) :
    ∀ {k : TKind} {a b : Ty k}, Sub Δ a b → NoRecMotiveAgg Δ k a b
  | _, _, _, .heapRefl => by intro _ _; exact .heapRefl
  | _, _, _, .heapTrans hok h₁ h₂ => by
    have ih₁ := Sub.noRecsAgg hT h₁
    have ih₂ := Sub.noRecsAgg hT h₂
    dsimp only [NoRecMotiveAgg] at ih₁ ih₂ ⊢
    intro c hc
    have hup := Sub.upAgg hT h₁
    dsimp only [UpMotiveAgg] at hup
    have hu' := hup c hc
    exact .heapTrans (TyOk.noRecs_heapAgg hu' hok) (ih₁ c hc) (ih₂ c (HeapUpVAgg.of_ok hu' hok))
  | _, _, _, .eqAny => by intro _ _; exact .eqAny
  | _, _, _, .i31Eq => by intro _ _; exact .i31Eq
  | _, _, _, .structEq => by intro _ _; exact .structEq
  | _, _, _, .arrayEq => by intro _ _; exact .arrayEq
  | _, _, _, .defStruct h => by intro _ _; exact .defStruct h
  | _, _, _, .defArray h => by intro _ _; exact .defArray h
  | _, _, _, .defFunc h => by intro _ _; exact .defFunc h
  | _, _, _, .defDef h => by
    have ih := Sub.noRecsAgg hT h
    dsimp only [NoRecMotiveAgg] at ih ⊢
    intro c hc
    exact .defDef (ih (hc.2 _ rfl))
  | _, _, _, .idxL hx hs => by
    have ih := Sub.noRecsAgg hT hs
    dsimp only [NoRecMotiveAgg] at ih ⊢
    intro c hc
    refine .idxL hx (ih c ⟨?_, fun d hd => ?_⟩)
    · have := hc.1
      simp only [HeapUpAgg, useKindAgg, hx] at this ⊢
      exact this
    · cases hd; exact hT _ _ hx
  | _, _, _, .idxR hx hs => by
    have ih := Sub.noRecsAgg hT hs
    dsimp only [NoRecMotiveAgg] at ih ⊢
    intro c hc
    exact .idxR hx (ih c hc)
  | _, _, _, .recStruct _ => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg, useKindAgg])
  | _, _, _, .recArray _ => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg, useKindAgg])
  | _, _, _, .recFunc _ => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg, useKindAgg])
  | _, _, _, .recSub _ _ => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg, useKindAgg])
  | _, _, _, .none _ _ => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .nofunc _ _ => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .noexn _ _ => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .noextern _ _ => by
    intro c hc; have := hc.1; revert this; cases c <;> simp [HeapUpAgg, absUpAgg]
  | _, _, _, .bot => by intro c hc; exact absurd hc.1 (by simp [HeapUpAgg])
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
  | _, _, _, .defRefl h => by intro _; exact .defRefl h
  | _, _, _, @Sub.defSuper _ _ _ _ _ ct _ _ hu hj hs => by
    intro hd
    obtain ⟨hk, hok⟩ := TyOk.super_kindAgg hd hu hj
    have ih := Sub.noRecsAgg hT hs
    dsimp only [NoRecMotiveAgg] at ih
    exact .defSuper hu hj (ih _ (HeapUpVAgg.of_ok hk hok))
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ => trivial

/-! ## Runtime subtyping from context subtyping -/

/-- Principal heap types of non-null references. -/
def RtHeapAgg : CHeapType → Prop
  | .abs a => a = .i31 ∨ a = .exn ∨ a = .any ∨ a = .extern
  | .use (.dt d) => TyOk {} d
  | _ => False

theorem RtHeapAgg.upV {Δ : TypeCtx} {h : CHeapType} (hr : RtHeapAgg h) :
    ∃ c, HeapUpVAgg Δ c h := by
  cases h with
  | abs a =>
    refine ⟨a, ?_, fun d hd => by cases hd⟩
    simp only [RtHeapAgg] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rfl
  | bot => exact absurd hr id
  | use u =>
    cases u with
    | dt d =>
      have hr' : TyOk {} d := hr
      obtain ⟨c, hc⟩ : ∃ c, defKindAgg d = some c := by
        cases hr' with
        | @defn _ subs i hg hi =>
          have hi' : i < subs.toList.length := by simpa [Ty.length] using hi
          exact ⟨compKindAgg ((subs.toList[i]).subst (unrollSubst subs)).body,
            by simp [defKindAgg, unrolldt_defn, List.getElem?_eq_getElem hi']⟩
      exact ⟨c, hc, fun d' hd' => by cases hd'; exact TyOk.ofEmptyAgg hr' _⟩
    | idx x => exact absurd hr id
    | recv i => exact absurd hr id

theorem Ty.clos_closedAgg {k : TKind} {t : Ty k} (h : t.Closed) (T : List DefType) :
    t.clos T = t := by
  simp only [Ty.clos, Ty.substAll]
  exact Ty.subst_closed t _ (fun _ => rfl) h

theorem reach_emptyAgg {Δ : TypeCtx} {d e : DefType} (h : Δ.Reach d e) :
    TyOk {} d → ({} : TypeCtx).Reach d e ∧ TyOk {} e := by
  induction h with
  | refl d => intro hd; exact ⟨.refl d, hd⟩
  | @step d d' e u hu hr _ ih =>
    intro hd
    obtain ⟨fin, sups, ct, j, hun, hj⟩ := supersOf_mem hu
    have hok := TyOk.unroll_super hd hun (List.mem_of_getElem? hj)
    cases u with
    | idx x => cases hok with | use h => cases h with | idx hx => simp at hx
    | recv i => cases hok with | use h => cases h with | recv hi => simp at hi
    | dt d₀ =>
      simp only [TypeCtx.resolve, Option.some.injEq] at hr
      subst hr
      have hd' : TyOk {} d₀ := hok.use_inv.dt_inv
      obtain ⟨h1, h2⟩ := ih hd'
      exact ⟨.step hu rfl h1, h2⟩

/-- Context subtyping from a principal (runtime) heap type to a runtime heap
type holds at run time. -/
theorem heap_rtAgg {Δ : TypeCtx} (hΔ : Δ.Ok) {h₀ h' : CHeapType} (hr : RtHeapAgg h₀)
    (hs : Sub Δ h₀ h') (hok : TyOk {} h') : Sub {} h₀ h' := by
  have hT : ∀ (x : Nat) (d : DefType), Δ.types[x]? = some d → TyOk Δ d :=
    fun x d hx => (hΔ d (List.mem_of_getElem? hx)).2
  obtain ⟨c, hc⟩ := hr.upV (Δ := Δ)
  have hnr := Sub.noRecsAgg hT hs
  dsimp only [NoRecMotiveAgg] at hnr
  have h1 := hnr c hc
  have hΔ' : ({ Δ with recs := [] } : TypeCtx).Ok := fun d hd =>
    ⟨(hΔ d hd).1, TyOk.def_congr (Δ₁ := Δ) (Δ₂ := { Δ with recs := [] }) rfl (hΔ d hd).2⟩
  have hok₀ : TyOk ({ Δ with recs := [] } : TypeCtx) h₀ := by
    cases h₀ with
    | abs a => exact .abs a
    | bot => exact absurd hr id
    | use u =>
      cases u with
      | dt d => exact .use (.dt (TyOk.ofEmptyAgg (show TyOk {} d from hr) _))
      | idx x => exact absurd hr id
      | recv i => exact absurd hr id
  have hck := Sub.complete hΔ' rfl h1 hok₀ (TyOk.ofEmptyAgg hok _)
  cases h₀ with
  | bot => exact absurd hr id
  | abs a =>
    cases h' with
    | abs b => exact absSub_sound (by simpa [Sub.checkK, TypeCtx.checkHeap] using hck)
    | bot => simp [Sub.checkK, TypeCtx.checkHeap] at hck
    | use u =>
      simp only [RtHeapAgg] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [Sub.checkK, TypeCtx.checkHeap, botTop] at hck
  | use u₀ =>
    cases u₀ with
    | idx x => exact absurd hr id
    | recv i => exact absurd hr id
    | dt D =>
      have hD : TyOk {} D := hr
      cases h' with
      | bot => simp [Sub.checkK, TypeCtx.checkHeap] at hck
      | abs b =>
        exact Sub.check_sound (Δ := {}) (k := .heap)
          (by simpa [Sub.check, Sub.checkK, TypeCtx.checkHeap, TypeCtx.checkUseAbs,
            TypeCtx.resolve] using hck)
      | use u =>
        cases u with
        | idx x => cases hok with | use h => cases h with | idx hx => simp at hx
        | recv i => cases hok with | use h => cases h with | recv hi => simp at hi
        | dt D' =>
          have hD' : TyOk {} D' := hok.use_inv.dt_inv
          have hdef : ({ Δ with recs := [] } : TypeCtx).checkDef D D' = true := by
            simpa [Sub.checkK, TypeCtx.checkHeap, TypeCtx.resolve] using hck
          obtain ⟨e, he, hce⟩ := TypeCtx.checkDef_exists hdef
          obtain ⟨he', heok⟩ := reach_emptyAgg he hD
          rw [Ty.clos_closedAgg (TyOk.closed_of_emptyAgg heok),
            Ty.clos_closedAgg (TyOk.closed_of_emptyAgg hD')] at hce
          subst hce
          exact .defDef (TypeCtx.Reach.sub he' rfl)

theorem Ref.type?_rtAgg {s : Store H} (hs : StoreOk s) (hD : StoreDefsOkAgg s) {r : Ref}
    {rt₀ : CRefType} (e : Ref.type? s r = some rt₀) (hr : r ≠ .null) :
    ∃ h₀, rt₀ = .ref false h₀ ∧ RtHeapAgg h₀ := by
  cases r with
  | null => exact absurd rfl hr
  | i31 b => cases e; exact ⟨_, rfl, .inl rfl⟩
  | struct a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨si, hsi, rfl⟩ := e
    exact ⟨_, rfl, show TyOk {} si.type from hD.1 si (List.mem_of_getElem? hsi)⟩
  | array a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨ai, hai, rfl⟩ := e
    exact ⟨_, rfl, show TyOk {} ai.type from hD.2 ai (List.mem_of_getElem? hai)⟩
  | func a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨fi, hfi, rfl⟩ := e
    refine ⟨_, rfl, show TyOk {} fi.type from ?_⟩
    cases hs.funcs fi (List.mem_of_getElem? hfi) with
    | wasm hdt => exact hdt
    | host hdt => exact hdt
  | exn a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨_, -, rfl⟩ := e
    exact ⟨_, rfl, .inr (.inl rfl)⟩
  | host a => cases e; exact ⟨_, rfl, .inr (.inr (.inl rfl))⟩
  | extern r => cases e; exact ⟨_, rfl, .inr (.inr (.inr rfl))⟩

theorem ref_rtAgg {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    (hD : StoreDefsOkAgg s) {r : Ref} {rt₀ rt' : CRefType} (e : Ref.type? s r = some rt₀)
    (hs : Sub C.toTypeCtx rt₀ rt') (hok : TyOk {} rt') : Sub {} rt₀ rt' := by
  have hΔ := hst.deltaOkAgg
  by_cases hr : r = .null
  · subst hr
    cases e
    cases hs with
    | refNull _ => exact .refNull .bot
  · obtain ⟨h₀, rfl, hrt⟩ := Ref.type?_rtAgg hst.1 hD e hr
    cases hs with
    | refNonNull h => exact .refNonNull (heap_rtAgg hΔ hrt h hok.ref_inv)
    | refNull h => exact .refNull (heap_rtAgg hΔ hrt h hok.ref_inv)

/-! ## Runtime typing of operands (foundational lemmas) -/

/-- **Runtime strengthening.** A value typed below a runtime type `T` in the
context of a typed frame is typed at `T` at run time. -/
theorem ValOk.ctxSubAgg {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    (hD : StoreDefsOkAgg s) {v : Val} {t T : CValType} (hv : ValOk s v t)
    (hs : Sub C.toTypeCtx t T) (hT : TyOk {} T) : ValOk s v T := by
  have hΔ := hst.deltaOkAgg
  cases hv with
  | num nv => cases hs; exact .num nv
  | vec b => cases hs; exact .vec b
  | @ref r rt h =>
    cases hs with
    | @refv _ _ rt' hs =>
      obtain ⟨rt₀, e, hrt, hx⟩ := h.principal
      have h₀ : RefOk s r rt₀ := RefOk.of_type? e hx
      have hs₀ : Sub C.toTypeCtx rt₀ rt' := by
        rcases hrt with rfl | ⟨hok, hsub⟩
        · exact hs
        · exact Sub.trans hΔ (TyOk.ofEmptyAgg hok _) (Sub.ofEmptyAgg hsub _) hs
      have hT' : TyOk {} rt' := TyOk.refv_inv hT
      exact .ref (.sub h₀ hT' (ref_rtAgg hst hD e hs₀ hT'))

/-- **Struct subtyping soundness.** A struct reference typed at a defined type
`d` points to an instance whose expansion is a structural subtype of `d`'s. -/
theorem RefOk.structSubAgg {s : Store H} (hs : StoreOk s) (hD : StoreDefsOkAgg s) {a : Nat}
    {n : Bool} {d : DefType} {fs : Ty (.list .field)}
    (hr : RefOk s (.struct a) (.ref n (Ty.defHeap d))) (hd : TyOk {} d)
    (he : Expand d (.struct fs)) :
    ∃ si fs', s.structs[a]? = some si ∧ Expand si.type (.struct fs') ∧
      Sub {} (Ty.struct fs' : CCompType) (Ty.struct fs) := by
  obtain ⟨rt₀, e, -, -⟩ := hr.principal
  simp only [Ref.type?, Option.map_eq_some_iff] at e
  obtain ⟨si, hsi, -⟩ := e
  obtain ⟨fs', hexp, -⟩ := hs.structs si (List.mem_of_getElem? hsi)
  exact ⟨si, fs', hsi, hexp, hr.def_subAgg (by simp [Ref.type?, hsi])
    (hD.1 si (List.mem_of_getElem? hsi)) hd hexp he⟩

/-- **Array subtyping soundness.** -/
theorem RefOk.arraySubAgg {s : Store H} (hs : StoreOk s) (hD : StoreDefsOkAgg s) {a : Nat}
    {n : Bool} {d : DefType} {ft : CFieldType}
    (hr : RefOk s (.array a) (.ref n (Ty.defHeap d))) (hd : TyOk {} d)
    (he : Expand d (.array ft)) :
    ∃ ai ft', s.arrays[a]? = some ai ∧ Expand ai.type (.array ft') ∧ Sub {} ft' ft := by
  obtain ⟨rt₀, e, -, -⟩ := hr.principal
  simp only [Ref.type?, Option.map_eq_some_iff] at e
  obtain ⟨ai, hai, -⟩ := e
  obtain ⟨ft', hexp, -⟩ := hs.arrays ai (List.mem_of_getElem? hai)
  have := hr.def_subAgg (by simp [Ref.type?, hai]) (hD.2 ai (List.mem_of_getElem? hai)) hd hexp he
  cases this with
  | array h => exact ⟨ai, ft', hai, hexp, h⟩

/-! ## Value-level helpers -/

theorem ValOk.i32Agg {s : Store H} (b : BitVec 32) : ValOk s (Val.i32 b) Ty.i32 := .num _

theorem ValOk.i32_eqAgg {s : Store H} {v : Val} (h : ValOk s v Ty.i32) : ∃ b, v = Val.i32 b := by
  rcases v with ⟨ty, b⟩ | b | r <;> cases h
  exact ⟨b, rfl⟩

theorem ValOk.subAgg {s : Store H} {v : Val} {t t' : CValType} (hv : ValOk s v t)
    (hs : Sub {} t t') (ht : TyOk {} t') : ValOk s v t' := by
  cases hv with
  | num v => cases hs; exact .num v
  | vec b => cases hs; exact .vec b
  | ref h =>
    cases hs with
    | refv hs => exact .ref (.sub h (TyOk.refv_inv ht) hs)

theorem FieldValOk.subAgg {s : Store H} {fv : FieldVal} {z z' : CStorageType}
    (h : FieldValOk s fv z) (hs : Sub {} z z') (ht : TyOk {} z') : FieldValOk s fv z' := by
  cases h with
  | val hv => cases hs with | val hs => exact .val (hv.subAgg hs (TyOk.val_inv ht))
  | pack p b => cases hs; exact .pack p b

theorem Sub.unpackAgg {Δ : TypeCtx} {z z' : CStorageType} (h : Sub Δ z z') :
    Sub Δ z.unpack z'.unpack := by
  cases h with
  | val h => exact h
  | pack => exact .num

theorem fieldUnpack_eqAgg (ft : CFieldType) : fieldUnpack ft = (fieldStorage ft).unpack := by
  cases ft; rfl

theorem packField_okAgg {s : Store H} {z : CStorageType} {v : Val} (hv : ValOk s v z.unpack) :
    FieldValOk s (packField z v) z := by
  cases z with
  | val t =>
    have : packField (.val t) v = .val v := by
      rcases v with ⟨⟨it⟩ | ⟨ft⟩, b⟩ | b | r <;> (try cases it) <;> rfl
    rw [this]; exact .val hv
  | pack p =>
    obtain ⟨b, rfl⟩ := ValOk.i32_eqAgg hv
    exact .pack p _

theorem unpackField_okAgg {s : Store H} (sx : Option Signedness) {fv : FieldVal}
    {z' z : CStorageType} (hfv : FieldValOk s fv z') (hz : Sub {} z' z) :
    ∃ t, ValOk s (unpackField sx fv) t ∧ Sub {} t z.unpack := by
  cases hfv with
  | val hv => cases hz with | val h => exact ⟨_, hv, h⟩
  | pack p b =>
    cases hz
    refine ⟨Ty.i32, ?_, .num⟩
    rcases sx with _ | ⟨_ | _⟩ <;> exact .num _

theorem defaultVal_okAgg {s : Store H} {t : CValType} {v : Val} (ht : TyOk {} t)
    (h : defaultVal? t = some v) : ValOk s v t := by
  cases t with
  | num nt =>
    cases nt with
    | int it => simp only [defaultVal?, Option.some.injEq] at h; subst h; exact .num _
    | float ft => simp only [defaultVal?, Option.some.injEq] at h; subst h; exact .num _
  | vec vt => cases vt; simp only [defaultVal?, Option.some.injEq] at h; subst h; exact .vec _
  | refv r =>
    cases r with
    | ref n hh =>
      cases n
      · simp [defaultVal?] at h
      · simp only [defaultVal?, Option.some.injEq] at h; subst h
        exact .ref (.sub .null (TyOk.refv_inv ht) (.refNull .bot))
  | botv => simp [defaultVal?] at h

theorem readField_okAgg {s : Store H} {z : CStorageType} {bytes : ByteArray} {off : Nat}
    {v : Val} (h : readField? z bytes off = some v) : ValOk s v z.unpack := by
  cases z with
  | val t =>
    cases t with
    | num nt =>
      simp only [readField?, Option.map_eq_some_iff] at h
      obtain ⟨c, -, rfl⟩ := h
      exact .num _
    | vec vt =>
      cases vt
      simp only [readField?, Option.map_eq_some_iff] at h
      obtain ⟨c, -, rfl⟩ := h
      exact .vec _
    | refv r => simp [readField?] at h
    | botv => simp [readField?] at h
  | pack p =>
    simp only [readField?, Option.map_eq_some_iff] at h
    obtain ⟨c, -, rfl⟩ := h
    exact .num _

theorem mapM_forall₂Agg {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {vs : List β}, l.mapM g = some vs → List.Forall₂ (fun a b => g a = some b) l vs
  | [], vs, h => by simp at h; subst h; exact .nil
  | a :: l, vs, h => by
    rw [List.mapM_cons] at h
    cases hg : g a with
    | none => simp [hg] at h
    | some b =>
      cases hl : l.mapM g with
      | none => simp [hg, hl] at h
      | some bs =>
        simp [hg, hl] at h
        subst h
        exact .cons hg (mapM_forall₂Agg hl)

theorem forall₂_replicateAgg {α β : Type} {R : α → β → Prop} {b : β} :
    ∀ {l : List α}, (∀ a ∈ l, R a b) → List.Forall₂ R l (List.replicate l.length b)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall₂_replicateAgg fun x hx => h x (by simp [hx]))

theorem forall₂_replicate_invAgg {α β : Type} {R : α → β → Prop} {b : β} :
    ∀ {l : List α} {n : Nat}, List.Forall₂ R l (List.replicate n b) → ∀ a ∈ l, R a b
  | [], _, _ => by simp
  | a :: l, n + 1, .cons h hl => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h
    · exact forall₂_replicate_invAgg hl x hx

theorem forall₂_getElem?_leftAgg {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (_ : List.Forall₂ R l₁ l₂) {i : Nat} {a : α},
      l₁[i]? = some a → ∃ b, l₂[i]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab hl, i, b, h => by
    cases i with
    | zero => simp at h; subst h; exact ⟨_, rfl, hab⟩
    | succ i => simpa using forall₂_getElem?_leftAgg hl (by simpa using h)

/-- Operands typed below runtime parameter types are typed at them. -/
theorem exactOpsAgg {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    (hD : StoreDefsOkAgg s) :
    ∀ {vs : List Val} {ts t₁ : List CValType}, List.Forall₂ (ValOk s) vs ts →
      ResultSub C.toTypeCtx ts t₁ → ResultOk {} t₁ → List.Forall₂ (ValOk s) vs t₁
  | _, _, _, .nil, .nil, _ => .nil
  | _, _, _, .cons hv hvs, .cons hs hss, hok =>
    .cons (hv.ctxSubAgg hst hD hs (hok _ (by simp)))
      (exactOpsAgg hst hD hvs hss fun t ht => hok t (by simp [ht]))

theorem structFieldsOkAgg {s : Store H} :
    ∀ {L : List CFieldType} {vs : List Val}, List.Forall₂ (ValOk s) vs (L.map fieldUnpack) →
      List.Forall₂ (FieldValOk s) ((L.zip vs).map fun (ft, v) => packField (fieldStorage ft) v)
        (L.map fieldStorage)
  | [], _, h => by cases h; exact .nil
  | ft :: L, _ :: vs, .cons hv hvs => by
    refine .cons ?_ (structFieldsOkAgg hvs)
    rw [fieldUnpack_eqAgg] at hv
    exact packField_okAgg hv

/-- Field lookup through a typed struct reference. -/
theorem structFieldAgg {s : Store H} (hs : StoreOk s) (hD : StoreDefsOkAgg s) {a : Nat}
    {n : Bool} {d : DefType} {fs : Ty (.list .field)} {i : Nat} {m : Mutability}
    {z : CStorageType} (hr : RefOk s (.struct a) (.ref n (Ty.defHeap d))) (hd : TyOk {} d)
    (he : Expand d (.struct fs)) (hi : fs.toList[i]? = some (.field m z)) :
    ∃ si fs' m' z', s.structs[a]? = some si ∧ Expand si.type (.struct fs') ∧
      fs'.toList[i]? = some (.field m' z') ∧ Sub {} z' z ∧ (m = .var → m' = .var ∧ Sub {} z z') ∧
      TyOk {} z' ∧ ∀ fv, si.fields[i]? = some fv → FieldValOk s fv z' := by
  obtain ⟨si, fs', hsi, he', hsub⟩ := hr.structSubAgg hs hD hd he
  cases hsub with
  | @struct _ fs₁ extra _ h =>
    rw [Sub.list_iff] at h
    obtain ⟨f', hf', hsf⟩ := forall₂_getElem?_rightAgg h hi
    have hlt : i < fs₁.toList.length := (List.getElem?_eq_some_iff.mp hf').1
    have hf'' : (fs₁.app extra).toList[i]? = some f' := by
      rw [Ty.toList_app, List.getElem?_append_left hlt]; exact hf'
    obtain ⟨fsi, hfsi, hfields⟩ := hs.structs si (List.mem_of_getElem? hsi)
    have := Expand.func_eq he' hfsi
    cases this
    have hzok : ∀ {m' z'}, f' = .field m' z' → TyOk {} z' := by
      intro m' z' e; subst e
      exact Expand.fieldAgg (hD.1 si (List.mem_of_getElem? hsi)) he' hf''
    have hfv : ∀ {m' z'}, f' = .field m' z' → ∀ fv, si.fields[i]? = some fv →
        FieldValOk s fv z' := by
      intro m' z' e fv hfv
      subst e
      obtain ⟨b, hb, hfvb⟩ := forall₂_getElem?_leftAgg hfields hfv
      rw [List.getElem?_map, hf''] at hb
      cases hb
      exact hfvb
    cases hsf with
    | fieldConst h => exact ⟨si, _, _, _, hsi, he', hf'', h, by simp, hzok rfl, hfv rfl⟩
    | fieldVar h₁ h₂ =>
      exact ⟨si, _, _, _, hsi, he', hf'', h₁, fun _ => ⟨rfl, h₂⟩, hzok rfl, hfv rfl⟩

/-- Field lookup through a typed array reference. -/
theorem arrayFieldAgg {s : Store H} (hs : StoreOk s) (hD : StoreDefsOkAgg s) {a : Nat}
    {n : Bool} {d : DefType} {m : Mutability} {z : CStorageType}
    (hr : RefOk s (.array a) (.ref n (Ty.defHeap d))) (hd : TyOk {} d)
    (he : Expand d (.array (.field m z))) :
    ∃ ai m' z', s.arrays[a]? = some ai ∧ Expand ai.type (.array (.field m' z')) ∧
      Sub {} z' z ∧ (m = .var → m' = .var ∧ Sub {} z z') ∧ TyOk {} z' ∧
      ∀ fv ∈ ai.fields, FieldValOk s fv z' := by
  obtain ⟨ai, ft', hai, he', hsub⟩ := hr.arraySubAgg hs hD hd he
  obtain ⟨fta, hfta, hfields⟩ := hs.arrays ai (List.mem_of_getElem? hai)
  have := Expand.func_eq he' hfta
  cases this
  have hok := hD.2 ai (List.mem_of_getElem? hai)
  cases hsub with
  | fieldConst h =>
    exact ⟨ai, _, _, hai, he', h, by simp, Expand.array_ok hok he', hfields⟩
  | fieldVar h₁ h₂ =>
    exact ⟨ai, _, _, hai, he', h₁, fun _ => ⟨rfl, h₂⟩, Expand.array_ok hok he', hfields⟩

/-! ## Store updates (allocation and field update) -/

theorem extendsList_modifyAgg {α : Type} {R : α → α → Prop} {l : List α} {a : Nat} {g : α → α}
    (hrefl : ∀ x ∈ l, R x x) (hR : ∀ x, l[a]? = some x → R x (g x)) :
    ExtendsList R l (l.modify a g) := by
  refine ⟨by simp, fun i x hx => ?_⟩
  by_cases hia : a = i
  · subst hia
    exact ⟨g x, by simp [hx], hR x hx⟩
  · exact ⟨x, by simp [hia, hx], hrefl x (List.mem_of_getElem? hx)⟩

theorem extendsList_appendAgg {α : Type} {R : α → α → Prop} {l : List α}
    (hrefl : ∀ x ∈ l, R x x) (y : α) : ExtendsList R l (l ++ [y]) := by
  refine ⟨by simp, fun i x hx => ⟨x, ?_, hrefl x (List.mem_of_getElem? hx)⟩⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx

theorem ExtendStruct.reflAgg {s : Store H} (hs : StoreOk s) :
    ∀ si ∈ s.structs, ExtendStruct si si := fun si hsi => by
  obtain ⟨fs, he, hf⟩ := hs.structs si hsi
  exact ⟨rfl, fs, he, rfl, by simpa using hf.length_eq, fun _ _ h => .inr h⟩

theorem ExtendArray.reflAgg {s : Store H} (hs : StoreOk s) :
    ∀ ai ∈ s.arrays, ExtendArray ai ai := fun ai hai => by
  obtain ⟨ft, he, _⟩ := hs.arrays ai hai
  match ft, he with
  | .field m z, he => exact ⟨rfl, m, z, he, rfl, .inr rfl⟩

theorem StructInstOk.extendAgg {s s' : Store H} (he : Extend s s') {si : StructInst}
    (h : StructInstOk s si) : StructInstOk s' si := by
  obtain ⟨fs, hx, hf⟩ := h
  exact ⟨fs, hx, hf.imp fun _ _ h => h.extend he⟩

theorem ArrayInstOk.extendAgg {s s' : Store H} (he : Extend s s') {ai : ArrayInst}
    (h : ArrayInstOk s ai) : ArrayInstOk s' ai := by
  obtain ⟨ft, hx, hf⟩ := h
  exact ⟨ft, hx, fun fv hfv => (hf fv hfv).extend he⟩

/-- A store extending a valid store with the same non-heap instances is valid,
given valid heap instances and acyclicity. -/
theorem StoreOk.transferAgg {s s' : Store H} (hs : StoreOk s) (he : Extend s s')
    (htags : s'.tags = s.tags) (hglobals : s'.globals = s.globals) (hmems : s'.mems = s.mems)
    (htables : s'.tables = s.tables) (hfuncs : s'.funcs = s.funcs)
    (helems : s'.elems = s.elems) (hexns : s'.exns = s.exns)
    (hstructs : ∀ si ∈ s'.structs, StructInstOk s' si)
    (harrays : ∀ ai ∈ s'.arrays, ArrayInstOk s' ai)
    (hacS : ∀ a < s'.structs.length,
      ¬ ImmutReachable s' (.val (.ref (.struct a))) (.val (.ref (.struct a))))
    (hacA : ∀ a < s'.arrays.length,
      ¬ ImmutReachable s' (.val (.ref (.array a))) (.val (.ref (.array a))))
    (hacE : ∀ a < s'.exns.length,
      ¬ ImmutReachable s' (.val (.ref (.exn a))) (.val (.ref (.exn a))))
    (hD' : StoreDefsOkAgg s') : StoreOk s' where
  tags ti h := hs.tags ti (htags ▸ h)
  globals gi h := by
    obtain ⟨h₁, h₂⟩ := hs.globals gi (hglobals ▸ h)
    exact ⟨h₁, h₂.extend he⟩
  mems mi h := hs.mems mi (hmems ▸ h)
  tables ti h := by
    obtain ⟨h₁, h₂, h₃⟩ := hs.tables ti (htables ▸ h)
    exact ⟨h₁, h₂, fun r hr => (h₃ r hr).extend he⟩
  funcs fi h := by
    cases hs.funcs fi (hfuncs ▸ h) with
    | wasm hdt hm hcode hf hsub => exact .wasm hdt (hm.extend hs he) hcode hf hsub
    | host hdt he' hcode => exact .host hdt he' hcode
  elems ei h := (hs.elems ei (helems ▸ h)).extend he ⟨rfl, .inl rfl⟩
  structs := hstructs
  arrays := harrays
  exns e h := by
    obtain ⟨ti, ts, ht, hx, hf⟩ := hs.exns e (hexns ▸ h)
    exact ⟨ti, ts, htags ▸ ht, hx, ValOk.forall₂_extend he hf⟩
  acyclicStructs := hacS
  acyclicArrays := hacA
  acyclicExns := hacE
  structsClosed := hD'.1
  arraysClosed := hD'.2

/-! ### Reachability through immutable fields -/

/-- A field value whose value (if any) is typed in `s`. -/
def GoodAgg (s : Store H) (fv : FieldVal) : Prop := ∀ v, fv = .val v → ∃ t, ValOk s v t

theorem GoodAgg.of_fieldValOk {s : Store H} {fv : FieldVal} {z : CStorageType}
    (h : FieldValOk s fv z) : GoodAgg s fv := by
  intro v e
  cases h with
  | val h => cases e; exact ⟨_, h⟩
  | pack => cases e

theorem GoodAgg.ref_type {s : Store H} {r : Ref} (h : GoodAgg s (.val (.ref r))) :
    ∃ rt₀, Ref.type? s r = some rt₀ ∧
      (∀ r', r = .extern r' → RefOk s r' (.ref false (.abs .any)) ∧ r' ≠ .null) := by
  obtain ⟨t, ht⟩ := h _ rfl
  cases ht with
  | ref hr =>
    obtain ⟨rt₀, e, -, hx⟩ := hr.principal
    exact ⟨rt₀, e, hx⟩

theorem GoodAgg.struct_lt {s : Store H} {a : Nat} (h : GoodAgg s (.val (.ref (.struct a)))) :
    a < s.structs.length := by
  obtain ⟨rt₀, e, -⟩ := h.ref_type
  simp only [Ref.type?, Option.map_eq_some_iff] at e
  obtain ⟨si, hsi, -⟩ := e
  exact (List.getElem?_eq_some_iff.mp hsi).1

theorem GoodAgg.array_lt {s : Store H} {a : Nat} (h : GoodAgg s (.val (.ref (.array a)))) :
    a < s.arrays.length := by
  obtain ⟨rt₀, e, -⟩ := h.ref_type
  simp only [Ref.type?, Option.map_eq_some_iff] at e
  obtain ⟨ai, hai, -⟩ := e
  exact (List.getElem?_eq_some_iff.mp hai).1

theorem GoodAgg.extern {s : Store H} {r : Ref} (h : GoodAgg s (.val (.ref (.extern r)))) :
    GoodAgg s (.val (.ref r)) := by
  obtain ⟨rt₀, -, hx⟩ := h.ref_type
  intro v e; cases e
  exact ⟨_, .ref (hx r rfl).1⟩

theorem GoodAgg.struct_field {s : Store H} (hs : StoreOk s) {a i : Nat} {si : StructInst}
    {fv : FieldVal} (hsi : s.structs[a]? = some si) (hfv : si.fields[i]? = some fv) :
    GoodAgg s fv := by
  obtain ⟨fs, -, hf⟩ := hs.structs si (List.mem_of_getElem? hsi)
  obtain ⟨b, -, hb⟩ := forall₂_getElem?_leftAgg hf hfv
  exact GoodAgg.of_fieldValOk hb

theorem GoodAgg.array_field {s : Store H} (hs : StoreOk s) {a i : Nat} {ai : ArrayInst}
    {fv : FieldVal} (hai : s.arrays[a]? = some ai) (hfv : ai.fields[i]? = some fv) :
    GoodAgg s fv := by
  obtain ⟨ft, -, hf⟩ := hs.arrays ai (List.mem_of_getElem? hai)
  exact GoodAgg.of_fieldValOk (hf fv (List.mem_of_getElem? hfv))

theorem GoodAgg.exn_field {s : Store H} (hs : StoreOk s) {a i : Nat} {e : ExnInst} {v : Val}
    (he : s.exns[a]? = some e) (hv : e.fields[i]? = some v) : GoodAgg s (.val v) := by
  obtain ⟨ti, ts, -, -, hf⟩ := hs.exns e (List.mem_of_getElem? he)
  obtain ⟨b, -, hb⟩ := forall₂_getElem?_leftAgg hf hv
  intro v' e'; cases e'; exact ⟨_, hb⟩

theorem reach_addStructAgg {s : Store H} (hs : StoreOk s) {si : StructInst}
    (hnew : ∀ fv ∈ si.fields, GoodAgg s fv) :
    ∀ {x y : FieldVal}, ImmutReachable (s.addStruct si) x y →
      (GoodAgg s x → ImmutReachable s x y ∧ GoodAgg s y) ∧
      (x = .val (.ref (.struct s.structs.length)) → GoodAgg s y) := by
  intro x y h
  induction h with
  | trans _ _ ih₁ ih₂ =>
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨r₁, g₁⟩ := ih₁.1 hx
      obtain ⟨r₂, g₂⟩ := ih₂.1 g₁
      exact ⟨.trans r₁ r₂, g₂⟩
    · exact (ih₂.1 (ih₁.2 hx)).2
  | @refStruct a i si₀ fs z fv hs' he hi hfv =>
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have hlt := hx.struct_lt
      have hs₀ : s.structs[a]? = some si₀ := by
        simp only [Store.addStruct] at hs'
        rwa [List.getElem?_append_left hlt] at hs'
      exact ⟨.refStruct hs₀ he hi hfv, GoodAgg.struct_field hs hs₀ hfv⟩
    · simp only [FieldVal.val.injEq, Val.ref.injEq, Ref.struct.injEq] at hx
      subst hx
      simp only [Store.addStruct, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hs'
      subst hs'
      exact hnew fv (List.mem_of_getElem? hfv)
  | @refArray a i ai z fv hs' he hfv =>
    refine ⟨fun _ => ⟨.refArray hs' he hfv, GoodAgg.array_field hs hs' hfv⟩, fun hx => ?_⟩
    simp at hx
  | @refExn a i e v hs' hv =>
    refine ⟨fun _ => ⟨.refExn hs' hv, GoodAgg.exn_field hs hs' hv⟩, fun hx => ?_⟩
    simp at hx
  | refExtern r =>
    refine ⟨fun hx => ⟨.refExtern r, hx.extern⟩, fun hx => ?_⟩
    simp at hx

theorem reach_addArrayAgg {s : Store H} (hs : StoreOk s) {ai : ArrayInst}
    (hnew : ∀ fv ∈ ai.fields, GoodAgg s fv) :
    ∀ {x y : FieldVal}, ImmutReachable (s.addArray ai) x y →
      (GoodAgg s x → ImmutReachable s x y ∧ GoodAgg s y) ∧
      (x = .val (.ref (.array s.arrays.length)) → GoodAgg s y) := by
  intro x y h
  induction h with
  | trans _ _ ih₁ ih₂ =>
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨r₁, g₁⟩ := ih₁.1 hx
      obtain ⟨r₂, g₂⟩ := ih₂.1 g₁
      exact ⟨.trans r₁ r₂, g₂⟩
    · exact (ih₂.1 (ih₁.2 hx)).2
  | @refStruct a i si₀ fs z fv hs' he hi hfv =>
    refine ⟨fun _ => ⟨.refStruct hs' he hi hfv, GoodAgg.struct_field hs hs' hfv⟩, fun hx => ?_⟩
    simp at hx
  | @refArray a i ai₀ z fv hs' he hfv =>
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have hlt := hx.array_lt
      have hs₀ : s.arrays[a]? = some ai₀ := by
        simp only [Store.addArray] at hs'
        rwa [List.getElem?_append_left hlt] at hs'
      exact ⟨.refArray hs₀ he hfv, GoodAgg.array_field hs hs₀ hfv⟩
    · simp only [FieldVal.val.injEq, Val.ref.injEq, Ref.array.injEq] at hx
      subst hx
      simp only [Store.addArray, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hs'
      subst hs'
      exact hnew fv (List.mem_of_getElem? hfv)
  | @refExn a i e v hs' hv =>
    refine ⟨fun _ => ⟨.refExn hs' hv, GoodAgg.exn_field hs hs' hv⟩, fun hx => ?_⟩
    simp at hx
  | refExtern r =>
    refine ⟨fun hx => ⟨.refExtern r, hx.extern⟩, fun hx => ?_⟩
    simp at hx

theorem StoreOk.addStructAgg {s : Store H} (hs : StoreOk s) (hD : StoreDefsOkAgg s)
    {si : StructInst} (hsi : StructInstOk s si) (hty : TyOk {} si.type) :
    StoreOk (s.addStruct si) ∧ Extend s (s.addStruct si) ∧ StoreDefsOkAgg (s.addStruct si) := by
  have he : Extend s (s.addStruct si) :=
    { Extend.refl hs with structs := extendsList_appendAgg (ExtendStruct.reflAgg hs) si }
  have hnew : ∀ fv ∈ si.fields, GoodAgg s fv := by
    intro fv hfv
    obtain ⟨fs, -, hf⟩ := hsi
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hfv
    obtain ⟨b, -, hb⟩ := forall₂_getElem?_leftAgg hf hi
    exact GoodAgg.of_fieldValOk hb
  refine ⟨StoreOk.transferAgg hs he rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?d, he, ?d⟩
  case' d => refine ⟨?_, ?_⟩
  rotate_left 2
  · intro si' h
    simp only [Store.addStruct, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact (hs.structs si' h).extendAgg he
    · exact hsi.extendAgg he
  · intro ai h; exact (hs.arrays ai h).extendAgg he
  · intro a ha hr
    simp only [Store.addStruct, List.length_append, List.length_singleton] at ha
    by_cases hlt : a < s.structs.length
    · obtain ⟨si₀, hsi₀⟩ : ∃ si₀, s.structs[a]? = some si₀ :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hg : GoodAgg s (.val (.ref (.struct a))) := fun v e => by
        cases e; exact ⟨_, .ref (.struct hsi₀)⟩
      exact hs.acyclicStructs a hlt ((reach_addStructAgg hs hnew hr).1 hg).1
    · have : a = s.structs.length := by omega
      subst this
      exact Nat.lt_irrefl _ ((reach_addStructAgg hs hnew hr).2 rfl).struct_lt
  · intro a ha hr
    have hg : GoodAgg s (.val (.ref (.array a))) := fun v e => by
      cases e; exact ⟨_, .ref (.array (List.getElem?_eq_getElem ha))⟩
    exact hs.acyclicArrays a ha ((reach_addStructAgg hs hnew hr).1 hg).1
  · intro a ha hr
    have hg : GoodAgg s (.val (.ref (.exn a))) := fun v e => by
      cases e; exact ⟨_, .ref (.exn (List.getElem?_eq_getElem ha))⟩
    exact hs.acyclicExns a ha ((reach_addStructAgg hs hnew hr).1 hg).1
  · intro si' h
    simp only [Store.addStruct, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact hD.1 si' h
    · exact hty
  · exact hD.2

theorem StoreOk.addArrayAgg {s : Store H} (hs : StoreOk s) (hD : StoreDefsOkAgg s)
    {ai : ArrayInst} (hai : ArrayInstOk s ai) (hty : TyOk {} ai.type) :
    StoreOk (s.addArray ai) ∧ Extend s (s.addArray ai) ∧ StoreDefsOkAgg (s.addArray ai) := by
  have he : Extend s (s.addArray ai) :=
    { Extend.refl hs with arrays := extendsList_appendAgg (ExtendArray.reflAgg hs) ai }
  have hnew : ∀ fv ∈ ai.fields, GoodAgg s fv := by
    intro fv hfv
    obtain ⟨ft, -, hf⟩ := hai
    exact GoodAgg.of_fieldValOk (hf fv hfv)
  refine ⟨StoreOk.transferAgg hs he rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?d, he, ?d⟩
  case' d => refine ⟨?_, ?_⟩
  rotate_left 2
  · intro si h; exact (hs.structs si h).extendAgg he
  · intro ai' h
    simp only [Store.addArray, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact (hs.arrays ai' h).extendAgg he
    · exact hai.extendAgg he
  · intro a ha hr
    have hg : GoodAgg s (.val (.ref (.struct a))) := fun v e => by
      cases e; exact ⟨_, .ref (.struct (List.getElem?_eq_getElem ha))⟩
    exact hs.acyclicStructs a ha ((reach_addArrayAgg hs hnew hr).1 hg).1
  · intro a ha hr
    simp only [Store.addArray, List.length_append, List.length_singleton] at ha
    by_cases hlt : a < s.arrays.length
    · have hg : GoodAgg s (.val (.ref (.array a))) := fun v e => by
        cases e; exact ⟨_, .ref (.array (List.getElem?_eq_getElem hlt))⟩
      exact hs.acyclicArrays a hlt ((reach_addArrayAgg hs hnew hr).1 hg).1
    · have : a = s.arrays.length := by omega
      subst this
      exact Nat.lt_irrefl _ ((reach_addArrayAgg hs hnew hr).2 rfl).array_lt
  · intro a ha hr
    have hg : GoodAgg s (.val (.ref (.exn a))) := fun v e => by
      cases e; exact ⟨_, .ref (.exn (List.getElem?_eq_getElem ha))⟩
    exact hs.acyclicExns a ha ((reach_addArrayAgg hs hnew hr).1 hg).1
  · exact hD.1
  · intro ai' h
    simp only [Store.addArray, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact hD.2 ai' h
    · exact hty

theorem forall₂_setAgg {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (_ : List.Forall₂ R l₁ l₂) {i : Nat} {a : α} {b : β},
      l₂[i]? = some b → R a b → List.Forall₂ R (l₁.set i a) l₂
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons hab hl, i, a, b, h, hr => by
    cases i with
    | zero => simp at h; subst h; exact .cons hr hl
    | succ i => exact .cons hab (forall₂_setAgg hl (by simpa using h) hr)

theorem reach_setStructFieldAgg {s : Store H} {a i : Nat} {fv₀ : FieldVal} {si : StructInst}
    {fs : Ty (.list .field)} {z : CStorageType}
    (hsi : s.structs[a]? = some si) (hex : Expand si.type (.struct fs))
    (hi : fs.toList[i]? = some (.field .var z)) :
    ∀ {x y : FieldVal}, ImmutReachable (s.setStructField a i fv₀) x y → ImmutReachable s x y := by
  intro x y h
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @refStruct b j si₀ fs₀ z₀ fv hs' he hj hfv =>
    simp only [Store.setStructField, List.getElem?_modify] at hs'
    by_cases hab : a = b
    · subst hab
      simp only [hsi, ite_true] at hs'
      simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at hs'
      subst hs'
      have e := Expand.func_eq hex he
      cases e
      have hji : j ≠ i := by
        rintro rfl; rw [hi] at hj; cases hj
      simp only [List.getElem?_set_ne hji.symm] at hfv
      exact .refStruct hsi he hj hfv
    · simp only [hab, ite_false] at hs'
      simp only [Option.map_eq_map, Option.map_id'] at hs'
      exact .refStruct hs' he hj hfv
  | refArray hs' he hfv => exact .refArray hs' he hfv
  | refExn hs' hv => exact .refExn hs' hv
  | refExtern r => exact .refExtern r

theorem reach_setArrayFieldAgg {s : Store H} {a i : Nat} {fv₀ : FieldVal} {ai : ArrayInst}
    {z : CStorageType} (hai : s.arrays[a]? = some ai)
    (hex : Expand ai.type (.array (.field .var z))) :
    ∀ {x y : FieldVal}, ImmutReachable (s.setArrayField a i fv₀) x y → ImmutReachable s x y := by
  intro x y h
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs' he hj hfv => exact .refStruct hs' he hj hfv
  | @refArray b j ai₀ z₀ fv hs' he hfv =>
    simp only [Store.setArrayField, List.getElem?_modify] at hs'
    by_cases hab : a = b
    · subst hab
      simp only [hai, ite_true] at hs'
      simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at hs'
      subst hs'
      have e := Expand.func_eq hex he
      cases e
    · simp only [hab, ite_false] at hs'
      simp only [Option.map_eq_map, Option.map_id'] at hs'
      exact .refArray hs' he hfv
  | refExn hs' hv => exact .refExn hs' hv
  | refExtern r => exact .refExtern r

theorem StoreOk.setStructFieldAgg {s : Store H} (hs : StoreOk s) (hD : StoreDefsOkAgg s)
    {a i : Nat} {fv : FieldVal} {si : StructInst} {fs : Ty (.list .field)} {z : CStorageType}
    (hsi : s.structs[a]? = some si) (he : Expand si.type (.struct fs))
    (hi : fs.toList[i]? = some (.field .var z)) (hfv : FieldValOk s fv z) :
    StoreOk (s.setStructField a i fv) ∧ Extend s (s.setStructField a i fv) ∧
      StoreDefsOkAgg (s.setStructField a i fv) := by
  have hext : Extend s (s.setStructField a i fv) :=
    { Extend.refl hs with
      structs := extendsList_modifyAgg (ExtendStruct.reflAgg hs) fun x hx => by
        rw [hsi] at hx; cases hx
        obtain ⟨fs', he', hf⟩ := hs.structs si (List.mem_of_getElem? hsi)
        have e := Expand.func_eq he he'
        cases e
        refine ⟨rfl, fs, he, by simp, by simpa using hf.length_eq, fun j fv' hj => ?_⟩
        by_cases hji : i = j
        · subst hji; exact .inl ⟨z, hi⟩
        · exact .inr (by simp only [List.getElem?_set_ne hji]; exact hj) }
  have hmod : ∀ si' ∈ (s.setStructField a i fv).structs, StructInstOk s si' := by
    intro si' h
    simp only [Store.setStructField] at h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
    rw [List.getElem?_modify] at hk
    split at hk
    · next hak =>
      subst hak
      simp only [Option.map_eq_map, hsi, Option.map_some, Option.some.injEq] at hk
      subst hk
      obtain ⟨fs', he', hf⟩ := hs.structs si (List.mem_of_getElem? hsi)
      have e := Expand.func_eq he he'
      cases e
      refine ⟨fs, he, forall₂_setAgg hf (by rw [List.getElem?_map, hi]; rfl) hfv⟩
    · simp only [Option.map_eq_map, Option.map_id'] at hk
      exact hs.structs si' (List.mem_of_getElem? hk)
  refine ⟨StoreOk.transferAgg hs hext rfl rfl rfl rfl rfl rfl rfl
    (fun si' h => (hmod si' h).extendAgg hext) (fun ai h => (hs.arrays ai h).extendAgg hext)
    ?_ ?_ ?_ ?d, hext, ?d⟩
  case' d => refine ⟨?_, hD.2⟩
  rotate_left 1
  · intro b hb hr
    exact hs.acyclicStructs b (by simpa [Store.setStructField] using hb)
      (reach_setStructFieldAgg hsi he hi hr)
  · intro b hb hr
    exact hs.acyclicArrays b hb (reach_setStructFieldAgg hsi he hi hr)
  · intro b hb hr
    exact hs.acyclicExns b hb (reach_setStructFieldAgg hsi he hi hr)
  · intro si' h
    simp only [Store.setStructField] at h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
    rw [List.getElem?_modify] at hk
    split at hk
    · next hak =>
      subst hak
      simp only [Option.map_eq_map, hsi, Option.map_some, Option.some.injEq] at hk
      subst hk
      exact hD.1 si (List.mem_of_getElem? hsi)
    · simp only [Option.map_eq_map, Option.map_id'] at hk
      exact hD.1 si' (List.mem_of_getElem? hk)

theorem StoreOk.setArrayFieldAgg {s : Store H} (hs : StoreOk s) (hD : StoreDefsOkAgg s)
    {a i : Nat} {fv : FieldVal} {ai : ArrayInst} {z : CStorageType}
    (hai : s.arrays[a]? = some ai) (he : Expand ai.type (.array (.field .var z)))
    (hfv : FieldValOk s fv z) :
    StoreOk (s.setArrayField a i fv) ∧ Extend s (s.setArrayField a i fv) ∧
      StoreDefsOkAgg (s.setArrayField a i fv) := by
  have hext : Extend s (s.setArrayField a i fv) :=
    { Extend.refl hs with
      arrays := extendsList_modifyAgg (ExtendArray.reflAgg hs) fun x hx => by
        rw [hai] at hx; cases hx
        exact ⟨rfl, .var, z, he, by simp, .inl rfl⟩ }
  have hmod : ∀ ai' ∈ (s.setArrayField a i fv).arrays, ArrayInstOk s ai' := by
    intro ai' h
    simp only [Store.setArrayField] at h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
    rw [List.getElem?_modify] at hk
    split at hk
    · next hak =>
      subst hak
      simp only [Option.map_eq_map, hai, Option.map_some, Option.some.injEq] at hk
      subst hk
      obtain ⟨ft', he', hf⟩ := hs.arrays ai (List.mem_of_getElem? hai)
      have e := Expand.func_eq he he'
      cases e
      refine ⟨.field .var z, he, fun fv' hfv' => ?_⟩
      rcases List.mem_or_eq_of_mem_set hfv' with h' | rfl
      · exact hf fv' h'
      · exact hfv
    · simp only [Option.map_eq_map, Option.map_id'] at hk
      exact hs.arrays ai' (List.mem_of_getElem? hk)
  refine ⟨StoreOk.transferAgg hs hext rfl rfl rfl rfl rfl rfl rfl
    (fun si h => (hs.structs si h).extendAgg hext) (fun ai' h => (hmod ai' h).extendAgg hext)
    ?_ ?_ ?_ ?d, hext, ?d⟩
  case' d => refine ⟨hD.1, ?_⟩
  rotate_left 1
  · intro b hb hr
    exact hs.acyclicStructs b hb (reach_setArrayFieldAgg hai he hr)
  · intro b hb hr
    exact hs.acyclicArrays b (by simpa [Store.setArrayField] using hb)
      (reach_setArrayFieldAgg hai he hr)
  · intro b hb hr
    exact hs.acyclicExns b hb (reach_setArrayFieldAgg hai he hr)
  · intro ai' h
    simp only [Store.setArrayField] at h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
    rw [List.getElem?_modify] at hk
    split at hk
    · next hak =>
      subst hak
      simp only [Option.map_eq_map, hai, Option.map_some, Option.some.injEq] at hk
      subst hk
      exact hD.2 ai (List.mem_of_getElem? hai)
    · simp only [Option.map_eq_map, Option.map_id'] at hk
      exact hD.2 ai' (List.mem_of_getElem? hk)

/-! ## Typing reducts -/

theorem trapAgg {s : Store H} {C : Context} {t₂ : List CValType} (hok : ResultOk C.toTypeCtx t₂) :
    AdminsOk s C [.trap] ⟨[], [], t₂⟩ :=
  .single (.trap ⟨by simp [ResultOk], hok, by simp⟩)

theorem valsOutAgg {s : Store H} {C : Context} {vs : List Val} {ts : List CValType}
    (hv : List.Forall₂ (ValOk s) vs ts) (hok : ResultOk {} ts) :
    AdminsOk s C (vals vs) ⟨[], [], ts⟩ :=
  AdminsOk.of_vals hv (ResultOk.ofEmptyAgg hok _)

theorem valOutSubAgg {s : Store H} {C : Context} {v : Val} {t t' : CValType}
    (hv : ValOk s v t) (hs : Sub C.toTypeCtx t t') (hok : TyOk C.toTypeCtx t') :
    AdminsOk s C [v.toAdmin] ⟨[], [], [t']⟩ :=
  .sub (.single (AdminOk.toAdmin_ok hv)) ⟨.nil, .cons hs .nil, by simp⟩
    ⟨by simp [ResultOk], by simpa [ResultOk] using hok, by simp⟩

theorem instrOutAgg {s : Store H} {C : Context} {i : Instr} {P Q : List CValType}
    (hi : RefInstrOk C i ⟨P, [], Q⟩) : AdminsOk s C [.plain i] ⟨P, [], Q⟩ :=
  .single (.plain (.reference hi))

theorem seqOutAgg {s : Store H} {C : Context} {as₁ as₂ : List Admin} {P Q R : List CValType}
    (h₁ : AdminsOk s C as₁ ⟨P, [], Q⟩) (h₂ : AdminsOk s C as₂ ⟨Q, [], R⟩) :
    AdminsOk s C (as₁ ++ as₂) ⟨P, [], R⟩ := by
  simpa using AdminsOk.seq h₁ (by simp) h₂

theorem forall₂_one_inv {α β : Type} {R : α → β → Prop} {a : α} {b : β}
    (h : List.Forall₂ R [a] [b]) : R a b := by
  cases h with | cons h _ => exact h

/-- Allocation typing for `REF.STRUCT_ADDR`/`REF.ARRAY_ADDR`. -/
theorem refOutAgg {s : Store H} {C : Context} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    AdminsOk s C [.ref r] ⟨[], [], [.refv rt]⟩ := .single (.ref h)

/-- The reduct of `array.copy-le`/`array.copy-gt` is typed. -/
theorem copyOutAgg {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    (hD : StoreDefsOkAgg s) {x₁ x₂ : TypeIdx} {a₁ a₂ : Nat} {i₁ i₂ n : BitVec 32}
    {ts : List CValType} {d₁ d₂ : DefType} {m₂ : Mutability} {z₁ z₂ : CStorageType}
    (hvs : List.Forall₂ (ValOk s)
      [.ref (.array a₁), Val.i32 i₁, .ref (.array a₂), Val.i32 i₂, Val.i32 n] ts)
    (hsub : ResultSub C.toTypeCtx ts
      [Ty.refT true (Ty.defHeap d₁), Ty.i32, Ty.refT true (Ty.defHeap d₂), Ty.i32, Ty.i32])
    (hp0 : ResultOk {}
      [Ty.refT true (Ty.defHeap d₁), Ty.i32, Ty.refT true (Ty.defHeap d₂), Ty.i32, Ty.i32])
    (hd₁ : C.type? x₁ = some d₁) (he₁ : Expand d₁ (.array (.field .var z₁)))
    (hd₂ : C.type? x₂ = some d₂) (he₂ : Expand d₂ (.array (.field m₂ z₂)))
    (hz : Sub C.toTypeCtx z₂ z₁) (k₁ k₂ k₃ k₄ k₅ : BitVec 32) :
    AdminsOk s C [arrRef a₁, constI32 k₁, arrRef a₂, constI32 k₂,
      .plain (.arrayGet (storageSx (fieldStorage (.field m₂ z₂))) x₂), .plain (.arraySet x₁),
      arrRef a₁, constI32 k₃, arrRef a₂, constI32 k₄, constI32 k₅,
      .plain (.arrayCopy x₁ x₂)] ⟨[], [], []⟩ := by
  have hops := exactOpsAgg hst hD hvs hsub hp0
  rcases hops with _ | ⟨hv₁, _ | ⟨-, _ | ⟨hv₃, -⟩⟩⟩
  have hR₁ : TyOk {} (Ty.refT true (Ty.defHeap d₁)) := hp0 _ (by simp)
  have hR₂ : TyOk {} (Ty.refT true (Ty.defHeap d₂)) := hp0 _ (by simp)
  have hZ₂ : TyOk {} z₂.unpack := TyOk.unpack (Expand.array_ok (hst.typeAgg hd₂).2 he₂)
  have hsx : (storageSx (fieldStorage (.field m₂ z₂))).isSome = z₂.isPacked := by
    cases z₂ <;> rfl
  have hA : AdminsOk s C (vals [.ref (.array a₁), Val.i32 k₁, .ref (.array a₂), Val.i32 k₂])
      ⟨[], [], [Ty.refT true (Ty.defHeap d₁), Ty.i32, Ty.refT true (Ty.defHeap d₂), Ty.i32]⟩ := by
    refine valsOutAgg (.cons hv₁ (.cons (ValOk.i32Agg _) (.cons hv₃ (.cons (ValOk.i32Agg _) .nil))))
      ?_
    intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hR₁
    · exact .num _
    · exact hR₂
    · exact .num _
  have hB := AdminsOk.frame (ts := [Ty.refT true (Ty.defHeap d₁), Ty.i32])
    (instrOutAgg (s := s) (.arrayGet hd₂ he₂ hsx))
    (ResultOk.ofEmptyAgg (fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hR₁
      · exact .num _) _)
  have hC : AdminsOk s C [.plain (.arraySet x₁)]
      ⟨[Ty.refT true (Ty.defHeap d₁), Ty.i32, z₂.unpack], [], []⟩ := by
    refine .sub (instrOutAgg (.arraySet hd₁ he₁))
      ⟨.cons (Sub.refl _ (k := .val) trivial _) (.cons .num (.cons (Sub.unpackAgg hz) .nil)),
        .nil, by simp⟩ ⟨fun t ht => ?_, by simp [ResultOk], by simp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact TyOk.ofEmptyAgg hR₁ _
    · exact .num _
    · exact TyOk.ofEmptyAgg hZ₂ _
  have hD' : AdminsOk s C (vals [.ref (.array a₁), Val.i32 k₃, .ref (.array a₂), Val.i32 k₄,
      Val.i32 k₅] ++ [.plain (.arrayCopy x₁ x₂)]) ⟨[], [], []⟩ := by
    refine seqOutAgg (valsOutAgg (.cons hv₁ (.cons (ValOk.i32Agg _) (.cons hv₃
      (.cons (ValOk.i32Agg _) (.cons (ValOk.i32Agg _) .nil))))) hp0) ?_
    exact instrOutAgg (.arrayCopy hd₁ he₁ hd₂ he₂ hz)
  exact seqOutAgg (seqOutAgg (seqOutAgg hA hB) hC) hD'

/-! ## Per-rule preservation -/

/-- Trapping rules. -/
theorem trapCaseAgg {s : Store H} {f : Frame} {C : Context} {i : Instr} {vs : List Val}
    {it : InstrType} (hst : StateOk s f C) (hD : StoreDefsOkAgg s) (ha : i.IsAggregate)
    (hlen : ∀ it', RefInstrOk C i it' → it'.params.length = vs.length)
    (hty : AdminsOk s C (vals vs ++ [.plain i]) it) :
    f = f ∧ StoreOk s ∧ Extend s s ∧ AdminsOk s C [.trap] it ∧ StoreDefsOkAgg s := by
  obtain ⟨t₁, t₂, ts, hi, -, -, -, hok₂, hrep⟩ :=
    redexAgg hst.deltaOkAgg (hiAgg hst ha hlen) hty
  exact ⟨rfl, hst.1, Extend.refl hst.1, hrep _ _ (trapAgg hok₂), hD⟩

/-- Rules reducing to the empty sequence without changing the store. -/
theorem nilCaseAgg {s : Store H} {f : Frame} {C : Context} {i : Instr} {vs : List Val}
    {it : InstrType} (hst : StateOk s f C) (hD : StoreDefsOkAgg s) (ha : i.IsAggregate)
    (hlen : ∀ it', RefInstrOk C i it' → it'.params.length = vs.length)
    (hres : ∀ it', RefInstrOk C i it' → it'.results = [])
    (hty : AdminsOk s C (vals vs ++ [.plain i]) it) :
    f = f ∧ StoreOk s ∧ Extend s s ∧ AdminsOk s C [] it ∧ StoreDefsOkAgg s := by
  obtain ⟨t₁, t₂, ts, hi, -, -, -, hok₂, hrep⟩ :=
    redexAgg hst.deltaOkAgg (hiAgg hst ha hlen) hty
  have := hres _ (InstrOk.aggAgg hi ha)
  simp only at this
  subst this
  exact ⟨rfl, hst.1, Extend.refl hst.1, hrep _ _ .nil, hD⟩

theorem Expand.eqAgg {d : DefType} {c₁ c₂ : CCompType} (h₁ : Expand d c₁) (h₂ : Expand d c₂) :
    c₁ = c₂ := Expand.func_eq h₁ h₂

/-- **Preservation (aggregate)**, with the invariant `StoreDefsOkAgg`. -/
theorem AggregateStep.preservationAgg {c c' : Config H} {C : Context} {it : InstrType}
    (hst : StateOk c.store c.frame C) (hD : StoreDefsOkAgg c.store)
    (hty : AdminsOk c.store C c.code it) (h : AggregateStep c c') :
    c'.frame = c.frame ∧ StoreOk c'.store ∧ Extend c.store c'.store ∧
      AdminsOk c'.store C c'.code it ∧ StoreDefsOkAgg c'.store := by
  have hs := hst.1
  have hΔ := hst.deltaOkAgg
  cases h with
  | @structNew s f x d fs vs hd he hn =>
    have hlen : ∀ it', RefInstrOk C (.structNew x) it' → it'.params.length = vs.length := by
      intro it' h'
      cases h' with
      | structNew hd' he' =>
        have e := (hst.typeAgg hd').1
        rw [hd] at e; cases e
        cases Expand.eqAgg he he'
        simp [hn, Ty.length]
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ := redexAgg hΔ (hiAgg hst (by trivial) hlen) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | structNew hd' he' =>
      obtain ⟨e, hdok⟩ := hst.typeAgg hd'
      rw [hd] at e; cases e
      cases Expand.eqAgg he he'
      have hops := exactOpsAgg hst hD hvs hsub hp0
      have hsi : StructInstOk s ⟨d, (fs.toList.zip vs).map fun (ft, v) =>
          packField (fieldStorage ft) v⟩ := ⟨fs, he, structFieldsOkAgg hops⟩
      obtain ⟨hs', hext, hD'⟩ := StoreOk.addStructAgg hs hD hsi hdok
      refine ⟨rfl, hs', hext, hrep _ _ (refOutAgg (.struct (si := ⟨d, (fs.toList.zip vs).map fun (ft, v) =>
          packField (fieldStorage ft) v⟩) ?_)), hD'⟩
      simp [Store.addStruct]
  | @structNewDefault s f x d fs vs hd he hdef =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := []) hΔ (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    cases hr with
    | structNewDefault hd' he' _ =>
      obtain ⟨e, hdok⟩ := hst.typeAgg hd'
      rw [hd] at e; cases e
      cases Expand.eqAgg he he'
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      have hfs := Expand.struct_ok hdok he
      have hvd : List.Forall₂ (ValOk s) vs (fs.toList.map fieldUnpack) := by
        have h1 := mapM_forall₂Agg hdef
        clear hdef hrep
        generalize fs.toList = L at h1 hfs ⊢
        induction h1 with
        | nil => exact .nil
        | @cons ft v L vs' hv _ ih =>
          refine .cons ?_ (ih fun f hf => hfs f (by simp [hf]))
          rw [fieldUnpack_eqAgg]
          refine defaultVal_okAgg ?_ hv
          rw [← fieldUnpack_eqAgg]
          exact TyOk.fieldUnpack (hfs ft (by simp))
      exact seqOutAgg (valsOutAgg hvd fun t ht => by
          simp only [List.mem_map] at ht
          obtain ⟨ft, hft, rfl⟩ := ht
          exact TyOk.fieldUnpack (hfs ft hft))
        (instrOutAgg (.structNew hd' he))
  | @structGetNull s f sx x i =>
    exact trapCaseAgg (vs := [.ref .null]) hst hD (by trivial) (by intro it h; cases h; rfl) hty
  | @structGetStruct s f sx x i a si fv _ _ _ hsi hfv _ _ _ _ =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.struct a)]) hΔ (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @structGet _ _ _ d fs m z hd he hfi _ =>
      have hdok := (hst.typeAgg hd).2
      have hops := exactOpsAgg hst hD hvs hsub hp0
      have hv := forall₂_one_inv hops
      cases hv with
      | ref hr =>
        obtain ⟨si', fs', m', z', hsi', -, -, hz, -, -, hfvok⟩ :=
          structFieldAgg hs hD hr hdok he hfi
        rw [hsi] at hsi'; cases hsi'
        obtain ⟨t, htv, hts⟩ := unpackField_okAgg sx (hfvok fv hfv) hz
        refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
        exact valOutSubAgg htv (Sub.ofEmptyAgg hts _) (hok₂ _ (by simp))
  | @structSetNull s f x i v =>
    exact trapCaseAgg (vs := [.ref .null, v]) hst hD (by trivial) (by intro it h; cases h; rfl) hty
  | @structSetStruct s f x i v a d fs ft _ hd he hi _ _ _ =>
    obtain ⟨t₁, t₂, ts, hi', hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.struct a), v]) hΔ
        (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi' trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @structSet _ _ d' fs' z hd' he' hfi =>
      obtain ⟨e, hdok⟩ := hst.typeAgg hd'
      rw [hd] at e; cases e
      cases Expand.eqAgg he he'
      rw [hi] at hfi; cases hfi
      have hops := exactOpsAgg hst hD hvs hsub hp0
      rcases hops with _ | ⟨hv₁, _ | ⟨hv₂, _⟩⟩
      cases hv₁ with
      | ref hr =>
        obtain ⟨si, fs₁, m', z', hsi, he₁, hfi₁, -, hvar, hzok, -⟩ :=
          structFieldAgg hs hD hr hdok he hi
        obtain ⟨rfl, hzz⟩ := hvar rfl
        have hfv : FieldValOk s (packField z v) z' :=
          (packField_okAgg hv₂).subAgg hzz hzok
        obtain ⟨hs', hext, hD'⟩ := StoreOk.setStructFieldAgg hs hD hsi he₁ hfi₁ hfv
        exact ⟨rfl, hs', hext, hrep _ _ .nil, hD'⟩
  | @arrayNew s f x v n =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [v, Val.i32 n]) hΔ (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @arrayNew _ d m z hd he =>
      have hops := exactOpsAgg hst hD hvs hsub hp0
      rcases hops with _ | ⟨hv, -⟩
      have hzok : TyOk {} z.unpack := hp0 _ (by simp)
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      have hrep' := forall₂_replicateAgg (l := List.replicate n.toNat v) (R := ValOk s)
        (b := z.unpack) (by intro a ha; rw [(List.mem_replicate.mp ha).2]; exact hv)
      rw [List.length_replicate] at hrep'
      exact seqOutAgg (valsOutAgg hrep' fun t ht => by rw [(List.mem_replicate.mp ht).2]; exact hzok)
        (instrOutAgg (.arrayNewFixed (n := ⟨n.toNat, n.isLt⟩) hd he))
  | @arrayNewDefault s f x n d ft v hd he hv =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [Val.i32 n]) hΔ (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    cases hr with
    | @arrayNewDefault _ d' m z hd' he' _ =>
      obtain ⟨e, hdok⟩ := hst.typeAgg hd'
      rw [hd] at e; cases e
      cases Expand.eqAgg he he'
      have hzok : TyOk {} z.unpack := TyOk.unpack (Expand.array_ok hdok he)
      have hv' : ValOk s v z.unpack := defaultVal_okAgg hzok hv
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      have hrep' := forall₂_replicateAgg (l := List.replicate n.toNat v) (R := ValOk s)
        (b := z.unpack) (by intro a ha; rw [(List.mem_replicate.mp ha).2]; exact hv')
      rw [List.length_replicate] at hrep'
      exact seqOutAgg (valsOutAgg hrep' fun t ht => by rw [(List.mem_replicate.mp ht).2]; exact hzok)
        (instrOutAgg (.arrayNewFixed (n := ⟨n.toNat, n.isLt⟩) hd' he))
  | @arrayNewFixed s f x n d ft vs hd he hn =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg hΔ (hiAgg hst (by trivial) (by intro it h; cases h; simp [hn])) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @arrayNewFixed _ _ d' m z hd' he' =>
      obtain ⟨e, hdok⟩ := hst.typeAgg hd'
      rw [hd] at e; cases e
      cases Expand.eqAgg he he'
      have hops := exactOpsAgg hst hD hvs hsub hp0
      have hall := forall₂_replicate_invAgg hops
      have hai : ArrayInstOk s ⟨d, vs.map (packField (fieldStorage (.field m z)))⟩ := by
        refine ⟨.field m z, he, fun fv hfv => ?_⟩
        simp only [List.mem_map] at hfv
        obtain ⟨v, hv, rfl⟩ := hfv
        exact packField_okAgg (hall v hv)
      obtain ⟨hs', hext, hD'⟩ := StoreOk.addArrayAgg hs hD hai hdok
      refine ⟨rfl, hs', hext, hrep _ _ (refOutAgg (.array (ai := ⟨d, vs.map (packField (fieldStorage (.field m z)))⟩) ?_)), hD'⟩
      simp [Store.addArray]
  | @arrayNewElemOob s f x y i n ea ei _ _ =>
    exact trapCaseAgg (vs := [Val.i32 i, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayNewElemAlloc s f x y i n ea ei hel hle =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [Val.i32 i, Val.i32 n]) hΔ
        (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    cases hr with
    | @arrayNewElem _ _ d m rt rt' hd he hy hsr =>
      have hdok := (hst.typeAgg hd).2
      obtain ⟨ea', ei', hel', hty', hok⟩ := hst.elemAgg hy
      rw [hel] at hel'; cases hel'
      have hrtok : TyOk {} (Ty.refv rt : CValType) := by
        have := Expand.array_ok hdok he
        exact TyOk.val_inv this
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      have hmap : ((ei.refs.drop i.toNat).take n.toNat).map Admin.ref =
          vals (((ei.refs.drop i.toNat).take n.toNat).map Val.ref) := by
        rw [vals, List.map_map]; rfl
      rw [hmap]
      have hl : (((ei.refs.drop i.toNat).take n.toNat).map Val.ref).length = n.toNat := by
        simp; omega
      have hvals : List.Forall₂ (ValOk s) (((ei.refs.drop i.toNat).take n.toNat).map Val.ref)
          (List.replicate n.toNat (Ty.refv rt)) := by
        have h2 := forall₂_replicateAgg (R := ValOk s) (b := Ty.refv rt)
          (l := ((ei.refs.drop i.toNat).take n.toNat).map Val.ref) (fun v hv => by
            simp only [List.mem_map] at hv
            obtain ⟨r, hr, rfl⟩ := hv
            have hr' : r ∈ ei.refs := List.mem_of_mem_drop (List.mem_of_mem_take hr)
            have hrok : RefOk s r rt' := hty' ▸ hok.2 r hr'
            exact ValOk.ctxSubAgg hst hD (.ref hrok) (.refv hsr) hrtok)
        rwa [hl] at h2
      exact seqOutAgg (valsOutAgg hvals fun t ht => by rw [(List.mem_replicate.mp ht).2]; exact hrtok)
        (instrOutAgg (.arrayNewFixed (n := ⟨n.toNat, n.isLt⟩) hd he))
  | @arrayNewDataOob s f x y i n d ft da di _ _ _ _ =>
    exact trapCaseAgg (vs := [Val.i32 i, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayNewDataNum s f x y i n d ft da di vs hd he hdat _ hb hvs₀ =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [Val.i32 i, Val.i32 n]) hΔ
        (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    cases hr with
    | @arrayNewData _ _ d' m z hd' he' _ _ =>
      obtain ⟨e, hdok⟩ := hst.typeAgg hd'
      rw [hd] at e; cases e
      cases Expand.eqAgg he he'
      have hzok : TyOk {} z.unpack := TyOk.unpack (Expand.array_ok hdok he)
      have h1 := mapM_forall₂Agg hvs₀
      have hl : vs.length = n.toNat := by rw [← h1.length_eq]; simp
      have hall : ∀ v ∈ vs, ValOk s v z.unpack := by
        intro v hv
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hv
        obtain ⟨j, hj, hjv⟩ := forall₂_getElem?_rightAgg h1 hk
        exact readField_okAgg hjv
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      have hvals := forall₂_replicateAgg (R := ValOk s) (b := z.unpack) hall
      rw [hl] at hvals
      exact seqOutAgg (valsOutAgg hvals fun t ht => by rw [(List.mem_replicate.mp ht).2]; exact hzok)
        (instrOutAgg (.arrayNewFixed (n := ⟨n.toNat, n.isLt⟩) hd' he))
  | @arrayGetNull s f sx x i =>
    exact trapCaseAgg (vs := [.ref .null, Val.i32 i]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayGetOob s f sx x i a ai _ _ =>
    exact trapCaseAgg (vs := [.ref (.array a), Val.i32 i]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayGetArray s f sx x i a ai fv _ _ hai hfv _ _ _ =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.array a), Val.i32 i]) hΔ
        (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @arrayGet _ _ d m z hd he _ =>
      have hdok := (hst.typeAgg hd).2
      have hops := exactOpsAgg hst hD hvs hsub hp0
      rcases hops with _ | ⟨hv₁, -⟩
      cases hv₁ with
      | ref hr =>
        obtain ⟨ai', m', z', hai', -, hz, -, -, hfields⟩ := arrayFieldAgg hs hD hr hdok he
        rw [hai] at hai'; cases hai'
        obtain ⟨t, htv, hts⟩ :=
          unpackField_okAgg sx (hfields fv (List.mem_of_getElem? hfv)) hz
        refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
        exact valOutSubAgg htv (Sub.ofEmptyAgg hts _) (hok₂ _ (by simp))
  | @arraySetNull s f x i v =>
    exact trapCaseAgg (vs := [.ref .null, Val.i32 i, v]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arraySetOob s f x i v a ai _ _ =>
    exact trapCaseAgg (vs := [.ref (.array a), Val.i32 i, v]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arraySetArray s f x i v a ai d ft hai hlt hd he =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.array a), Val.i32 i, v]) hΔ
        (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @arraySet _ d' z hd' he' =>
      obtain ⟨e, hdok⟩ := hst.typeAgg hd'
      rw [hd] at e; cases e
      cases Expand.eqAgg he he'
      have hops := exactOpsAgg hst hD hvs hsub hp0
      rcases hops with _ | ⟨hv₁, _ | ⟨-, _ | ⟨hv₃, -⟩⟩⟩
      cases hv₁ with
      | ref hr =>
        obtain ⟨ai', m', z', hai', he₁, -, hvar, hzok, -⟩ := arrayFieldAgg hs hD hr hdok he
        rw [hai] at hai'; cases hai'
        obtain ⟨rfl, hzz⟩ := hvar rfl
        have hfv : FieldValOk s (packField z v) z' := (packField_okAgg hv₃).subAgg hzz hzok
        obtain ⟨hs', hext, hD'⟩ := StoreOk.setArrayFieldAgg (i := i.toNat) hs hD hai he₁ hfv
        exact ⟨rfl, hs', hext, hrep _ _ .nil, hD'⟩
  | @arrayLenNull s f =>
    exact trapCaseAgg (vs := [.ref .null]) hst hD (by trivial) (by intro it h; cases h; rfl) hty
  | @arrayLenArray s f a ai hai =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.array a)]) hΔ (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    cases hr with
    | arrayLen =>
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      exact valsOutAgg (vs := [Val.i32 _]) (.cons (ValOk.i32Agg _) .nil)
        (fun t ht => by simp at ht; subst ht; exact .num _)
  | @arrayFillNull s f x i n v =>
    exact trapCaseAgg (vs := [.ref .null, Val.i32 i, v, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayFillOob s f x i n v a ai _ _ =>
    exact trapCaseAgg (vs := [.ref (.array a), Val.i32 i, v, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayFillZero s f x i v a ai _ _ =>
    exact nilCaseAgg (vs := [.ref (.array a), Val.i32 i, v, Val.i32 0]) hst hD (by trivial)
      (by intro it h; cases h; rfl) (by intro it h; cases h; rfl) hty
  | @arrayFillSucc s f x i n v a ai hai hle hn =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.array a), Val.i32 i, v, Val.i32 n]) hΔ
        (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @arrayFill _ d z hd he =>
      have hops := exactOpsAgg hst hD hvs hsub hp0
      rcases hops with _ | ⟨hv₁, _ | ⟨-, _ | ⟨hv₃, -⟩⟩⟩
      have hR : TyOk {} (Ty.refT true (Ty.defHeap d)) := hp0 _ (by simp)
      have hZ : TyOk {} z.unpack := hp0 _ (by simp)
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      refine seqOutAgg (as₁ := vals [.ref (.array a), Val.i32 i, v] ++ [.plain (.arraySet x)])
        (seqOutAgg (valsOutAgg (.cons hv₁ (.cons (ValOk.i32Agg _) (.cons hv₃ .nil))) ?_)
          (instrOutAgg (.arraySet hd he)))
        (seqOutAgg (valsOutAgg (.cons hv₁ (.cons (ValOk.i32Agg _) (.cons hv₃
          (.cons (ValOk.i32Agg _) .nil)))) ?_) (instrOutAgg (.arrayFill hd he)))
      · intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        · exact hR
        · exact .num _
        · exact hZ
      · intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hR
        · exact .num _
        · exact hZ
        · exact .num _
  | @arrayCopyNull₁ s f x₁ x₂ i₁ i₂ n r =>
    exact trapCaseAgg (vs := [.ref .null, Val.i32 i₁, .ref r, Val.i32 i₂, Val.i32 n]) hst hD
      (by trivial) (by intro it h; cases h; rfl) hty
  | @arrayCopyNull₂ s f x₁ x₂ i₁ i₂ n r =>
    exact trapCaseAgg (vs := [.ref r, Val.i32 i₁, .ref .null, Val.i32 i₂, Val.i32 n]) hst hD
      (by trivial) (by intro it h; cases h; rfl) hty
  | @arrayCopyOob₁ s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ _ _ =>
    exact trapCaseAgg (vs := [.ref (.array a₁), Val.i32 i₁, .ref (.array a₂), Val.i32 i₂,
      Val.i32 n]) hst hD (by trivial) (by intro it h; cases h; rfl) hty
  | @arrayCopyOob₂ s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₂ _ _ =>
    exact trapCaseAgg (vs := [.ref (.array a₁), Val.i32 i₁, .ref (.array a₂), Val.i32 i₂,
      Val.i32 n]) hst hD (by trivial) (by intro it h; cases h; rfl) hty
  | @arrayCopyZero s f x₁ x₂ i₁ i₂ a₁ a₂ ai₁ ai₂ _ _ _ =>
    exact nilCaseAgg (vs := [.ref (.array a₁), Val.i32 i₁, .ref (.array a₂), Val.i32 i₂,
      Val.i32 0]) hst hD (by trivial) (by intro it h; cases h; rfl) (by intro it h; cases h; rfl) hty
  | @arrayCopyLe s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ _ _ _ _ hd he _ =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.array a₁), Val.i32 i₁, .ref (.array a₂), Val.i32 i₂, Val.i32 n])
        hΔ (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @arrayCopy _ _ d₁ d₂' m₂ z₁ z₂ hd₁ he₁ hd₂ he₂ hz =>
      obtain ⟨e, -⟩ := hst.typeAgg hd₂
      rw [hd] at e; cases e
      cases Expand.eqAgg he he₂
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      exact copyOutAgg hst hD hvs hsub hp0 hd₁ he₁ hd₂ he₂ hz _ _ _ _ _
  | @arrayCopyGt s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ _ _ _ _ hd he _ =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.array a₁), Val.i32 i₁, .ref (.array a₂), Val.i32 i₂, Val.i32 n])
        hΔ (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @arrayCopy _ _ d₁ d₂' m₂ z₁ z₂ hd₁ he₁ hd₂ he₂ hz =>
      obtain ⟨e, -⟩ := hst.typeAgg hd₂
      rw [hd] at e; cases e
      cases Expand.eqAgg he he₂
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      exact copyOutAgg hst hD hvs hsub hp0 hd₁ he₁ hd₂ he₂ hz _ _ _ _ _
  | @arrayInitElemNull s f x y i j n =>
    exact trapCaseAgg (vs := [.ref .null, Val.i32 i, Val.i32 j, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayInitElemOob₁ s f x y i j n a ai _ _ =>
    exact trapCaseAgg (vs := [.ref (.array a), Val.i32 i, Val.i32 j, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayInitElemOob₂ s f x y i j n a ea ei _ _ =>
    exact trapCaseAgg (vs := [.ref (.array a), Val.i32 i, Val.i32 j, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayInitElemZero s f x y i j a ea ai ei _ _ _ =>
    exact nilCaseAgg (vs := [.ref (.array a), Val.i32 i, Val.i32 j, Val.i32 0]) hst hD (by trivial)
      (by intro it h; cases h; rfl) (by intro it h; cases h; rfl) hty
  | @arrayInitElemSucc s f x y i j n a ea ai ei r hai hel hle hn hr' =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.array a), Val.i32 i, Val.i32 j, Val.i32 n]) hΔ
        (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @arrayInitElem _ _ d z rt hd he hy hsz =>
      have hdok := (hst.typeAgg hd).2
      obtain ⟨ea', ei', hel', hty', hok⟩ := hst.elemAgg hy
      rw [hel] at hel'; cases hel'
      have hops := exactOpsAgg hst hD hvs hsub hp0
      rcases hops with _ | ⟨hv₁, -⟩
      have hR : TyOk {} (Ty.refT true (Ty.defHeap d)) := hp0 _ (by simp)
      have hZ : TyOk {} z.unpack := TyOk.unpack (Expand.array_ok hdok he)
      have hrok : RefOk s r rt := hty' ▸ hok.2 r (List.mem_of_getElem? hr')
      have hv₃ : ValOk s (.ref r) z.unpack :=
        ValOk.ctxSubAgg hst hD (.ref hrok) (Sub.unpackAgg hsz) hZ
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      refine seqOutAgg (as₁ := vals [.ref (.array a), Val.i32 i, .ref r] ++ [.plain (.arraySet x)])
        (seqOutAgg (valsOutAgg (.cons hv₁ (.cons (ValOk.i32Agg _) (.cons hv₃ .nil))) ?_)
          (instrOutAgg (.arraySet hd he)))
        (seqOutAgg (valsOutAgg (vs := [.ref (.array a), Val.i32 _, Val.i32 _, Val.i32 _])
          (.cons hv₁ (.cons (ValOk.i32Agg _) (.cons (ValOk.i32Agg _)
          (.cons (ValOk.i32Agg _) .nil)))) ?_) (instrOutAgg (.arrayInitElem hd he hy hsz)))
      · intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        · exact hR
        · exact .num _
        · exact hZ
      · intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hR
        all_goals exact .num _
  | @arrayInitDataNull s f x y i j n =>
    exact trapCaseAgg (vs := [.ref .null, Val.i32 i, Val.i32 j, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayInitDataOob₁ s f x y i j n a ai _ _ =>
    exact trapCaseAgg (vs := [.ref (.array a), Val.i32 i, Val.i32 j, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayInitDataOob₂ s f x y i j n a da d ft di _ _ _ _ =>
    exact trapCaseAgg (vs := [.ref (.array a), Val.i32 i, Val.i32 j, Val.i32 n]) hst hD (by trivial)
      (by intro it h; cases h; rfl) hty
  | @arrayInitDataZero s f x y i j a da ai di _ _ _ =>
    exact nilCaseAgg (vs := [.ref (.array a), Val.i32 i, Val.i32 j, Val.i32 0]) hst hD (by trivial)
      (by intro it h; cases h; rfl) (by intro it h; cases h; rfl) hty
  | @arrayInitDataNum s f x y i j n a da ai d ft di v hai hd he hdat hle hn hv =>
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -, hok₂, hrep⟩ :=
      redexAgg (vs := [.ref (.array a), Val.i32 i, Val.i32 j, Val.i32 n]) hΔ
        (hiAgg hst (by trivial) (by intro it h; cases h; rfl)) hty
    have hr := InstrOk.aggAgg hi trivial
    obtain ⟨-, hp0, hr0⟩ := hr.regAgg hst trivial
    cases hr with
    | @arrayInitData _ _ d' z hd' he' hnv hy =>
      obtain ⟨e, hdok⟩ := hst.typeAgg hd'
      rw [hd] at e; cases e
      cases Expand.eqAgg he he'
      have hops := exactOpsAgg hst hD hvs hsub hp0
      rcases hops with _ | ⟨hv₁, -⟩
      have hR : TyOk {} (Ty.refT true (Ty.defHeap d)) := hp0 _ (by simp)
      have hZ : TyOk {} z.unpack := TyOk.unpack (Expand.array_ok hdok he)
      have hv₃ : ValOk s v z.unpack := readField_okAgg hv
      refine ⟨rfl, hs, Extend.refl hs, hrep _ _ ?_, hD⟩
      refine seqOutAgg (as₁ := vals [.ref (.array a), Val.i32 i, v] ++ [.plain (.arraySet x)])
        (seqOutAgg (valsOutAgg (.cons hv₁ (.cons (ValOk.i32Agg _) (.cons hv₃ .nil))) ?_)
          (instrOutAgg (.arraySet hd' he)))
        (seqOutAgg (valsOutAgg (vs := [.ref (.array a), Val.i32 _, Val.i32 _, Val.i32 _])
          (.cons hv₁ (.cons (ValOk.i32Agg _) (.cons (ValOk.i32Agg _)
          (.cons (ValOk.i32Agg _) .nil)))) ?_) (instrOutAgg (.arrayInitData hd' he hnv hy)))
      · intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        · exact hR
        · exact .num _
        · exact hZ
      · intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hR
        all_goals exact .num _

end Silmaril.Wasm.Execution.Core
