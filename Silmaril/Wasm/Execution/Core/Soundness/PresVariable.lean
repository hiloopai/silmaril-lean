module

public import Silmaril.Wasm.Execution.Core.Soundness.StateFacts

@[expose] public section

/-! # Preservation case lemmas for the variable family (`VariableStep`)

Spec rules (§4.3): `Step_read/local.get`, `Step/local.set`, `Step_pure/local.tee`,
`Step_read/global.get`, `Step/global.set`; typing rules `Instr_ok/local.get`,
`Instr_ok/local.set`, `Instr_ok/local.tee`, `Instr_ok/global.get`,
`Instr_ok/global.set`.

The code is typed in a context `Ct` related to the frame context `Cf`
(`Frame_ok`) by `LocalsLeVar Ct.locals Cf.locals`: same local types, and a local
set in `Ct` is set in `Cf`. This is `LocalsLe` of the generalised preservation
invariant (`Soundness/Preservation.lean`), spelled out.

* `localGet_presVar`, `globalGet_presVar`: the redex has no operands and no
  initialised locals, so `redex_inv` applies (no well-formedness needed);
* `globalSet_presVar`: also via `redex_inv`, plus the store update lemmas
  (`StoreOk.setGlobalVar`);
* `localTee_presVar`, `localSet_presVar`: the instruction initialises a local, so
  `redex_inv` does not apply; `AdminsOk.pair_auxVar` is a principal inversion for
  `[val, instr]` (it needs `C.toTypeCtx.Ok` to compose subsumptions).

Extra hypothesis (reported): `ValSubOk s Δ v` for the stored value of
`local.set`/`global.set`. The operand typing only gives `ValOk s v t` with
`Sub Δ t t'` in the *context*; storing `v` needs `ValOk s v t'`, i.e. runtime
subsumption from a context subtyping. For numeric and vector values this is
automatic (`ValSubOk.of_nonref`); for references it is the strengthening
`Sub Δ → Sub {}` on runtime types, which the current `StoreOk` does not support
(cf. `StateOk.redexSubOk` in the table/memory unit).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## The locals relation and runtime subsumption -/

/-- `L ≤ L'` pointwise: same length, same types, set locals stay set. (Definitionally
the `LocalsLe` of `Soundness/Preservation.lean`.) -/
abbrev LocalsLeVar (L L' : List LocalType) : Prop :=
  L.length = L'.length ∧
    ∀ (y : Nat) (a : LocalType), L[y]? = some a →
      ∃ b, L'[y]? = some b ∧ (a.type = b.type ∧ (a.init = .set → b.init = .set))

/-- Runtime subsumption for a value: a context subtype of a runtime type of `v`
is a runtime type of `v`. -/
def ValSubOk (s : Store H) (Δ : TypeCtx) (v : Val) : Prop :=
  ∀ t t', ValOk s v t → Sub Δ t t' → TyOk Δ t' → ValOk s v t'

theorem ValSubOk.of_nonref {s : Store H} {Δ : TypeCtx} {v : Val} (h : ∀ r, v ≠ .ref r) :
    ValSubOk s Δ v := by
  intro t t' hv hs _
  cases hv with
  | num n => cases hs; exact .num n
  | vec b => cases hs; exact .vec b
  | ref _ => exact absurd rfl (h _)

/-- Runtime subsumption in the empty context. -/
theorem ValOk.sub_emptyVar {s : Store H} {v : Val} {t t' : CValType} (hv : ValOk s v t)
    (hs : Sub {} t t') (hok : TyOk {} t') : ValOk s v t' := by
  cases hv with
  | num n => cases hs; exact .num n
  | vec b => cases hs; exact .vec b
  | ref h =>
    cases hs with
    | refv h' =>
      cases hok with
      | refv hr => exact .ref (.sub h hr h')

/-! ## Lists -/

theorem forall₂_setVar {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ (i : Nat) {a : α} {b : β}, R a b →
      List.Forall₂ R (l₁.set i a) (l₂.set i b)
  | _, _, .nil, _, _, _, _ => .nil
  | _, _, .cons _ t, 0, _, _, hab => .cons hab t
  | _, _, .cons h t, i + 1, _, _, hab => .cons h (forall₂_setVar t i hab)

theorem forall₂_getVar {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {b : β}, l₂[i]? = some b →
      ∃ a, l₁[i]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons h t, 0, _, e => by simp at e; subst e; exact ⟨_, rfl, h⟩
  | _, _, .cons _ t, i + 1, _, e => by simpa using forall₂_getVar t (i := i) (by simpa using e)

theorem forall₂_getVar' {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {a : α} {b : β},
      l₁[i]? = some a → l₂[i]? = some b → R a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons h t, 0, _, _, e₁, e₂ => by simp at e₁ e₂; subst e₁ e₂; exact h
  | _, _, .cons _ t, i + 1, _, _, e₁, e₂ =>
    forall₂_getVar' t (i := i) (by simpa using e₁) (by simpa using e₂)

theorem forall₂_snocVar {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {a : α} {b : β}, List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) →
      List.Forall₂ R l₁ l₂ ∧ R a b
  | [], [], _, _, .cons h .nil => ⟨.nil, h⟩
  | [], _ :: _, _, _, .cons _ t => by have := t.length_eq; simp at this
  | _ :: _, [], _, _, .cons _ t => by have := t.length_eq; simp at this
  | _ :: _, _ :: _, _, _, .cons h t =>
    let ih := forall₂_snocVar t
    ⟨.cons h ih.1, ih.2⟩

theorem ResultOk.of_subEqRVar {Δ : TypeCtx} :
    ∀ {a b : List CValType}, List.Forall₂ (SubEqR Δ) a b → ResultOk Δ a → ResultOk Δ b
  | _, _, .nil, _ => fun _ h => by cases h
  | _, _, .cons (a := x) (b := y) h t, ha => by
    intro u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · rcases h with rfl | ⟨_, hy⟩
      · exact ha _ (by simp)
      · exact hy
    · exact ResultOk.of_subEqRVar t (fun w hw => ha w (by simp [hw])) u hu

theorem ResultOk.of_subEqLVar {Δ : TypeCtx} :
    ∀ {a b : List CValType}, List.Forall₂ (SubEqL Δ) a b → ResultOk Δ b → ResultOk Δ a
  | _, _, .nil, _ => fun _ h => by cases h
  | _, _, .cons (a := x) (b := y) h t, hb => by
    intro u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · rcases h with rfl | ⟨_, hy⟩
      · exact hb _ (by simp)
      · exact hy
    · exact ResultOk.of_subEqLVar t (fun w hw => hb w (by simp [hw])) u hu

theorem resultOk_nilVar {Δ : TypeCtx} : ResultOk Δ [] := fun _ h => by cases h

/-! ## Principal inversion for a single instruction, with a well-formed frame -/

/-- `AdminsOk.single_aux`, additionally recording that the frame `ts` is well formed. -/
theorem AdminsOk.single_auxVar {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → ∀ a, as = [a] →
      C.toTypeCtx.Ok →
      ∃ ts it₀, ResultOk C.toTypeCtx ts ∧ AdminOk s C a it₀ ∧
        List.Forall₂ (SubEqL C.toTypeCtx) it.params (ts ++ it₀.params) ∧
        List.Forall₂ (SubEqR C.toTypeCtx) (ts ++ it₀.results) it.results ∧
        ∀ x ∈ it.inits, x ∉ it₀.inits → ∃ t, C.locals[x]? = some ⟨.set, t⟩
  | _, _, _, .nil, _, e, _ => by cases e
  | _, _, it, .single h, a, e, _ => by
    cases e
    exact ⟨[], it, resultOk_nilVar, h, forall₂_self (fun _ => .inl rfl) _,
      forall₂_self (fun _ => .inl rfl) _, fun _ hx hn => absurd hx hn⟩
  | C, _, _, .cons (t₁ := t₁) (t₂ := t₂) (xs₁ := xs₁) ha _ hs, a, e, hΔ => by
    obtain ⟨rfl, e₂⟩ := List.cons_eq_cons.mp e
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux hs e₂ hΔ'
    rw [Context.initLocals_toTypeCtx] at r₂ s₂
    refine ⟨[], ⟨t₁, xs₁, t₂⟩, resultOk_nilVar, ha, forall₂_self (fun _ => .inl rfl) _,
      forall₂_subEqR_of_sub s₂ r₂, ?_⟩
    intro x hx hn
    rcases List.mem_append.mp hx with hx | hx
    · exact absurd hx hn
    · obtain ⟨t, ht⟩ := i₂ x hx
      rcases Context.initLocals_set ht with hx' | h'
      · exact absurd hx' hn
      · exact ⟨t, h'⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, a, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    rcases List.append_eq_singleton_iff.mp e with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · obtain ⟨p₁, _, s₁, i₁⟩ := AdminsOk.nil_aux h₁ e₁ hΔ
      have hC : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
      obtain ⟨ts, it₀, hts, ha, hp, hr, hi⟩ := AdminsOk.single_auxVar h₂ a e₂ hΔ'
      rw [hC] at hts ha hp hr hi
      refine ⟨ts, it₀, hts, ha, forall₂_comp s₁ hp fun a _ _ ha' _ _ hab hbc =>
        SubEqL.sub_left hΔ hab (p₁ a ha') hbc, hr, ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact i₁ x hx
      · exact hi x hx hn
    · obtain ⟨ts, it₀, hts, ha, hp, hr, hi⟩ := AdminsOk.single_auxVar h₁ a e₁ hΔ
      obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux h₂ e₂ hΔ'
      rw [Context.initLocals_toTypeCtx] at r₂ s₂
      refine ⟨ts, it₀, hts, ha, hp, forall₂_comp hr s₂ fun _ _ c _ _ hc hab hbc =>
        SubEqR.sub_right hΔ hab hbc (r₂ c hc), ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact hi x hx hn
      · obtain ⟨t, ht⟩ := i₂ x hx
        rcases Context.initLocals_set ht with hx' | h'
        · exact hi x hx' hn
        · exact ⟨t, h'⟩
  | _, _, _, .sub (it := it) h hs hok, a, e, hΔ => by
    obtain ⟨ts, it₀, hts, ha, hp, hr, hi⟩ := AdminsOk.single_auxVar h a e hΔ
    refine ⟨ts, it₀, hts, ha, forall₂_comp hs.1 hp fun a _ _ ha' _ _ hab hbc =>
        SubEqL.sub_left hΔ hab (hok.1 a ha') hbc,
      forall₂_comp hr hs.2.1 fun _ _ c _ _ hc hab hbc =>
        SubEqR.sub_right hΔ hab hbc (hok.2.1 c hc), ?_⟩
    intro x hx hn
    by_cases hx' : x ∈ it.inits
    · exact hi x hx' hn
    · exact hs.2.2 x hx hx'
  | _, _, _, .frame (ts := F) h hok, a, e, hΔ => by
    obtain ⟨ts, it₀, hts, ha, hp, hr, hi⟩ := AdminsOk.single_auxVar h a e hΔ
    refine ⟨F ++ ts, it₀, ResultOk.append hok hts, ha, ?_, ?_, hi⟩
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hp
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hr

theorem subEqR_subEqL_subVar {Δ : TypeCtx} {a b c : CValType} (h₁ : SubEqR Δ a b)
    (h₂ : SubEqL Δ b c) : Sub Δ a c := by
  rcases h₁ with rfl | ⟨h₁, hb⟩
  · exact h₂.sub
  rcases h₂ with rfl | ⟨h₂, _⟩
  · exact h₁
  exact Sub.trans_val hb h₁ h₂

theorem forall₂_sub_of_subEqLVar {Δ : TypeCtx} :
    ∀ {a b : List CValType}, List.Forall₂ (SubEqL Δ) a b → List.Forall₂ (Sub Δ) a b
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h.sub (forall₂_sub_of_subEqLVar t)

theorem forall₂_sub_transVar {Δ : TypeCtx} :
    ∀ {a b c : List CValType}, List.Forall₂ (Sub Δ) a b → List.Forall₂ (Sub Δ) b c →
      ResultOk Δ b → List.Forall₂ (Sub Δ) a c
  | _, _, _, .nil, .nil, _ => .nil
  | _, _, _, .cons h t, .cons h' t', hb =>
    .cons (Sub.trans_val (hb _ (by simp)) h h')
      (forall₂_sub_transVar t t' fun u hu => hb u (by simp [hu]))

/-! ## Principal inversion for `[val, instr]` -/

/-- **Principal inversion for `[w, a]`**, where every typing of `a` has parameters.
The value `w` is consumed by the last parameter `tp` of a typing `it₀` of `a`;
the typing of the pair is `(ts ++ p₀ → ts ++ it₀.results)`, weakened. -/
theorem AdminsOk.pair_auxVar {s : Store H} {w : Val} {a : Admin}
    (hpar : ∀ C it₀, AdminOk s C a it₀ → it₀.params ≠ []) :
    ∀ {C : Context} {L : List Admin} {it : InstrType}, AdminsOk s C L it →
      L = [w.toAdmin, a] → C.toTypeCtx.Ok →
      ∃ ts it₀ p₀ tp tw, ResultOk C.toTypeCtx ts ∧ AdminOk s C a it₀ ∧
        it₀.params = p₀ ++ [tp] ∧ ValOk s w tw ∧ Sub C.toTypeCtx tw tp ∧
        ResultOk C.toTypeCtx it.params ∧
        List.Forall₂ (Sub C.toTypeCtx) it.params (ts ++ p₀) ∧
        List.Forall₂ (SubEqR C.toTypeCtx) (ts ++ it₀.results) it.results ∧
        ∀ x ∈ it.inits, x ∉ it₀.inits → ∃ t, C.locals[x]? = some ⟨.set, t⟩
  | _, _, _, .nil, e, _ => by cases e
  | _, _, _, .single _, e, _ => by simp at e
  | C, _, _, .cons (t₁ := t₁) (t₂ := t₂) (xs₁ := xs₁) (xs₂ := xs₂) ha _ hs, e, hΔ => by
    obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp e
    obtain ⟨tw, hit, hw⟩ := AdminOk.val_invRT ha
    simp only [InstrType.plain, InstrType.mk.injEq] at hit
    obtain ⟨rfl, rfl, rfl⟩ := hit
    obtain ⟨ts, it₀, hts, ha', hp, hr, hi⟩ := AdminsOk.single_auxVar hs _ rfl hΔ
    have hne := hpar _ _ ha'
    have hl := hp.length_eq
    obtain ⟨rfl, tp, hp0⟩ : ts = [] ∧ ∃ tp, it₀.params = [tp] := by
      match ts, it₀.params, hne, hl with
      | [], [tp], _, _ => exact ⟨rfl, tp, rfl⟩
      | [], [], hne, _ => exact absurd rfl hne
      | [], _ :: _ :: _, _, hl => simp at hl
      | _ :: _, [], hne, _ => exact absurd rfl hne
      | _ :: _, _ :: _, _, hl => simp at hl
    rw [hp0] at hp
    refine ⟨[], it₀, [], tp, tw, resultOk_nilVar, ha', hp0, hw, ?_,
      resultOk_nilVar, .nil, hr, ?_⟩
    · exact (List.forall₂_cons.mp hp).1.sub
    · intro x hx hn
      exact hi x (by simpa using hx) hn
  | C, _, _, .seq (as₁ := as₁) (as₂ := as₂) (xs₁ := xs₁) h₁ _ h₂, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    have ih₁ := fun e' => AdminsOk.pair_auxVar (w := w) hpar h₁ e' hΔ
    have ih₂ := fun e' => AdminsOk.pair_auxVar (w := w) hpar h₂ e' hΔ'
    rcases as₁ with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, as₁⟩⟩⟩
    · -- `[] ++ [w, a]`
      simp only [List.nil_append] at e
      obtain ⟨p₁, r₁, s₁, i₁⟩ := AdminsOk.nil_aux h₁ rfl hΔ
      have hC : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
      obtain ⟨ts, it₀, p₀, tp, tw, hts, ha, hp0, hw, htw, hpok, hp, hr, hi⟩ :=
        ih₂ e
      rw [hC] at hts ha htw hpok hp hr hi
      refine ⟨ts, it₀, p₀, tp, tw, hts, ha, hp0, hw, htw, p₁,
        forall₂_sub_transVar s₁ hp hpok, hr, ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact i₁ x hx
      · exact hi x hx hn
    · -- `[w] ++ [a]`
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨ts₁, it₁, hts₁, hw₁, hp₁, hr₁, hi₁⟩ := AdminsOk.single_auxVar h₁ _ rfl hΔ
      obtain ⟨tw, hit, hw⟩ := AdminOk.val_invRT hw₁
      subst hit
      simp only [List.append_nil] at hp₁ hr₁ hi₁
      have hset : ∀ x ∈ xs₁, ∃ t, C.locals[x]? = some ⟨.set, t⟩ :=
        fun x hx => hi₁ x hx (by simp)
      have hC : C.initLocals xs₁ = C := Context.initLocals_of_set hset
      obtain ⟨ts₂, it₀, hts₂, ha, hp₂, hr₂, hi₂⟩ := AdminsOk.single_auxVar h₂ _ rfl hΔ'
      rw [hC] at hts₂ ha hp₂ hr₂ hi₂
      obtain ⟨p₀, tp, hp0⟩ : ∃ p₀ tp, it₀.params = p₀ ++ [tp] := by
        rcases List.eq_nil_or_concat it₀.params with h | ⟨L, b, h⟩
        · exact absurd h (hpar _ _ ha)
        · exact ⟨L, b, by simpa using h⟩
      rw [hp0] at hp₂
      have hcomp : List.Forall₂ (Sub C.toTypeCtx) (ts₁ ++ [tw]) (ts₂ ++ p₀ ++ [tp]) := by
        have := forall₂_comp hr₁ hp₂ fun _ _ _ _ _ _ h h' => subEqR_subEqL_subVar h h'
        simpa [List.append_assoc] using this
      obtain ⟨hc₁, hc₂⟩ := forall₂_snocVar hcomp
      have hpok : ResultOk C.toTypeCtx _ := ResultOk.of_subEqLVar hp₁ hts₁
      refine ⟨ts₂, it₀, p₀, tp, tw, hts₂, ha, hp0, hw, hc₂, hpok,
        forall₂_sub_transVar (forall₂_sub_of_subEqLVar hp₁) hc₁ hts₁, hr₂, ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact hset x hx
      · exact hi₂ x hx hn
    · -- `[w, a] ++ []`
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      obtain ⟨ts, it₀, p₀, tp, tw, hts, ha, hp0, hw, htw, hpok, hp, hr, hi⟩ :=
        ih₁ rfl
      obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux h₂ rfl hΔ'
      rw [Context.initLocals_toTypeCtx] at r₂ s₂
      refine ⟨ts, it₀, p₀, tp, tw, hts, ha, hp0, hw, htw, hpok, hp,
        forall₂_comp hr s₂ fun _ _ c _ _ hc hab hbc => SubEqR.sub_right hΔ hab hbc (r₂ c hc), ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact hi x hx hn
      · obtain ⟨t, ht⟩ := i₂ x hx
        rcases Context.initLocals_set ht with hx' | h'
        · exact hi x hx' hn
        · exact ⟨t, h'⟩
    · simp at e
  | _, _, _, .sub (it := it) h hs hok, e, hΔ => by
    obtain ⟨ts, it₀, p₀, tp, tw, hts, ha, hp0, hw, htw, hpok, hp, hr, hi⟩ :=
      AdminsOk.pair_auxVar hpar h e hΔ
    refine ⟨ts, it₀, p₀, tp, tw, hts, ha, hp0, hw, htw, hok.1,
      forall₂_sub_transVar hs.1 hp hpok,
      forall₂_comp hr hs.2.1 fun _ _ c _ _ hc hab hbc =>
        SubEqR.sub_right hΔ hab hbc (hok.2.1 c hc), ?_⟩
    intro x hx hn
    by_cases hx' : x ∈ it.inits
    · exact hi x hx' hn
    · exact hs.2.2 x hx hx'
  | _, _, _, .frame (ts := F) h hok, e, hΔ => by
    obtain ⟨ts, it₀, p₀, tp, tw, hts, ha, hp0, hw, htw, hpok, hp, hr, hi⟩ :=
      AdminsOk.pair_auxVar hpar h e hΔ
    refine ⟨F ++ ts, it₀, p₀, tp, tw, ResultOk.append hok hts, ha, hp0, hw, htw,
      ResultOk.append hok hpok, ?_, ?_, hi⟩
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => Sub.refl _ (k := .val) trivial _) _) hp
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hr

/-! ## Inversion of the variable instruction typings -/

section inv

variable {C : Context} {it : InstrType}

theorem _root_.Silmaril.Wasm.Validation.InstrOk.localGet_invVar {x : LocalIdx} (h : InstrOk C (.localGet x) it) :
    ∃ t, C.locals[x.toNat]? = some ⟨.set, t⟩ ∧ it = .plain [] [t] := by
  cases h with
  | «variable» h => cases h with | localGet h => exact ⟨_, h, rfl⟩
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.localSet_invVar {x : LocalIdx} (h : InstrOk C (.localSet x) it) :
    ∃ i t, C.locals[x.toNat]? = some ⟨i, t⟩ ∧ it = ⟨[t], [x.toNat], []⟩ := by
  cases h with
  | «variable» h => cases h with | localSet h => exact ⟨_, _, h, rfl⟩
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.localTee_invVar {x : LocalIdx} (h : InstrOk C (.localTee x) it) :
    ∃ i t, C.locals[x.toNat]? = some ⟨i, t⟩ ∧ it = ⟨[t], [x.toNat], [t]⟩ := by
  cases h with
  | «variable» h => cases h with | localTee h => exact ⟨_, _, h, rfl⟩
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.globalGet_invVar {x : GlobalIdx} (h : InstrOk C (.globalGet x) it) :
    ∃ m t, C.globals[x.toNat]? = some ⟨m, t⟩ ∧ it = .plain [] [t] := by
  cases h with
  | «variable» h => cases h with | globalGet h => exact ⟨_, _, h, rfl⟩
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.globalSet_invVar {x : GlobalIdx} (h : InstrOk C (.globalSet x) it) :
    ∃ t, C.globals[x.toNat]? = some ⟨.var, t⟩ ∧ it = .plain [t] [] := by
  cases h with
  | «variable» h => cases h with | globalSet h => exact ⟨_, h, rfl⟩
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

end inv

theorem AdminOk.plain_invVar {s : Store H} {C : Context} {i : Instr} {it : InstrType}
    (h : AdminOk s C (.plain i) it) (hne : i ≠ .throwRef := by intro h; cases h) :
    InstrOk C i it := h.plain_inv_ne hne

/-! ## Frames -/

theorem ModuleInstOk.locals_nilVar {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.locals = [] := by
  cases h; rfl

theorem ModuleInstOk.globals_invVar {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) :
    List.Forall₂ (fun a g => ExternAddrOk s (.global a) (.global g)) mi.globals C.globals := by
  cases h with
  | mk _ _ hglobals => exact hglobals

/-- `Frame_ok` unfolded: the frame context is the module context with the frame's
local types. -/
theorem FrameOk.invVar {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    ∃ C₀, ModuleInstOk s f.module C₀ ∧ List.Forall₂ (LocalValOk s) f.locals C.locals ∧
      C = { C₀ with locals := C.locals } := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := h
  refine ⟨C₀, hm, by simpa [hm.locals_nilVar] using hl, rfl⟩

theorem FrameOk.localVar {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {y : Nat} {ov : Option Val} {lt : LocalType} (hf : f.locals[y]? = some ov)
    (hC : C.locals[y]? = some lt) : LocalValOk s ov lt := by
  obtain ⟨-, -, hl, -⟩ := h.invVar
  exact forall₂_getVar' hl hf hC

theorem FrameOk.globalVar {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {x : GlobalIdx} {gt : CGlobalType} (hx : C.globals[x.toNat]? = some gt) :
    ∃ a, f.module.globals[x.toNat]? = some a ∧ ExternAddrOk s (.global a) (.global gt) := by
  obtain ⟨C₀, hm, -, hC⟩ := h.invVar
  have hg : C.globals = C₀.globals := by rw [hC]
  rw [hg] at hx
  exact forall₂_getVar hm.globals_invVar hx

theorem LocalValOk.set_invVar {s : Store H} {v : Val} {t : CValType}
    (h : LocalValOk s (some v) ⟨.set, t⟩) : ValOk s v t := by
  cases h with | set h => exact h

theorem Store.global?_specVar {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} (h : s.global? f x = some (a, g)) :
    f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some g := by
  simp only [Store.global?] at h
  cases h₁ : f.module.globals[x.toNat]? with
  | none => simp [h₁] at h
  | some b =>
    cases h₂ : s.globals[b]? with
    | none => simp [h₁, h₂] at h
    | some t =>
      simp [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h₂⟩

/-- Inversion of a typed global address, in a valid store. -/
theorem ExternAddrOk.global_invVar {s : Store H} (hs : StoreOk s) {xa : ExternAddr}
    {xt : CExternType} (h : ExternAddrOk s xa xt) :
    ∀ a gt, xa = .global a → xt = .global gt →
      ∃ gi, s.globals[a]? = some gi ∧ TyOk {} gt.type ∧
        gi.type.mutability = gt.mutability ∧
        (∀ v, ValOk s v gi.type.type → ValOk s v gt.type) ∧
        (gt.mutability = .var → ∀ v, ValOk s v gt.type → ValOk s v gi.type.type) := by
  induction h with
  | @global a' gi h =>
    intro a gt ha hg
    cases ha; cases hg
    exact ⟨gi, h, (hs.globals gi (List.mem_of_getElem? h)).1, rfl, fun _ h => h,
      fun _ _ h => h⟩
  | sub _ hok hsub ih =>
    intro a gt ha hg
    subst ha hg
    cases hsub with
    | @global g' _ hgs =>
      obtain ⟨gi, hgi, hok', hm, hfw, hbw⟩ := ih a g' rfl rfl
      have htok : TyOk {} gt.type := by cases hok with | global h => exact h
      cases hgs with
      | const h₁ =>
        exact ⟨gi, hgi, htok, hm, fun v hv => (hfw v hv).sub_emptyVar h₁ htok,
          fun e => by cases e⟩
      | var h₁ h₂ =>
        exact ⟨gi, hgi, htok, hm, fun v hv => (hfw v hv).sub_emptyVar h₁ htok,
          fun _ v hv => hbw rfl v (hv.sub_emptyVar h₂ hok')⟩
  | tag => intro a gt ha; cases ha
  | mem => intro a gt ha; cases ha
  | table => intro a gt ha; cases ha
  | func => intro a gt ha; cases ha

/-! ## Local contexts -/

theorem Context.initLocals_singleVar (C : Context) {y : Nat} {lt : LocalType}
    (h : C.locals[y]? = some lt) :
    (C.initLocals [y]).locals = C.locals.set y ⟨.set, lt.type⟩ := by
  apply List.ext_getElem?
  intro z
  rw [Context.initLocals_locals, List.getElem?_set]
  by_cases hz : y = z
  · subst hz
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
    simp [hlt]
  · have : z ≠ y := fun e => hz e.symm
    simp [hz, this]

theorem LocalsLeVar.initLocals_singleVar {L L' : List LocalType} (h : LocalsLeVar L L')
    {y : Nat} {a : LocalType} (ha : L[y]? = some a) {b : LocalType} (hb : L'[y]? = some b)
    (hab : a.type = b.type) :
    LocalsLeVar (L.set y ⟨.set, a.type⟩) (L'.set y ⟨.set, b.type⟩) := by
  refine ⟨by simp [h.1], fun z c hc => ?_⟩
  rw [List.getElem?_set] at hc ⊢
  by_cases hz : y = z
  · subst hz
    have hl : y < L.length := (List.getElem?_eq_some_iff.mp ha).1
    have hl' : y < L'.length := (List.getElem?_eq_some_iff.mp hb).1
    simp only [hl, hl', ite_true] at hc ⊢
    cases hc
    exact ⟨_, rfl, hab, fun _ => rfl⟩
  · simp only [hz, ite_false] at hc ⊢
    exact h.2 z c hc

/-! ## The case lemmas -/

/-- **`local.get`** (`Step_read/local.get`). -/
theorem localGet_presVar {s : Store H} {f : Frame} {Cf Ct : Context} {x : LocalIdx} {v : Val}
    {it : InstrType} (hf : FrameOk s f Cf) (hL : LocalsLeVar Ct.locals Cf.locals)
    (hx : f.local? x = some (some v)) (h : AdminsOk s Ct [.plain (.localGet x)] it) :
    AdminsOk s Ct [v.toAdmin] it := by
  obtain ⟨t₁, t₂, ts, hi, hvs, hB, hrep⟩ := redex_inv (vs := []) (i := .localGet x)
    (fun it' h' => by obtain ⟨t, -, rfl⟩ := h'.localGet_invVar; exact ⟨rfl, rfl⟩) h
  obtain ⟨t, ht, hit⟩ := hi.localGet_invVar
  simp only [InstrType.plain, InstrType.mk.injEq] at hit
  obtain ⟨rfl, -, rfl⟩ := hit
  obtain ⟨b, hb, hty, hset⟩ := hL.2 _ _ ht
  obtain ⟨bi, bt⟩ := b
  simp only at hty hset
  have hbi := hset trivial
  subst hty hbi
  have hv := (hf.localVar hx hb).set_invVar
  exact hrep s _ (AdminsOk.val_single hv)

/-- **`global.get`** (`Step_read/global.get`). -/
theorem globalGet_presVar {s : Store H} {f : Frame} {Cf Ct : Context} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf)
    (hg : Ct.globals = Cf.globals) (hx : s.global? f x = some (a, g))
    (h : AdminsOk s Ct [.plain (.globalGet x)] it) :
    AdminsOk s Ct [g.value.toAdmin] it := by
  obtain ⟨t₁, t₂, ts, hi, hvs, hB, hrep⟩ := redex_inv (vs := []) (i := .globalGet x)
    (fun it' h' => by obtain ⟨_, t, -, rfl⟩ := h'.globalGet_invVar; exact ⟨rfl, rfl⟩) h
  obtain ⟨m, t, ht, hit⟩ := hi.globalGet_invVar
  simp only [InstrType.plain, InstrType.mk.injEq] at hit
  obtain ⟨rfl, -, rfl⟩ := hit
  rw [hg] at ht
  obtain ⟨a', ha', hxa⟩ := hf.globalVar ht
  obtain ⟨hfa, hga⟩ := Store.global?_specVar hx
  rw [hfa] at ha'
  cases ha'
  obtain ⟨gi, hgi, -, -, hfw, -⟩ := hxa.global_invVar hs a _ rfl rfl
  rw [hga] at hgi
  cases hgi
  have hv := hfw _ (hs.globals g (List.mem_of_getElem? hga)).2
  exact hrep s _ (AdminsOk.val_single hv)

/-- **`local.tee`** (`Step_pure/local.tee`). -/
theorem localTee_presVar {s : Store H} {C : Context} {x : LocalIdx} {v : Val} {it : InstrType}
    (hΔ : C.toTypeCtx.Ok) (hloc : ∀ lt ∈ C.locals, TyOk C.toTypeCtx lt.type)
    (h : AdminsOk s C [v.toAdmin, .plain (.localTee x)] it) :
    AdminsOk s C [v.toAdmin, v.toAdmin, .plain (.localSet x)] it := by
  obtain ⟨ts, it₀, p₀, tp, tw, hts, ha, hp0, hw, htw, hpok, hp, hr, hi⟩ :=
    AdminsOk.pair_auxVar (w := v) (a := .plain (.localTee x))
      (fun C it₀ h' => by
        cases h' with
        | plain h' => obtain ⟨_, _, -, rfl⟩ := h'.localTee_invVar; simp) h rfl hΔ
  obtain ⟨i, t, hlt, rfl⟩ := (AdminOk.plain_invVar ha).localTee_invVar
  simp only at hp0
  obtain ⟨rfl, rfl⟩ : p₀ = [] ∧ t = tp := by
    rcases p₀ with _ | ⟨_, _ | _⟩ <;> simp_all
  simp only [List.append_nil] at hp hr
  have htok : TyOk C.toTypeCtx t := hloc _ (List.mem_of_getElem? hlt)
  -- `[v, v, local.set x] : [] →_{x} [t]`
  have hv : AdminsOk s C [v.toAdmin] (.plain [] [t]) := AdminsOk.val_sub hw htw htok
  have hset : AdminsOk s C [.plain (.localSet x)] ⟨[t], [x.toNat], []⟩ :=
    .single (.plain (.variable (.localSet hlt)))
  have h1 : AdminsOk s C [v.toAdmin, .plain (.localSet x)] ⟨[], [x.toNat], []⟩ :=
    AdminsOk.seq (xs₁ := []) hv (by simp) hset
  have h2 : AdminsOk s C [v.toAdmin, .plain (.localSet x)] ⟨[t], [x.toNat], [t]⟩ := by
    simpa using AdminsOk.frame (ts := [t]) h1 (by simpa [ResultOk] using htok)
  have h3 : AdminsOk s C [v.toAdmin, v.toAdmin, .plain (.localSet x)] ⟨[], [x.toNat], [t]⟩ :=
    AdminsOk.seq (xs₁ := []) hv (by simp) h2
  have h4 := AdminsOk.frame (ts := ts) h3 hts
  simp only [List.append_nil] at h4
  have hrok : ResultOk C.toTypeCtx it.results :=
    ResultOk.of_subEqRVar hr (ResultOk.append hts (by simpa [ResultOk] using htok))
  have hset' : ∀ y ∈ it.inits, y ∉ [x.toNat] → ∃ t, C.locals[y]? = some ⟨.set, t⟩ :=
    fun y hy hn => hi y hy hn
  refine AdminsOk.sub h4 ⟨hp, forall₂_comp hr (forall₂_self (R := Eq) (fun _ => rfl) _)
    (fun _ _ _ _ _ _ h e => e ▸ h.sub), hset'⟩ ⟨hpok, hrok, fun y hy => ?_⟩
  by_cases hyx : y = x.toNat
  · subst hyx; exact ⟨_, hlt⟩
  · obtain ⟨t', ht'⟩ := hset' y hy (by simpa using hyx)
    exact ⟨_, ht'⟩

/-- **`local.set`** (`Step/local.set`). The frame context initialises local `x`
(`Cf.initLocals [x]`), and the code context too (`Ct.initLocals [x]`); the
empty reduct is typed at the redex's type there (`Instrtype_sub` only needs the
newly initialised locals to be set).

Extra hypotheses (reported): `Ct.toTypeCtx.Ok` and valid local types, to compose
subsumptions in the inversion; `ValSubOk` to store `v` (see the module doc). -/
theorem localSet_presVar {s : Store H} {f : Frame} {Cf Ct : Context} {x : LocalIdx} {v : Val}
    {it : InstrType} (hΔ : Ct.toTypeCtx.Ok) (hloc : ∀ lt ∈ Ct.locals, TyOk Ct.toTypeCtx lt.type)
    (hvsub : ValSubOk s Ct.toTypeCtx v) (hf : FrameOk s f Cf)
    (hL : LocalsLeVar Ct.locals Cf.locals)
    (h : AdminsOk s Ct [v.toAdmin, .plain (.localSet x)] it) :
    FrameOk s (f.setLocal x v) (Cf.initLocals [x.toNat]) ∧
      LocalsLeVar (Ct.initLocals [x.toNat]).locals (Cf.initLocals [x.toNat]).locals ∧
      AdminsOk s (Ct.initLocals [x.toNat]) [] it := by
  obtain ⟨ts, it₀, p₀, tp, tw, hts, ha, hp0, hw, htw, hpok, hp, hr, hi⟩ :=
    AdminsOk.pair_auxVar (w := v) (a := .plain (.localSet x))
      (fun C it₀ h' => by
        cases h' with
        | plain h' => obtain ⟨_, _, -, rfl⟩ := h'.localSet_invVar; simp) h rfl hΔ
  obtain ⟨i, t, hlt, rfl⟩ := (AdminOk.plain_invVar ha).localSet_invVar
  simp only at hp0
  obtain ⟨rfl, rfl⟩ : p₀ = [] ∧ t = tp := by
    rcases p₀ with _ | ⟨_, _ | _⟩ <;> simp_all
  simp only [List.append_nil] at hp hr
  have htok : TyOk Ct.toTypeCtx t := hloc _ (List.mem_of_getElem? hlt)
  have hvt : ValOk s v t := hvsub tw t hw htw htok
  obtain ⟨b, hb, hty, -⟩ := hL.2 _ _ hlt
  simp only at hty
  obtain ⟨C₀, hm, hl, hC⟩ := hf.invVar
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨C₀, (Cf.initLocals [x.toNat]).locals, hm, ?_, ?_⟩
    · rw [Context.initLocals_singleVar Cf hb]
      exact forall₂_setVar hl _ (.set (hty ▸ hvt))
    · rw [hm.locals_nilVar, List.nil_append]
      have e := Context.initLocals_eq_with Cf [x.toNat]
      generalize (Cf.initLocals [x.toNat]).locals = L at e ⊢
      rw [e, hC]
  · rw [Context.initLocals_singleVar Ct hlt, Context.initLocals_singleVar Cf hb]
    exact hL.initLocals_singleVar hlt hb hty
  · have e : (Ct.initLocals [x.toNat]).toTypeCtx = Ct.toTypeCtx :=
      Context.initLocals_toTypeCtx _ _
    have hsetC' : ∀ y ∈ it.inits, ∃ t',
        (Ct.initLocals [x.toNat]).locals[y]? = some ⟨.set, t'⟩ := by
      intro y hy
      by_cases hyx : y = x.toNat
      · subst hyx
        exact ⟨_, Context.initLocals_set_of_mem (List.mem_singleton_self _) hlt⟩
      · obtain ⟨t', ht'⟩ := hi y hy (by simpa using hyx)
        exact ⟨t', Context.initLocals_set_of_set ht'⟩
    have hid : AdminsOk s (Ct.initLocals [x.toNat]) [] ⟨ts, [], ts⟩ :=
      AdminsOk.id (by rw [e]; exact hts)
    refine AdminsOk.sub hid ⟨?_, ?_, fun y hy _ => hsetC' y hy⟩ ⟨?_, ?_, ?_⟩
    · show ResultSub _ _ _
      rw [e]; exact hp
    · show ResultSub _ _ _
      rw [e]; exact hr.imp fun _ _ h => h.sub
    · show ResultOk _ _
      rw [e]; exact hpok
    · show ResultOk _ _
      rw [e]; exact ResultOk.of_subEqRVar hr hts
    · intro y hy
      obtain ⟨t', h'⟩ := hsetC' y hy
      exact ⟨_, h'⟩

/-! ## Updating a global -/

theorem ImmutReachable.transferVar {s s' : Store H} (hstructs : s'.structs = s.structs)
    (harrays : s'.arrays = s.arrays) (hexns : s'.exns = s.exns) {a b : FieldVal}
    (h : ImmutReachable s' a b) : ImmutReachable s a b := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct (hstructs ▸ hs) he hi hfv
  | refArray hs he hfv => exact .refArray (harrays ▸ hs) he hfv
  | refExn hs hv => exact .refExn (hexns ▸ hs) hv
  | refExtern r => exact .refExtern r

/-- Writing a value of the global's type into a mutable global keeps the store
valid and extends it. -/
theorem StoreOk.setGlobalVar {s : Store H} {a : Nat} {g : GlobalInst} {v : Val}
    (hs : StoreOk s) (ha : s.globals[a]? = some g) (hmut : g.type.mutability = .var)
    (hv : ValOk s v g.type.type) :
    StoreOk (s.setGlobal a v) ∧ Extend s (s.setGlobal a v) := by
  have hext : ExtendsList ExtendGlobal s.globals (s.setGlobal a v).globals := by
    refine ⟨by simp [Store.setGlobal], fun i x hx => ?_⟩
    simp only [Store.setGlobal, List.getElem?_modify, hx]
    by_cases hia : a = i
    · subst hia
      rw [ha] at hx
      cases hx
      exact ⟨{ g with value := v }, by simp, rfl, .inl hmut⟩
    · exact ⟨_, by simp [hia], rfl, .inr rfl⟩
  have he : Extend s (s.setGlobal a v) := { Extend.refl hs with globals := hext }
  refine ⟨?_, he⟩
  exact {
    tags := fun ti h => hs.tags ti h
    globals := fun gi h => by
      simp only [Store.setGlobal] at h
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
      rw [List.getElem_modify]
      have hi' : i < s.globals.length := by simpa using hi
      have hg := hs.globals _ (List.getElem_mem hi')
      split
      · next hai =>
        subst hai
        have : s.globals[a] = g := by
          rw [List.getElem?_eq_getElem hi'] at ha; exact Option.some.inj ha
        rw [this] at hg ⊢
        exact ⟨hg.1, hv.extend he⟩
      · exact ⟨hg.1, hg.2.extend he⟩
    mems := hs.mems
    tables := fun ti h =>
      ⟨(hs.tables ti h).1, (hs.tables ti h).2.1, fun r hr => ((hs.tables ti h).2.2 r hr).extend he⟩
    funcs := fun fi h => by
      cases hs.funcs fi h with
      | wasm hdt hm hcode hf hsub => exact .wasm hdt (hm.extend hs he) hcode hf hsub
      | host hdt he' hcode => exact .host hdt he' hcode
    elems := fun ei h => (hs.elems ei h).extend he ⟨rfl, .inl rfl⟩
    structs := fun si h => by
      obtain ⟨fs, hx, hf⟩ := hs.structs si h
      exact ⟨fs, hx, hf.imp fun _ _ h => h.extend he⟩
    arrays := fun ai h => by
      obtain ⟨ft, hx, hf⟩ := hs.arrays ai h
      exact ⟨ft, hx, fun fv hfv => (hf fv hfv).extend he⟩
    exns := fun e h => by
      obtain ⟨ti, ts, ht, hx, hf⟩ := hs.exns e h
      exact ⟨ti, ts, ht, hx, hf.imp fun _ _ h => h.extend he⟩
    acyclicStructs := fun b hb hr => hs.acyclicStructs b hb
      (ImmutReachable.transferVar (s := s) (s' := s.setGlobal a v) rfl rfl rfl hr)
    acyclicArrays := fun b hb hr => hs.acyclicArrays b hb
      (ImmutReachable.transferVar (s := s) (s' := s.setGlobal a v) rfl rfl rfl hr)
    acyclicExns := fun b hb hr => hs.acyclicExns b hb
      (ImmutReachable.transferVar (s := s) (s' := s.setGlobal a v) rfl rfl rfl hr)
    structsClosed := hs.structsClosed
    arraysClosed := hs.arraysClosed }

/-- **`global.set`** (`Step/global.set`).

Extra hypothesis (reported): `ValSubOk` to store `v` (see the module doc). -/
theorem globalSet_presVar {s : Store H} {f : Frame} {Cf Ct : Context} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} {v : Val} {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf)
    (hg : Ct.globals = Cf.globals) (hvsub : ValSubOk s Ct.toTypeCtx v)
    (hx : s.global? f x = some (a, g))
    (h : AdminsOk s Ct [v.toAdmin, .plain (.globalSet x)] it) :
    StoreOk (s.setGlobal a v) ∧ Extend s (s.setGlobal a v) ∧ FrameOk (s.setGlobal a v) f Cf ∧
      AdminsOk (s.setGlobal a v) Ct [] it := by
  obtain ⟨t₁, t₂, ts, hi, hvs, hB, hrep⟩ := redex_inv (vs := [v]) (i := .globalSet x)
    (fun it' h' => by obtain ⟨t, -, rfl⟩ := h'.globalSet_invVar; exact ⟨rfl, rfl⟩) h
  obtain ⟨t, ht, hit⟩ := hi.globalSet_invVar
  simp only [InstrType.plain, InstrType.mk.injEq] at hit
  obtain ⟨rfl, -, rfl⟩ := hit
  obtain ⟨tv, hv, rfl⟩ : ∃ tv, ValOk s v tv ∧ ts = [tv] := by
    rcases hvs with _ | ⟨hv, _ | _⟩
    exact ⟨_, hv, rfl⟩
  have hsub : Sub Ct.toTypeCtx tv t := by
    cases hB with | cons h _ => exact h
  rw [hg] at ht
  obtain ⟨a', ha', hxa⟩ := hf.globalVar ht
  obtain ⟨hfa, hga⟩ := Store.global?_specVar hx
  rw [hfa] at ha'
  cases ha'
  obtain ⟨gi, hgi, htok, hm, -, hbw⟩ := hxa.global_invVar hs a _ rfl rfl
  rw [hga] at hgi
  cases hgi
  have hvt : ValOk s v t := hvsub tv t hv hsub (TyOk.ofEmpty htok _)
  have hvg : ValOk s v g.type.type := hbw rfl v hvt
  obtain ⟨hs', he⟩ := StoreOk.setGlobalVar hs hga hm hvg
  exact ⟨hs', he, FrameOk.extend hs he hf, hrep _ _ AdminsOk.nil⟩

/-- **The variable family**, packaged: each `VariableStep` preserves the typing of
the code under a context whose locals are below the frame's.  The frame context
changes only for `local.set` (to `Cf.initLocals [x]`), and so does the code context
(to `Ct.initLocals [x]`). -/
theorem VariableStep.presVar {c c' : Config H} {Cf Ct : Context} {it : InstrType}
    (h : VariableStep c c') (hs : StoreOk c.store) (hf : FrameOk c.store c.frame Cf)
    (hL : LocalsLeVar Ct.locals Cf.locals) (hg : Ct.globals = Cf.globals)
    (hΔ : Ct.toTypeCtx.Ok) (hloc : ∀ lt ∈ Ct.locals, TyOk Ct.toTypeCtx lt.type)
    (hvsub : ∀ v, ValSubOk c.store Ct.toTypeCtx v)
    (hty : AdminsOk c.store Ct c.code it) :
    ∃ Cf' Ct', StoreOk c'.store ∧ Extend c.store c'.store ∧ FrameOk c'.store c'.frame Cf' ∧
      ((Cf' = Cf ∧ Ct' = Ct) ∨ ∃ y, Cf' = Cf.initLocals [y] ∧ Ct' = Ct.initLocals [y]) ∧
      LocalsLeVar Ct'.locals Cf'.locals ∧ AdminsOk c'.store Ct' c'.code it := by
  cases h with
  | localGet hx =>
    exact ⟨Cf, Ct, hs, Extend.refl hs, hf, .inl ⟨rfl, rfl⟩, hL, localGet_presVar hf hL hx hty⟩
  | localSet _ =>
    rename_i x v _
    obtain ⟨hf', hL', hty'⟩ := localSet_presVar hΔ hloc (hvsub v) hf hL hty
    exact ⟨_, _, hs, Extend.refl hs, hf', .inr ⟨x.toNat, rfl, rfl⟩, hL', hty'⟩
  | localTee =>
    exact ⟨Cf, Ct, hs, Extend.refl hs, hf, .inl ⟨rfl, rfl⟩, hL, localTee_presVar hΔ hloc hty⟩
  | globalGet hx =>
    exact ⟨Cf, Ct, hs, Extend.refl hs, hf, .inl ⟨rfl, rfl⟩, hL,
      globalGet_presVar hs hf hg hx hty⟩
  | globalSet hx =>
    rename_i v
    obtain ⟨hs', he, hf', hty'⟩ := globalSet_presVar hs hf hg (hvsub v) hx hty
    exact ⟨Cf, Ct, hs', he, hf', .inl ⟨rfl, rfl⟩, hL, hty'⟩

end Silmaril.Wasm.Execution.Core
