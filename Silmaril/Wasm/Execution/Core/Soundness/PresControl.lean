module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Validation.Subtyping.Properties
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping

@[expose] public section

/-! # Preservation for the control rules of `Step` (replacement lemmas)

For each control rule (`block`, `loop`, `if`, `label-vals`, branches, `return`,
`frame-vals`, `handler-vals`, `try_table`) an `AdminsOk`-level replacement
lemma: a typing of the left-hand side at any `it` yields a typing of the
right-hand side at the same `it`, under explicit well-formedness hypotheses on
the context (`C.Wf`, and `C.types = f.module.types` for rules reading the
frame's module).

The redex-inversion infrastructure is duplicated from `RedexTyping.lean`
(suffix `Ctl`), since that file is owned by another unit and did not build
when this unit was written.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}


/-! ## Lists -/

theorem List.forall₂_append_right_splitCtl {α β : Type _} {R : α → β → Prop} {l : List α}
    {l₁ l₂ : List β} (h : List.Forall₂ R l (l₁ ++ l₂)) :
    ∃ a b, l = a ++ b ∧ List.Forall₂ R a l₁ ∧ List.Forall₂ R b l₂ := by
  refine ⟨l.take l₁.length, l.drop l₁.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · exact List.forall₂_take_append l l₁ l₂ h
  · exact List.forall₂_drop_append l l₁ l₂ h

theorem ResultOk.appendRTCtl {Δ : TypeCtx} {a b : List CValType} (ha : ResultOk Δ a) (hb : ResultOk Δ b) :
    ResultOk Δ (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem ResultOk.singleCtl {Δ : TypeCtx} {t : CValType} (h : TyOk Δ t) : ResultOk Δ [t] := by
  intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact h

theorem ResultOk.leftRTCtl {Δ : TypeCtx} {a b : List CValType} (h : ResultOk Δ (a ++ b)) :
    ResultOk Δ a := fun t ht => h t (List.mem_append_left _ ht)

theorem ResultOk.rightRTCtl {Δ : TypeCtx} {a b : List CValType} (h : ResultOk Δ (a ++ b)) :
    ResultOk Δ b := fun t ht => h t (List.mem_append_right _ ht)

/-! ## Transitivity of value subtyping (no context well-formedness needed) -/

theorem Sub.trans_heapCtl {Δ : TypeCtx} {a b c : CHeapType} (hb : TyOk Δ b) (hab : Sub Δ a b)
    (hbc : Sub Δ b c) : Sub Δ a c := .heapTrans hb hab hbc

theorem Sub.trans_refCtl {Δ : TypeCtx} {a b c : CRefType} (hb : TyOk Δ b) (hab : Sub Δ a b)
    (hbc : Sub Δ b c) : Sub Δ a c := by
  cases hb with
  | ref hh =>
    cases hab with
    | refNonNull h1 =>
      cases hbc with
      | refNonNull h2 => exact .refNonNull (.heapTrans hh h1 h2)
      | refNull h2 => exact .refNull (.heapTrans hh h1 h2)
    | refNull h1 =>
      cases hbc with
      | refNull h2 => exact .refNull (.heapTrans hh h1 h2)

theorem Sub.trans_valCtl {Δ : TypeCtx} {a b c : CValType} (hb : TyOk Δ b) (hab : Sub Δ a b)
    (hbc : Sub Δ b c) : Sub Δ a c := by
  cases hab with
  | num => exact hbc
  | vec => exact hbc
  | botv => exact .botv
  | refv h1 =>
    cases hb with
    | refv hr =>
      cases hbc with
      | refv h2 => exact .refv (Sub.trans_refCtl hr h1 h2)

theorem ResultSub.trans_okCtl {Δ : TypeCtx} {a b c : List CValType} (hb : ResultOk Δ b)
    (hab : ResultSub Δ a b) (hbc : ResultSub Δ b c) : ResultSub Δ a c := by
  induction hab generalizing c with
  | nil => exact hbc
  | cons h _ ih =>
    cases hbc with
    | cons h' hl' =>
      exact .cons (Sub.trans_valCtl (hb _ (by simp)) h h')
        (ih (fun t ht => hb t (by simp [ht])) hl')

/-! ## Empty sequences -/

theorem AdminsOk.nil_storeCtl {H' : Type} {s : Store H} (s' : Store H') :
    ∀ {C : Context} {as : List Admin}
    {it : InstrType}, AdminsOk s C as it → as = [] → AdminsOk s' C [] it
  | _, _, _, .nil, _ => .nil
  | _, _, _, .single _, he => by simp at he
  | _, _, _, .cons _ _ _, he => by simp at he
  | _, _, _, .seq h₁ hx h₂, he => by
    obtain ⟨e₁, e₂⟩ := List.append_eq_nil_iff.mp he
    have := AdminsOk.seq (AdminsOk.nil_storeCtl s' h₁ e₁) hx (AdminsOk.nil_storeCtl s' h₂ e₂)
    simpa using this
  | _, _, _, .sub h hs hok, he => .sub (AdminsOk.nil_storeCtl s' h he) hs hok
  | _, _, _, .frame h hok, he => .frame (AdminsOk.nil_storeCtl s' h he) hok

/-! ## Lifting a typing through `sub`/`frame` steps and empty sequences -/

/-- A sequence of `Instrs_ok2/sub` and `Instrs_ok2/frame` steps, and compositions
with typed empty sequences on either side. -/
inductive LiftCtl (C : Context) : InstrType → InstrType → Prop where
  | refl {it : InstrType} : LiftCtl C it it
  | sub {it₀ it₁ it₂ : InstrType} (h : LiftCtl C it₀ it₁) (hs : InstrTypeSub C it₁ it₂)
      (hok : InstrTypeOk C it₂) : LiftCtl C it₀ it₂
  | frame {it₀ : InstrType} {ts p r : List CValType} {x : List Nat}
      (h : LiftCtl C it₀ ⟨p, x, r⟩) (hok : ResultOk C.toTypeCtx ts) :
      LiftCtl C it₀ ⟨ts ++ p, x, ts ++ r⟩
  | tail {it₀ : InstrType} {p m r : List CValType} {x₁ x₂ : List Nat}
      (h : LiftCtl C it₀ ⟨p, x₁, m⟩) (hx : ∀ x ∈ x₁, ∃ lt, C.locals[x]? = some lt)
      (ht : ∀ {H' : Type} (s : Store H'), AdminsOk s (C.initLocals x₁) [] ⟨m, x₂, r⟩) :
      LiftCtl C it₀ ⟨p, x₁ ++ x₂, r⟩
  | head {it₀ : InstrType} {p m r : List CValType} {x₁ x₂ : List Nat}
      (h : LiftCtl C it₀ ⟨m, x₂, r⟩) (hp : ResultSub C.toTypeCtx p m)
      (hpok : ResultOk C.toTypeCtx p) (hmok : ResultOk C.toTypeCtx m)
      (hx : ∀ x ∈ x₁, ∃ t, C.locals[x]? = some ⟨.set, t⟩) :
      LiftCtl C it₀ ⟨p, x₁ ++ x₂, r⟩

theorem LiftCtl.apply {s : Store H} {C : Context} {as : List Admin} {it₀ it : InstrType}
    (hl : LiftCtl C it₀ it) (h : AdminsOk s C as it₀) : AdminsOk s C as it := by
  induction hl with
  | refl => exact h
  | sub _ hs hok ih => exact .sub ih hs hok
  | frame _ hok ih => exact .frame ih hok
  | tail _ hx ht ih => simpa using AdminsOk.seq ih hx (ht s)
  | @head p m r x₁ x₂ _ hp hpok hmok hx ih =>
    have hx' : ∀ x ∈ x₁, ∃ lt, C.locals[x]? = some lt := fun x hx' =>
      let ⟨_, ht⟩ := hx x hx'; ⟨_, ht⟩
    have h0 : AdminsOk s C [] ⟨p, x₁, m⟩ :=
      .sub (AdminsOk.id hpok) ⟨ResultSub.refl _ _, hp, fun x hx'' _ => hx x hx''⟩
        ⟨hpok, hmok, hx'⟩
    have := AdminsOk.seq h0 hx' (by rw [Context.initLocals_of_set hx]; exact ih)
    simpa using this

/-- Dropping operands from the top of the parameter stack. -/
theorem LiftCtl.dropTopCtl {C : Context} {it₀ it : InstrType} (hl : LiftCtl C it₀ it) :
    ∀ {A B : List CValType}, it₀.params = A ++ B →
    ∃ QA QB, it.params = QA ++ QB ∧ ResultSub C.toTypeCtx QB B ∧
      LiftCtl C ⟨A, it₀.inits, it₀.results⟩ ⟨QA, it.inits, it.results⟩ ∧
      (QB = B ∨ ResultOk C.toTypeCtx QB) := by
  induction hl with
  | refl =>
    intro A B he
    exact ⟨A, B, he, ResultSub.refl _ _, .refl, .inl rfl⟩
  | sub _ hs hok ih =>
    intro A B he
    obtain ⟨QA, QB, hp, hQB, hl, hinv⟩ := ih he
    obtain ⟨hs₁, hs₂, hs₃⟩ := hs
    rw [hp] at hs₁
    obtain ⟨QA', QB', hp', h₁, h₂⟩ := List.forall₂_append_right_splitCtl hs₁
    have hokp : ResultOk C.toTypeCtx (QA' ++ QB') := hp' ▸ hok.1
    refine ⟨QA', QB', hp', ?_, ?_, .inr (ResultOk.rightRTCtl hokp)⟩
    · rcases hinv with rfl | hQ
      · exact h₂
      · exact ResultSub.trans_okCtl hQ h₂ hQB
    · refine .sub hl ⟨h₁, hs₂, hs₃⟩ ⟨ResultOk.leftRTCtl hokp, hok.2.1, hok.2.2⟩
  | frame _ hok ih =>
    intro A B he
    obtain ⟨QA, QB, hp, hQB, hl, hinv⟩ := ih he
    simp only at hp
    subst hp
    exact ⟨_, QB, (List.append_assoc _ _ _).symm, hQB, .frame hl hok, hinv⟩
  | tail _ hx ht ih =>
    intro A B he
    obtain ⟨QA, QB, hp, hQB, hl, hinv⟩ := ih he
    exact ⟨QA, QB, hp, hQB, .tail hl hx ht, hinv⟩
  | head _ hp hpok hmok hx ih =>
    intro A B he
    obtain ⟨QA, QB, hm, hQB, hl, hinv⟩ := ih he
    simp only at hm
    subst hm
    obtain ⟨pA, pB, rfl, h₁, h₂⟩ := List.forall₂_append_right_splitCtl hp
    refine ⟨pA, pB, rfl, ?_, .head hl h₁ (ResultOk.left hpok) (ResultOk.left hmok) hx,
      .inr (ResultOk.right hpok)⟩
    rcases hinv with rfl | hQ
    · exact h₂
    · exact ResultSub.trans_okCtl (ResultOk.right hmok) h₂ hQB

/-- Appending an empty-sequence typing: the replacement for the empty tail. -/
def BaseRepCtl (C : Context) (t₂ : List CValType) (xs₂ : List Nat) (t₃ : List CValType) : Prop :=
  ∀ (s' : Store H) (out : List Admin) (Q : List CValType),
    AdminsOk s' C out ⟨Q, [], t₂⟩ → AdminsOk s' C out ⟨Q, xs₂, t₃⟩

/-! ## Values -/

theorem AdminOk.val_invRTCtl {s : Store H} {C : Context} {v : Val} {it : InstrType}
    (h : AdminOk s C v.toAdmin it) : ∃ t, it = .plain [] [t] ∧ ValOk s v t := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r
  · cases h with
    | plain h =>
      cases h <;> rename_i h <;> cases h
      exact ⟨_, rfl, .num ⟨.int t, b⟩⟩
  · cases h with
    | plain h =>
      cases h <;> rename_i h <;> cases h
      exact ⟨_, rfl, .num ⟨.float t, b⟩⟩
  · cases h with
    | plain h =>
      cases h <;> rename_i h <;> cases h
      exact ⟨_, rfl, .vec b⟩
  · cases h with
    | ref h => exact ⟨_, rfl, .ref h⟩

theorem SubEqR.trans_valCtl {Δ : TypeCtx} {a b c : CValType} (h₁ : SubEqR Δ a b)
    (h₂ : SubEqR Δ b c) : SubEqR Δ a c := by
  rcases h₁ with rfl | ⟨h₁, hb⟩
  · exact h₂
  rcases h₂ with rfl | ⟨h₂, hc⟩
  · exact .inr ⟨h₁, hb⟩
  exact .inr ⟨Sub.trans_valCtl hb h₁ h₂, hc⟩

theorem SubEqR.sub_right_valCtl {Δ : TypeCtx} {a b c : CValType} (h₁ : SubEqR Δ a b)
    (h₂ : Sub Δ b c) (hc : TyOk Δ c) : SubEqR Δ a c :=
  h₁.trans_valCtl (.inr ⟨h₂, hc⟩)

theorem forall₂_subEqR_resultSubCtl {Δ : TypeCtx} {x y z : List CValType}
    (h₁ : List.Forall₂ (SubEqR Δ) x y) (h₂ : ResultSub Δ y z) : ResultSub Δ x z :=
  forall₂_comp (S := Sub Δ) h₁ h₂ fun _ _ _ _ _ _ hab hbc => by
    rcases hab with rfl | ⟨hab, hb⟩
    · exact hbc
    · exact Sub.trans_valCtl hb hab hbc

theorem forall₂_subEqR_okCtl {Δ : TypeCtx} : ∀ {x y : List CValType},
    List.Forall₂ (SubEqR Δ) x y → ResultOk Δ x → ResultOk Δ y
  | _, _, .nil, _ => fun _ h => by cases h
  | _, _, .cons h t, hx => by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rcases h with rfl | ⟨_, hb⟩
      · exact hx _ (by simp)
      · exact hb
    · exact forall₂_subEqR_okCtl t (fun u hu => hx u (by simp [hu])) c hc

/-- Inversion for a value sequence (no well-formedness of the context needed). -/
theorem AdminsOk.vals_auxPCtl {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → ∀ vs, as = vals vs →
      ResultOk C.toTypeCtx it.params ∧ (∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩) ∧
      ∃ ts, List.Forall₂ (ValOk s) vs ts ∧
        List.Forall₂ (SubEqR C.toTypeCtx) (it.params ++ ts) it.results
  | _, _, _, .nil, vs, e => by
    have : vs = [] := List.map_eq_nil_iff.mp e.symm
    subst this
    exact ⟨by simp [ResultOk], by simp, [], .nil, .nil⟩
  | _, _, _, .single h, vs, e => by
    obtain ⟨v, rfl, hv⟩ := List.map_eq_singleton_iff.mp e.symm
    subst hv
    obtain ⟨t, rfl, hv⟩ := AdminOk.val_invRTCtl h
    refine ⟨by simp [ResultOk], by simp, [t], .cons hv .nil, ?_⟩
    simp only [List.nil_append]
    exact forall₂_self (fun _ => .inl rfl) _
  | C, _, _, .cons ha _ hs, vs, e => by
    obtain ⟨v, vs', rfl, hv, e'⟩ := List.map_eq_cons_iff.mp e.symm
    subst hv
    obtain ⟨_, hi, ts', hv', r⟩ := AdminsOk.vals_auxPCtl hs vs' e'.symm
    obtain ⟨t, hit, hv⟩ := AdminOk.val_invRTCtl ha
    simp only [InstrType.plain, InstrType.mk.injEq] at hit
    obtain ⟨rfl, rfl, rfl⟩ := hit
    have hC0 : C.initLocals [] = C := rfl
    rw [hC0] at hi r
    exact ⟨by simp [ResultOk], by simpa using hi, t :: ts', .cons hv hv', by simpa using r⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, vs, e => by
    obtain ⟨vs₁, vs₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp e.symm
    obtain ⟨p₁, i₁, ts₁, v₁, r₁⟩ := AdminsOk.vals_auxPCtl h₁ vs₁ e₁.symm
    obtain ⟨_, i₂, ts₂, v₂, r₂⟩ := AdminsOk.vals_auxPCtl h₂ vs₂ e₂.symm
    rw [Context.initLocals_of_set i₁] at i₂ r₂
    refine ⟨p₁, ?_, ts₁ ++ ts₂, forall₂_append v₁ v₂, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact i₁ x h
      · exact i₂ x h
    · rw [← List.append_assoc]
      exact forall₂_comp (forall₂_append r₁ (forall₂_self (fun _ => .inl rfl) ts₂)) r₂
        fun _ _ _ _ _ _ hab hbc => hab.trans_valCtl hbc
  | _, _, _, .sub (it := it₀) h hs hok, vs, e => by
    obtain ⟨p, i, ts, hv, r⟩ := AdminsOk.vals_auxPCtl h vs e
    refine ⟨hok.1, fun x hx => ?_, ts, hv, ?_⟩
    · by_cases hx' : x ∈ it₀.inits
      · exact i x hx'
      · exact hs.2.2 x hx hx'
    · have h1 : List.Forall₂ (SubEqR _) _ _ :=
        forall₂_append (forall₂_subEqR_of_sub hs.1 p) (forall₂_self (fun _ => .inl rfl) ts)
      exact forall₂_comp (forall₂_comp h1 r fun _ _ _ _ _ _ hab hbc => hab.trans_valCtl hbc) hs.2.1
        fun _ _ c _ _ hc hab hbc => SubEqR.sub_right_valCtl hab hbc (hok.2.1 c hc)
  | _, _, _, .frame h hok, vs, e => by
    obtain ⟨p, i, ts, hv, r⟩ := AdminsOk.vals_auxPCtl h vs e
    refine ⟨ResultOk.append hok p, i, ts, hv, ?_⟩
    rw [List.append_assoc]
    exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) r

/-! ## Redex inversion -/

/-- Inversion and replacement for `vals vs ++ [a]`, where `a` has only typings
with no initialised locals and at least `N` parameters, `vs.length ≤ N`. -/
theorem redex_inv_auxCtl {s : Store H} {C : Context} {a : Admin} {N : Nat}
    (hI : ∀ it', AdminOk s C a it' → it'.inits = [] ∧ N ≤ it'.params.length) :
    ∀ {C' : Context} {as : List Admin} {it : InstrType}, AdminsOk s C' as it → C' = C →
    ∀ vs : List Val, as = vals vs ++ [a] → vs.length ≤ N →
    ∃ A B t₂ ts xs₂ t₃, AdminOk s C a ⟨A ++ B, [], t₂⟩ ∧ List.Forall₂ (ValOk s) vs ts ∧
      ResultSub C.toTypeCtx ts B ∧ BaseRepCtl (H := H) C t₂ xs₂ t₃ ∧ LiftCtl C ⟨A, xs₂, t₃⟩ it
  | _, _, _, .nil, _, vs, he, _ => by cases vs <;> simp [vals] at he
  | _, _, it, .single ha, hC, vs, he, _ => by
    cases vs with
    | cons v vs => simp [vals] at he
    | nil =>
      subst hC
      simp only [vals, List.map_nil, List.nil_append, List.cons.injEq, and_true] at he
      subst he
      have h0 := (hI _ ha).1
      obtain ⟨p, x, r⟩ := it
      simp only at h0
      subst h0
      exact ⟨p, [], r, [], [], r, by simpa using ha, .nil, .nil, fun _ _ _ h => h, .refl⟩
  | _, _, _, @AdminsOk.cons _ _ C₀ a' as' t₁ t₂ t₃ xs₁ xs₂ ha hx hs, hC, vs, he, hlen => by
    cases vs with
    | nil =>
      subst hC
      simp only [vals, List.map_nil, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hx₁ := (hI _ ha).1
      simp only at hx₁
      subst hx₁
      refine ⟨t₁, [], t₂, [], xs₂, t₃, by simpa using ha, .nil, .nil, ?_, by simpa using LiftCtl.refl⟩
      intro s' out Q hout
      have := AdminsOk.append hout (by simp) (by simpa using AdminsOk.nil_storeCtl s' hs rfl)
      simpa using this
    | cons v vs' =>
      simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at he
      obtain ⟨ha', has'⟩ := he
      obtain ⟨tv, hit, hv⟩ := AdminOk.val_invRTCtl (ha' ▸ ha)
      simp only [InstrType.plain, InstrType.mk.injEq] at hit
      obtain ⟨ht₁, hxs₁, ht₂⟩ := hit
      simp only [List.length_cons] at hlen
      obtain ⟨A', B', t₂', ts', xs₂', t₃', hi, hvs, hB, hrep, hl⟩ :=
        redex_inv_auxCtl hI hs (by rw [hxs₁, hC]; rfl) vs' has' (by omega)
      subst hC ht₁ hxs₁ ht₂
      have hN := (hI _ hi).2
      have hBl := hB.length_eq
      have hvl := hvs.length_eq
      simp only [List.length_append] at hN
      obtain ⟨A, b, rfl⟩ : ∃ A b, A' = A ++ [b] := by
        rcases List.eq_nil_or_concat A' with h | ⟨L, b, h⟩
        · subst h; simp at hN; omega
        · exact ⟨L, b, by simpa using h⟩
      obtain ⟨QA, QB, hp, hQB, hl', -⟩ := hl.dropTopCtl (A := A) (B := [b]) rfl
      have hQBl := hQB.length_eq
      simp only at hp
      obtain ⟨rfl, rfl⟩ : QA = [] ∧ QB = [tv] := by
        have h1 := congrArg List.length hp
        simp only [List.length_append, List.length_cons, List.length_nil] at h1 hQBl
        obtain rfl : QA = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact ⟨rfl, by simpa using hp.symm⟩
      refine ⟨A, b :: B', t₂', tv :: ts', xs₂', t₃', by simpa using hi, .cons hv hvs,
        .cons (by cases hQB; assumption) hB, hrep, by simpa using hl'⟩
  | _, _, _, @AdminsOk.seq _ _ C₀ as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂, hC, vs, he, hlen => by
    rcases List.eq_nil_or_concat as₂ with h0 | ⟨l, x, h0⟩
    · have he' : as₁ = vals vs ++ [a] := by rw [← he, h0, List.append_nil]
      obtain ⟨A, B, t₂', ts, xs₂', t₃', hi, hvs, hB, hrep, hl⟩ :=
        redex_inv_auxCtl hI h₁ hC vs he' hlen
      have ht : ∀ {H' : Type} (s' : Store H'),
          AdminsOk s' (C₀.initLocals xs₁) [] ⟨t₂, xs₂, t₃⟩ :=
        fun s' => AdminsOk.nil_storeCtl s' h₂ h0
      subst hC
      exact ⟨A, B, t₂', ts, xs₂', t₃', hi, hvs, hB, hrep, .tail hl hx ht⟩
    · rw [List.concat_eq_append] at h0
      have he2 : (as₁ ++ l) ++ [x] = vals vs ++ [a] := by
        rw [List.append_assoc, ← h0]; exact he
      obtain ⟨he₁, hxa⟩ := List.append_inj' he2 rfl
      simp only [List.cons.injEq, and_true] at hxa
      obtain ⟨vs₁, vs₂, hvs0, e₁, e₂⟩ := List.map_eq_append_iff.mp he₁.symm
      obtain ⟨p₁, i₁, ts₁, v₁, r₁⟩ := AdminsOk.vals_auxPCtl h₁ vs₁ e₁.symm
      have hC₁ : C₀.initLocals xs₁ = C := by rw [Context.initLocals_of_set i₁, hC]
      have he₂ : as₂ = vals vs₂ ++ [a] := by rw [h0, hxa, ← e₂]; rfl
      have hlen₂ : vs₂.length ≤ N := by
        rw [hvs0] at hlen; simp only [List.length_append] at hlen; omega
      obtain ⟨A₂, B₂, t₂', ts₂, xs₂', t₃', hi, hvs₂, hB₂, hrep, hl⟩ :=
        redex_inv_auxCtl hI h₂ hC₁ vs₂ he₂ hlen₂
      subst hC hvs0
      simp only [List.length_append] at hlen
      have hN := (hI _ hi).2
      have hB₂l := hB₂.length_eq
      have hv₂l := hvs₂.length_eq
      have hv₁l := v₁.length_eq
      simp only [List.length_append] at hN
      obtain ⟨A, B₁, rfl, hB₁l⟩ : ∃ A B₁, A₂ = A ++ B₁ ∧ B₁.length = vs₁.length :=
        ⟨A₂.take (A₂.length - vs₁.length), A₂.drop (A₂.length - vs₁.length),
          (List.take_append_drop _ _).symm, by simp; omega⟩
      obtain ⟨QA, QB, hp, hQB, hl', -⟩ := hl.dropTopCtl (A := A) (B := B₁) rfl
      simp only at hp
      subst hp
      have hQBl := hQB.length_eq
      dsimp only at r₁ p₁ i₁
      obtain ⟨a₁, b₁, hab, ha₁, hb₁⟩ := List.forall₂_append_right_splitCtl r₁
      have ha₁l := ha₁.length_eq
      have hb₁l := hb₁.length_eq
      have htot := congrArg List.length hab
      simp only [List.length_append] at htot
      obtain ⟨rfl, rfl⟩ := List.append_inj hab (by omega)
      refine ⟨A, B₁ ++ B₂, t₂', ts₁ ++ ts₂, xs₂', t₃', by simpa [List.append_assoc] using hi,
        forall₂_append v₁ hvs₂, List.rel_append (forall₂_subEqR_resultSubCtl hb₁ hQB) hB₂, hrep, ?_⟩
      exact .head hl' (ha₁.imp fun _ _ h => h.sub) p₁ (forall₂_subEqR_okCtl ha₁ p₁) i₁
  | _, _, _, .sub h hs hok, hC, vs, he, hlen => by
    obtain ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, hl⟩ := redex_inv_auxCtl hI h hC vs he hlen
    subst hC
    exact ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, .sub hl hs hok⟩
  | _, _, _, .frame h hok, hC, vs, he, hlen => by
    obtain ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, hl⟩ := redex_inv_auxCtl hI h hC vs he hlen
    subst hC
    exact ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, .frame hl hok⟩

/-- **General redex inversion.** For `vals vs ++ [a]`, where every typing of `a`
initialises no locals and has at least `vs.length` parameters: the operands are
typed at (subtypes of) the top `B` of the principal parameters `A ++ B`, and any
code typed at `A → t₂` replaces the redex. -/
theorem redex_inv_genCtl {s : Store H} {C : Context} {a : Admin} {vs : List Val} {it : InstrType}
    (hI : ∀ it', AdminOk s C a it' → it'.inits = [] ∧ vs.length ≤ it'.params.length)
    (h : AdminsOk s C (vals vs ++ [a]) it) :
    ∃ A B t₂ ts, AdminOk s C a ⟨A ++ B, [], t₂⟩ ∧ List.Forall₂ (ValOk s) vs ts ∧
      ResultSub C.toTypeCtx ts B ∧
      ∀ (s' : Store H) (out : List Admin), AdminsOk s' C out ⟨A, [], t₂⟩ →
        AdminsOk s' C out it := by
  obtain ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, hl⟩ :=
    redex_inv_auxCtl hI h rfl vs rfl le_rfl
  exact ⟨A, B, t₂, ts, hi, hvs, hB, fun s' out hout => hl.apply (hrep s' out A hout)⟩

/-- **Redex inversion.** For a redex whose value count is the instruction's
arity: the operands are typed at (subtypes of) the principal parameters, and any
code typed at `[] → t₂` replaces the redex. -/
theorem redex_invCtl {s : Store H} {C : Context} {i : Instr} {vs : List Val} {it : InstrType}
    (hI : ∀ it', InstrOk C i it' → it'.inits = [] ∧ it'.params.length = vs.length)
    (h : AdminsOk s C (vals vs ++ [.plain i]) it) :
    ∃ t₁ t₂ ts, InstrOk C i ⟨t₁, [], t₂⟩ ∧ List.Forall₂ (ValOk s) vs ts ∧
      ResultSub C.toTypeCtx ts t₁ ∧
      ∀ (s' : Store H) (out : List Admin), AdminsOk s' C out ⟨[], [], t₂⟩ → AdminsOk s' C out it := by
  have hI' : ∀ it', AdminOk s C (.plain i) it' →
      it'.inits = [] ∧ vs.length ≤ it'.params.length := by
    intro it' h'
    have h' := h'.plain_inv_arity (fun it hi => (hI it hi).2)
    exact ⟨(hI _ h').1, (hI _ h').2.ge⟩
  obtain ⟨A, B, t₂, ts, hi, hvs, hB, hrep⟩ := redex_inv_genCtl hI' h
  have hi' : InstrOk C i ⟨A ++ B, [], t₂⟩ := hi.plain_inv_arity (fun it hi => (hI it hi).2)
  have hN := (hI _ hi').2
  have hBl := hB.length_eq
  have hvl := hvs.length_eq
  simp only [List.length_append] at hN
  obtain rfl : A = [] := List.eq_nil_of_length_eq_zero (by omega)
  exact ⟨B, t₂, ts, by simpa using hi', hvs, hB, hrep⟩

/-! ## Typing replacement code -/

theorem AdminsOk.trap_singleCtl {s : Store H} {C : Context} {t₂ : List CValType}
    (hok : ResultOk C.toTypeCtx t₂) : AdminsOk s C [.trap] (.plain [] t₂) :=
  AdminsOk.single (.trap ⟨by simp [ResultOk], hok, by simp⟩)

theorem AdminsOk.val_singleCtl {s : Store H} {C : Context} {v : Val} {t : CValType}
    (hv : ValOk s v t) : AdminsOk s C [v.toAdmin] (.plain [] [t]) :=
  AdminsOk.single (AdminOk.toAdmin_ok hv)

/-- A single value, subsumed to a well-formed type. -/
theorem AdminsOk.val_subCtl {s : Store H} {C : Context} {v : Val} {t t' : CValType}
    (hv : ValOk s v t) (hs : Sub C.toTypeCtx t t') (hok : TyOk C.toTypeCtx t') :
    AdminsOk s C [v.toAdmin] (.plain [] [t']) :=
  .sub (AdminsOk.val_singleCtl hv) ⟨.nil, .cons hs .nil, by simp⟩
    ⟨by simp [ResultOk], by simpa [ResultOk] using hok, by simp⟩

theorem ValOk.i32Ctl {s : Store H} (b : BitVec 32) : ValOk s (Val.i32 b) Ty.i32 := .num _

theorem AdminsOk.constI32Ctl {s : Store H} {C : Context} (b : BitVec 32) :
    AdminsOk s C [Core.constI32 b] (.plain [] [Ty.i32]) :=
  AdminsOk.val_singleCtl (ValOk.i32Ctl b)



/-! ## Principal types of references (duplicated from `RefTyping.lean`, suffix `Ctl`) -/

/-- The non-subsumption rules of `Ref_ok`. -/
inductive RefBaseCtl (s : Store H) : Ref → CRefType → Prop where
  | null : RefBaseCtl s .null (.ref true .bot)
  | i31 (b : BitVec 31) : RefBaseCtl s (.i31 b) (.ref false (.abs .i31))
  | struct {a : Nat} {si : StructInst} (h : s.structs[a]? = some si) :
      RefBaseCtl s (.struct a) (.ref false (.defHeap si.type))
  | array {a : Nat} {ai : ArrayInst} (h : s.arrays[a]? = some ai) :
      RefBaseCtl s (.array a) (.ref false (.defHeap ai.type))
  | func {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
      RefBaseCtl s (.func a) (.ref false (.defHeap fi.type))
  | exn {a : Nat} {e : ExnInst} (h : s.exns[a]? = some e) :
      RefBaseCtl s (.exn a) (.ref false (.abs .exn))
  | host (a : Nat) : RefBaseCtl s (.host a) (.ref false (.abs .any))
  | extern {r : Ref} (h : RefOk s r (.ref false (.abs .any))) (hn : r ≠ .null) :
      RefBaseCtl s (.extern r) (.ref false (.abs .extern))

theorem RefBaseCtl.refOk {s : Store H} {r : Ref} {rt : CRefType} (h : RefBaseCtl s r rt) :
    RefOk s r rt := by
  cases h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h => exact .func h
  | exn h => exact .exn h
  | host a => exact .host a
  | extern h hn => exact .extern h hn

theorem RefBaseCtl.nonnull {s : Store H} {r : Ref} {n : Bool} {h : CHeapType}
    (hb : RefBaseCtl s r (.ref n h)) (hr : r ≠ .null) : n = false := by
  cases hb <;> first | rfl | exact absurd rfl hr

theorem RefOk.principalCtl {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    ∃ rt₀, RefBaseCtl s r rt₀ ∧ (rt₀ = rt ∨ (Sub {} rt₀ rt ∧ TyOk {} rt)) := by
  induction h with
  | null => exact ⟨_, .null, .inl rfl⟩
  | i31 b => exact ⟨_, .i31 b, .inl rfl⟩
  | struct h => exact ⟨_, .struct h, .inl rfl⟩
  | array h => exact ⟨_, .array h, .inl rfl⟩
  | func h => exact ⟨_, .func h, .inl rfl⟩
  | exn h => exact ⟨_, .exn h, .inl rfl⟩
  | host a => exact ⟨_, .host a, .inl rfl⟩
  | extern h hn => exact ⟨_, .extern h hn, .inl rfl⟩
  | sub _ hok hs ih =>
    obtain ⟨rt₀, hb, h0⟩ := ih
    rcases h0 with rfl | ⟨hs0, hok0⟩
    · exact ⟨_, hb, .inr ⟨hs, hok⟩⟩
    · exact ⟨_, hb, .inr ⟨Sub.trans_refCtl hok0 hs0 hs, hok⟩⟩

theorem Sub.ref_invCtl {Δ : TypeCtx} {n₁ n₂ : Bool} {h₁ h₂ : CHeapType}
    (h : Sub Δ (Ty.ref n₁ h₁) (Ty.ref n₂ h₂)) : Sub Δ h₁ h₂ ∧ (n₁ = true → n₂ = true) := by
  cases h with
  | refNonNull h => exact ⟨h, by simp⟩
  | refNull h => exact ⟨h, by simp⟩

theorem RefOk.nonnull_subCtl {s : Store H} {r : Ref} {n : Bool} {h : CHeapType}
    (hr : RefOk s r (.ref n h)) (hn : r ≠ .null) : RefOk s r (.ref false h) := by
  obtain ⟨rt₀, hb, h0⟩ := hr.principalCtl
  rcases h0 with h0 | ⟨hs0, hok0⟩
  · subst h0; rw [hb.nonnull hn] at hb; exact hb.refOk
  · cases rt₀ with
    | ref n₀ h₀ =>
      have hn₀ := hb.nonnull hn; subst hn₀
      cases hok0 with
      | ref hh => exact .sub hb.refOk (.ref hh) (.refNonNull (Sub.ref_invCtl hs0).1)

/-! ## Control helpers -/

theorem forall₂_split_leftCtl {α β : Type _} {R : α → β → Prop} {a b : List α} {l : List β}
    (h : List.Forall₂ R (a ++ b) l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R a l₁ ∧ List.Forall₂ R b l₂ := by
  refine ⟨l.take a.length, l.drop a.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · have := List.forall₂_take a.length h; simpa using this
  · have := List.forall₂_drop a.length h; simpa using this

theorem Context.Wf.withLabelCtl {C : Context} (hC : C.Wf) {ts : List CValType}
    (h : ResultOk C.toTypeCtx ts) : (C.withLabel ts).Wf := by
  refine ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, hC.locals, ?_, hC.return_, hC.elems⟩
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact h
  · exact hC.labels t ht

/-- Values typed at well-formed supertypes of their types. -/
theorem AdminsOk.vals_toCtl {s : Store H} {C : Context} {vs : List Val} {ts : List CValType}
    (hv : List.Forall₂ (ValOk s) vs ts) :
    ∀ {us : List CValType}, ResultSub C.toTypeCtx ts us → ResultOk C.toTypeCtx us →
    AdminsOk s C (vals vs) (.plain [] us) := by
  induction hv with
  | nil => intro us hs _; cases hs; exact .nil
  | @cons v t vs ts hv _ ih =>
    intro us hs hok
    cases hs with
    | @cons _ u _ us hs hss =>
      have hu : TyOk C.toTypeCtx u := hok u (by simp)
      have h1 : AdminsOk s C [v.toAdmin] (.plain [] [u]) := AdminsOk.val_subCtl hv hs hu
      have h2 : AdminsOk s C (vals vs) (.plain [] us) :=
        ih hss (fun x hx => hok x (by simp [hx]))
      have h3 : AdminsOk s C (vals vs) ⟨[u] ++ [], [], [u] ++ us⟩ :=
        .frame h2 (by simpa using hu)
      have := AdminsOk.seq h1 (by simp) (by simpa using h3)
      simpa [vals] using this

/-- Source code has well-formed instruction types in a well-formed context. -/
theorem AdminsOk.expr_okCtl {s : Store H} {C : Context} {is : List Instr} {it : InstrType}
    (hC : C.Wf) (h : AdminsOk s C (expression is) it) : InstrTypeOk C it :=
  AdminsOk.instrTypeOk_of_plain hC h (by simp [expression])

/-- A value sequence typed with initialised locals is also typed without them,
in any context with the same type context. -/
theorem AdminsOk.vals_noinitCtl {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it →
    ∀ vs, as = vals vs → ∀ C' : Context, C'.toTypeCtx = C.toTypeCtx →
      AdminsOk s C' (vals vs) ⟨it.params, [], it.results⟩
  | _, _, _, .nil, vs, e, _, _ => by
    have : vs = [] := List.map_eq_nil_iff.mp e.symm
    subst this; exact .nil
  | _, _, _, .single h, vs, e, C', _ => by
    obtain ⟨v, rfl, hv⟩ := List.map_eq_singleton_iff.mp e.symm
    subst hv
    obtain ⟨hp, t, hv, hr⟩ := AdminOk.toAdmin_inv h
    rw [hp, hr]
    exact .single (AdminOk.toAdmin_ok hv)
  | _, _, _, .cons ha _ hs, vs, e, C', hC' => by
    obtain ⟨v, vs', rfl, hv, e'⟩ := List.map_eq_cons_iff.mp e.symm
    subst hv
    obtain ⟨hp, t, hv, hr⟩ := AdminOk.toAdmin_inv ha
    have ih := AdminsOk.vals_noinitCtl hs vs' e'.symm C' (by rw [hC']; simp)
    simp only at hp hr ih ⊢
    subst hp hr
    have := AdminsOk.cons (xs₁ := []) (AdminOk.toAdmin_ok (C := C') hv) (by simp) (by simpa using ih)
    simpa [vals] using this
  | _, _, _, .seq h₁ _ h₂, vs, e, C', hC' => by
    obtain ⟨vs₁, vs₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp e.symm
    have ih₁ := AdminsOk.vals_noinitCtl h₁ vs₁ e₁.symm C' hC'
    have ih₂ := AdminsOk.vals_noinitCtl h₂ vs₂ e₂.symm C' (by rw [hC']; simp)
    have := AdminsOk.seq ih₁ (by simp) (by simpa using ih₂)
    simpa using this
  | _, _, _, .sub h hs hok, vs, e, C', hC' => by
    have ih := AdminsOk.vals_noinitCtl h vs e C' hC'
    refine .sub ih ⟨?_, ?_, by simp⟩ ⟨?_, ?_, by simp⟩
    · rw [hC']; exact hs.1
    · rw [hC']; exact hs.2.1
    · rw [hC']; exact hok.1
    · rw [hC']; exact hok.2.1
  | _, _, _, .frame h hok, vs, e, C', hC' => by
    have ih := AdminsOk.vals_noinitCtl h vs e C' hC'
    exact .frame ih (by rw [hC']; exact hok)

/-- A single administrative instruction with inits-free typings: its principal
typing, and replacement at that typing. -/
theorem single_repCtl {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    (hI : ∀ it', AdminOk s C a it' → it'.inits = []) (h : AdminsOk s C [a] it) :
    ∃ A t₂, AdminOk s C a ⟨A, [], t₂⟩ ∧
      ∀ (s' : Store H) (out : List Admin), AdminsOk s' C out ⟨A, [], t₂⟩ →
        AdminsOk s' C out it := by
  obtain ⟨A, B, t₂, ts, hi, hvs, hB, hrep⟩ :=
    redex_inv_genCtl (vs := []) (fun it' h' => ⟨hI it' h', by simp⟩) (by simpa [vals] using h)
  cases hvs
  cases hB
  exact ⟨A, t₂, by simpa using hi, hrep⟩

/-- Replacement of a single administrative instruction at a typing with
well-formed results: code typed at `it.params → it.results` replaces it. -/
theorem single_at_itCtl {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    {out : List Admin} (hC : C.Wf) (hr : ResultOk C.toTypeCtx it.results)
    (hI : ∀ it', AdminOk s C a it' → it'.inits = []) (h : AdminsOk s C [a] it)
    (hout : AdminsOk s C out ⟨it.params, [], it.results⟩) : AdminsOk s C out it := by
  obtain ⟨ts, it₀, ha, -, -, hi⟩ := AdminsOk.single_aux h a rfl hC.types
  have hp := AdminsOk.params_ok hC h
  exact .sub hout ⟨ResultSub.refl _ _, ResultSub.refl _ _,
    fun x hx _ => hi x hx (by rw [hI _ ha]; simp)⟩ ⟨hp.1, hr, hp.2⟩

theorem AdminOk.label_invCtl {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {body : List Admin} {it : InstrType} (h : AdminOk s C (.label n cont body) it) :
    it.params = [] ∧ it.inits = [] ∧ ∃ t' xs' xs, t'.length = n ∧
      AdminsOk s C (expression cont) ⟨t', xs', it.results⟩ ∧
      AdminsOk s (C.withLabel t') body ⟨[], xs, it.results⟩ := by
  cases h with
  | label hn hc hb => exact ⟨rfl, rfl, _, _, _, hn, hc, hb⟩

theorem AdminOk.handler_invCtl {s : Store H} {C : Context} {n : Nat} {cs : List Catch}
    {body : List Admin} {it : InstrType} (h : AdminOk s C (.handler n cs body) it) :
    it.params = [] ∧ it.inits = [] ∧ (∀ c ∈ cs, CatchOk C c) ∧ ∃ xs,
      AdminsOk s C body ⟨[], xs, it.results⟩ := by
  cases h with
  | handler hc hb => exact ⟨rfl, rfl, hc, _, hb⟩

theorem AdminOk.frame_invCtl {s : Store H} {C : Context} {n : Nat} {fr : Frame}
    {body : List Admin} {it : InstrType} (h : AdminOk s C (.frame n fr body) it) :
    it.params = [] ∧ it.inits = [] ∧ ∃ C', FrameOk s fr C' ∧ it.results.length = n ∧
      AdminsOk s { C' with return_ := some it.results } body (.plain [] it.results) ∧
      ResultOk {} it.results := by
  cases h with
  | frame hf hn hb hok => exact ⟨rfl, rfl, _, hf, hn, hb, hok⟩

theorem AdminOk.label_initsCtl {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {body : List Admin} : ∀ it', AdminOk s C (.label n cont body) it' → it'.inits = [] :=
  fun _ h => (AdminOk.label_invCtl h).2.1

theorem AdminOk.handler_initsCtl {s : Store H} {C : Context} {n : Nat} {cs : List Catch}
    {body : List Admin} : ∀ it', AdminOk s C (.handler n cs body) it' → it'.inits = [] :=
  fun _ h => (AdminOk.handler_invCtl h).2.1

theorem AdminOk.frame_initsCtl {s : Store H} {C : Context} {n : Nat} {fr : Frame}
    {body : List Admin} : ∀ it', AdminOk s C (.frame n fr body) it' → it'.inits = [] :=
  fun _ h => (AdminOk.frame_invCtl h).2.1

/-- Inversion of a value prefix: the values are typed below a well-formed stack
type `m`, from which the rest continues. -/
theorem vals_head_invCtl {s : Store H} {C : Context} {vs : List Val} {as : List Admin}
    {xs : List Nat} {r : List CValType} (hC : C.Wf) (hne : as ≠ [])
    (h : AdminsOk s C (vals vs ++ as) ⟨[], xs, r⟩) :
    ∃ m x₂ tv, ResultOk C.toTypeCtx m ∧ List.Forall₂ (ValOk s) vs tv ∧
      ResultSub C.toTypeCtx tv m ∧ AdminsOk s C as ⟨m, x₂, r⟩ := by
  obtain ⟨m, xs₁, xs₂, h₁, h₂, -⟩ := AdminsOk.split h hC (vals vs) as rfl hne
  obtain ⟨-, hi, tv, hv, hr⟩ := AdminsOk.vals_auxPCtl h₁ vs rfl
  have hC₁ : C.initLocals xs₁ = C := Context.initLocals_of_set hi
  rw [hC₁] at h₂
  have hm := (AdminsOk.params_ok hC h₂).1
  refine ⟨m, xs₂, tv, hm, hv, ?_, h₂⟩
  have : List.Forall₂ (SubEqR C.toTypeCtx) tv m := by simpa using hr
  exact this.imp fun _ _ h => h.sub

/-- Inversion of the head of a nonempty sequence. -/
theorem head_invCtl {s : Store H} {C : Context} {a : Admin} {rest : List Admin} {it : InstrType}
    (hC : C.Wf) (h : AdminsOk s C (a :: rest) it) :
    ∃ F it₀, AdminOk s C a it₀ ∧ ResultSub C.toTypeCtx it.params (F ++ it₀.params) := by
  have h1 : ∃ it₁ : InstrType, AdminsOk s C [a] it₁ ∧ it₁.params = it.params := by
    by_cases hr : rest = []
    · subst hr; exact ⟨it, h, rfl⟩
    · obtain ⟨t₂, xs₁, xs₂, h₁, -, -⟩ := AdminsOk.split h hC [a] rest rfl hr
      exact ⟨_, h₁, rfl⟩
  obtain ⟨it₁, h₁, hp⟩ := h1
  obtain ⟨F, it₀, ha, hs⟩ := AdminsOk.single_inv hC.types h₁
  exact ⟨F, it₀, ha, hp ▸ hs.1⟩

/-- Inversion of `val* a instr*`. -/
theorem vals_admin_invCtl {s : Store H} {C : Context} {vs : List Val} {a : Admin}
    {rest : List Admin} {xs : List Nat} {r : List CValType} (hC : C.Wf)
    (h : AdminsOk s C (vals vs ++ [a] ++ rest) ⟨[], xs, r⟩) :
    ∃ m tv F it₀, ResultOk C.toTypeCtx m ∧ List.Forall₂ (ValOk s) vs tv ∧
      ResultSub C.toTypeCtx tv m ∧ AdminOk s C a it₀ ∧
      ResultSub C.toTypeCtx m (F ++ it₀.params) := by
  have h' : AdminsOk s C (vals vs ++ (a :: rest)) ⟨[], xs, r⟩ := by simpa using h
  obtain ⟨m, x₂, tv, hm, hv, hs, h₂⟩ := vals_head_invCtl hC (by simp) h'
  obtain ⟨F, it₀, ha, hsub⟩ := head_invCtl hC h₂
  exact ⟨m, tv, F, it₀, hm, hv, hs, ha, hsub⟩

theorem AdminOk.br_invCtl {s : Store H} {C : Context} {l : LabelIdx} {it₀ : InstrType}
    (h : AdminOk s C (.plain (.br l)) it₀) :
    ∃ lt t₁, C.labels[l.toNat]? = some lt ∧ it₀.params = t₁ ++ lt := by
  cases h with
  | plain h =>
    cases h with
    | br hl _ => exact ⟨_, _, hl, rfl⟩
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h

theorem AdminOk.return_invCtl {s : Store H} {C : Context} {it₀ : InstrType}
    (h : AdminOk s C (.plain .return_) it₀) :
    ∃ lt t₁, C.return_ = some lt ∧ it₀.params = t₁ ++ lt := by
  cases h with
  | plain h =>
    cases h with
    | return_ hr _ => exact ⟨_, _, hr, rfl⟩
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h

/-- The operands of a branch: the last `|lt|` values are typed below `lt`. -/
theorem suffix_subCtl {Δ : TypeCtx} (hΔ : Δ.Ok) {s : Store H} {vs₁ vs₂ : List Val}
    {tv m M lt : List CValType} (hm : ResultOk Δ m) (hv : List.Forall₂ (ValOk s) (vs₁ ++ vs₂) tv)
    (h₁ : ResultSub Δ tv m) (h₂ : ResultSub Δ m (M ++ lt)) (hlen : vs₂.length = lt.length) :
    ∃ tv₂, List.Forall₂ (ValOk s) vs₂ tv₂ ∧ ResultSub Δ tv₂ lt := by
  obtain ⟨m₁, m₂, rfl, -, hm₂⟩ := List.forall₂_append_right_splitCtl h₂
  obtain ⟨c, d, rfl, -, hd⟩ := List.forall₂_append_right_splitCtl h₁
  obtain ⟨e, f, he, -, hvf⟩ := forall₂_split_leftCtl hv
  have l1 := hvf.length_eq
  have l2 := hd.length_eq
  have l3 := hm₂.length_eq
  obtain ⟨-, rfl⟩ := List.append_inj' he (by omega)
  exact ⟨d, hvf, ResultSub.trans hΔ (ResultOk.right hm) hd hm₂⟩

/-- Retyping `val* a` for a stack-polymorphic `a` consuming `lt`. -/
theorem vals_poly_retypeCtl {s : Store H} {C : Context} {vs : List Val} {a : Admin}
    {p tv m M lt r : List CValType} (hp : ResultOk C.toTypeCtx p) (hm : ResultOk C.toTypeCtx m)
    (hr : ResultOk C.toTypeCtx r) (hv : List.Forall₂ (ValOk s) vs tv)
    (h₁ : ResultSub C.toTypeCtx tv m) (h₂ : ResultSub C.toTypeCtx m (M ++ lt))
    (ha : ∀ t₁, ResultOk C.toTypeCtx t₁ → AdminOk s C a (.plain (t₁ ++ lt) r)) :
    AdminsOk s C (vals vs ++ [a]) (.plain p r) := by
  obtain ⟨m₁, m₂, rfl, -, hm₂⟩ := List.forall₂_append_right_splitCtl h₂
  have hpm₁ : ResultOk C.toTypeCtx (p ++ m₁) := ResultOk.append hp (ResultOk.left hm)
  have hA : AdminsOk s C [a] (.plain (p ++ m₁ ++ m₂) r) :=
    .sub (.single (ha _ hpm₁))
      ⟨ResultSub.append (ResultSub.refl _ _) hm₂, ResultSub.refl _ _, by simp⟩
      ⟨by simpa [List.append_assoc] using ResultOk.append hp hm, hr, by simp⟩
  have hV : AdminsOk s C (vals vs) ⟨p ++ [], [], p ++ (m₁ ++ m₂)⟩ :=
    .frame (AdminsOk.vals_toCtl hv h₁ hm) hp
  have := AdminsOk.seq hV (by simp) (by simpa [List.append_assoc] using hA)
  simpa using this

/-! ## Block types -/

theorem blockType_lenCtl {C : Context} {f : Frame} {bt : BlockType}
    {t₁ t₂ t₁' t₂' : List CValType} (ht : C.types = f.module.types) (h : BlockTypeOk C bt t₁ t₂)
    (hbt : f.module.blockType? bt = some (t₁', t₂')) :
    t₁'.length = t₁.length ∧ t₂'.length = t₂.length := by
  cases h with
  | empty =>
    simp only [ModuleInst.blockType?, Option.some.injEq, Prod.mk.injEq] at hbt
    obtain ⟨rfl, rfl⟩ := hbt; simp
  | value _ =>
    simp only [ModuleInst.blockType?, Option.some.injEq, Prod.mk.injEq] at hbt
    obtain ⟨rfl, rfl⟩ := hbt; simp
  | typeIdx hd he =>
    rename_i x d ps rs
    have hd' : f.module.types[x.toNat]? = some d := by
      rw [← ht]; exact hd
    have he' := Expand.iff.1 he
    simp [ModuleInst.blockType?, hd', DefType.funcType?, he'] at hbt
    obtain ⟨rfl, rfl⟩ := hbt; simp

/-- The label of a block: `LABEL_n{} (val* instr*)`, typed at `[] → t₂`. -/
theorem label_blockCtl {s : Store H} {C : Context} {vs : List Val} {tv t₁ t₂ : List CValType}
    {body : List Instr} {xs : List Nat} {n : Nat} (hn : t₂.length = n)
    (ht₁ : ResultOk C.toTypeCtx t₁) (ht₂ : ResultOk C.toTypeCtx t₂)
    (hv : List.Forall₂ (ValOk s) vs tv) (hsub : ResultSub C.toTypeCtx tv t₁)
    (hb : InstrsOk (C.withLabel t₂) body ⟨t₁, xs, t₂⟩) :
    AdminOk s C (.label n [] (vals vs ++ expression body)) (.plain [] t₂) := by
  refine .label (t' := t₂) (xs' := []) (xs := xs) hn (by simpa [expression] using AdminsOk.id (s := s) ht₂) ?_
  have hV : AdminsOk s (C.withLabel t₂) (vals vs) (.plain [] t₁) := AdminsOk.vals_toCtl hv hsub ht₁
  have := AdminsOk.seq hV (by simp) (by simpa using AdminsOk.of_instrsOk (s := s) hb)
  simpa using this

/-! ## Blocks -/

/-- `Step_read/block`. -/
theorem Step.block_presCtl {s : Store H} {C : Context} {f : Frame} {bt : BlockType}
    {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType} {it : InstrType}
    (h : AdminsOk s C (vals vs ++ [.plain (.block bt body)]) it)
    (hC : C.Wf) (ht : C.types = f.module.types)
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
    AdminsOk s C [.label t₂.length [] (vals vs ++ expression body)] it := by
  have hI : ∀ it', AdminOk s C (.plain (.block bt body)) it' →
      it'.inits = [] ∧ vs.length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | block hbt' _ => exact ⟨rfl, by have := (blockType_lenCtl ht hbt' hbt).1; simp; omega⟩
      | parametric h => cases h
      | numeric h => cases h
      | vector h => cases h
      | «variable» h => cases h
      | memory h => cases h
      | table h => cases h
      | reference h => cases h
  obtain ⟨A, B, t₂', tv, hi, hvs, hB, hrep⟩ := redex_inv_genCtl hI h
  cases hi with
  | plain hi =>
    cases hi with
    | block hbt' hb =>
      have hl := blockType_lenCtl ht hbt' hbt
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      simp only [List.length_append] at hl
      obtain rfl : A = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hreg := hbt'.regular hC
      simp only [List.nil_append] at hreg hb
      exact hrep s _ (.single (label_blockCtl (by omega) hreg.1 hreg.2 hvs hB hb))
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h

/-- `Step_read/loop`. -/
theorem Step.loop_presCtl {s : Store H} {C : Context} {f : Frame} {bt : BlockType}
    {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType} {it : InstrType}
    (h : AdminsOk s C (vals vs ++ [.plain (.loop bt body)]) it)
    (hC : C.Wf) (ht : C.types = f.module.types)
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
    AdminsOk s C [.label t₁.length [.loop bt body] (vals vs ++ expression body)] it := by
  have hI : ∀ it', AdminOk s C (.plain (.loop bt body)) it' →
      it'.inits = [] ∧ vs.length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | loop hbt' _ => exact ⟨rfl, by have := (blockType_lenCtl ht hbt' hbt).1; simp; omega⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, B, t₂', tv, hi, hvs, hB, hrep⟩ := redex_inv_genCtl hI h
  cases hi with
  | plain hi =>
    cases hi with
    | loop hbt' hb =>
      have hl := blockType_lenCtl ht hbt' hbt
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      simp only [List.length_append] at hl
      obtain rfl : A = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hreg := hbt'.regular hC
      simp only [List.nil_append] at hreg hb hbt'
      have hV : AdminsOk s (C.withLabel B) (vals vs) (.plain [] B) :=
        AdminsOk.vals_toCtl hvs hB hreg.1
      have hbody := AdminsOk.seq hV (by simp) (AdminsOk.of_instrsOk (s := s) hb)
      exact hrep s _ (.single (.label (t' := B) (xs' := []) (by simp at hl; omega)
        (.single (.plain (.loop hbt' hb))) hbody))
    | _ => rename_i hh; cases hh

/-- Inversion and replacement for `i32.const c; if`. -/
theorem if_invCtl {s : Store H} {C : Context} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} {it : InstrType}
    (h : AdminsOk s C [constI32 c, .plain (.if_ bt b₁ b₂)] it) :
    ∃ t₁ t₂ xs₁ xs₂, BlockTypeOk C bt t₁ t₂ ∧ InstrsOk (C.withLabel t₂) b₁ ⟨t₁, xs₁, t₂⟩ ∧
      InstrsOk (C.withLabel t₂) b₂ ⟨t₁, xs₂, t₂⟩ ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨t₁, [], t₂⟩ → AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.if_ bt b₁ b₂)) it' →
      it'.inits = [] ∧ [Val.i32 c].length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | if_ _ _ _ => exact ⟨rfl, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, B, t₂', tv, hi, hvs, hB, hrep⟩ := redex_inv_genCtl (vs := [Val.i32 c]) hI h
  generalize hP : A ++ B = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | if_ hbt h₁ h₂ =>
      rename_i t₁ _ _
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      obtain ⟨rfl, -⟩ := List.append_inj' hP (by simp at l1 l2 ⊢; omega)
      exact ⟨_, _, _, _, hbt, h₁, h₂, fun out hout => hrep s out hout⟩
    | _ => rename_i hh; cases hh

/-- `Step_pure/if-true`. -/
theorem Step.ifTrue_presCtl {s : Store H} {C : Context} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} {it : InstrType}
    (h : AdminsOk s C [constI32 c, .plain (.if_ bt b₁ b₂)] it) :
    AdminsOk s C [.plain (.block bt b₁)] it := by
  obtain ⟨t₁, t₂, xs₁, xs₂, hbt, h₁, h₂, hrep⟩ := if_invCtl h
  exact hrep _ (.single (.plain (.block hbt h₁)))

/-- `Step_pure/if-false`. -/
theorem Step.ifFalse_presCtl {s : Store H} {C : Context} {bt : BlockType}
    {b₁ b₂ : List Instr} {it : InstrType}
    (h : AdminsOk s C [constI32 0, .plain (.if_ bt b₁ b₂)] it) :
    AdminsOk s C [.plain (.block bt b₂)] it := by
  obtain ⟨t₁, t₂, xs₁, xs₂, hbt, h₁, h₂, hrep⟩ := if_invCtl h
  exact hrep _ (.single (.plain (.block hbt h₂)))

/-- `Step_pure/label-vals`. -/
theorem Step.labelVals_presCtl {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {vs : List Val} {it : InstrType}
    (h : AdminsOk s C [.label n cont (vals vs)] it) : AdminsOk s C (vals vs) it := by
  obtain ⟨A, t₂, ha, hrep⟩ := single_repCtl AdminOk.label_initsCtl h
  obtain ⟨hA, -, t', xs', xs, -, -, hb⟩ := AdminOk.label_invCtl ha
  simp only at hA hb
  subst hA
  exact hrep s _ (AdminsOk.vals_noinitCtl hb vs rfl C rfl)

/-- `Step_pure/handler-vals`. -/
theorem Step.handlerVals_presCtl {s : Store H} {C : Context} {n : Nat} {cs : List Catch}
    {vs : List Val} {it : InstrType}
    (h : AdminsOk s C [.handler n cs (vals vs)] it) : AdminsOk s C (vals vs) it := by
  obtain ⟨A, t₂, ha, hrep⟩ := single_repCtl AdminOk.handler_initsCtl h
  obtain ⟨hA, -, -, xs, hb⟩ := AdminOk.handler_invCtl ha
  simp only at hA hb
  subst hA
  exact hrep s _ (AdminsOk.vals_noinitCtl hb vs rfl C rfl)

/-- `Step_read/try_table`. -/
theorem Step.tryTable_presCtl {s : Store H} {C : Context} {f : Frame} {bt : BlockType}
    {cs : List Catch} {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType}
    {it : InstrType}
    (h : AdminsOk s C (vals vs ++ [.plain (.tryTable bt cs body)]) it)
    (hC : C.Wf) (ht : C.types = f.module.types)
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
    AdminsOk s C [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]] it := by
  have hI : ∀ it', AdminOk s C (.plain (.tryTable bt cs body)) it' →
      it'.inits = [] ∧ vs.length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | tryTable hbt' _ _ => exact ⟨rfl, by have := (blockType_lenCtl ht hbt' hbt).1; simp; omega⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, B, t₂', tv, hi, hvs, hB, hrep⟩ := redex_inv_genCtl hI h
  cases hi with
  | plain hi =>
    cases hi with
    | tryTable hbt' hb hc =>
      have hl := blockType_lenCtl ht hbt' hbt
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      simp only [List.length_append] at hl
      obtain rfl : A = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hreg := hbt'.regular hC
      simp only [List.nil_append] at hreg hb
      exact hrep s _ (.single (.handler (xs := []) hc
        (.single (label_blockCtl (by omega) hreg.1 hreg.2 hvs hB hb))))
    | _ => rename_i hh; cases hh

/-! ## Conditional branches -/

/-- Inversion and replacement for `i32.const c; br_if l`. -/
theorem brIf_invCtl {s : Store H} {C : Context} {c : BitVec 32} {l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [constI32 c, .plain (.brIf l)] it) :
    ∃ ts, C.labels[l.toNat]? = some ts ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨ts, [], ts⟩ → AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brIf l)) it' →
      it'.inits = [] ∧ [Val.i32 c].length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brIf _ => exact ⟨rfl, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, B, t₂', tv, hi, hvs, hB, hrep⟩ := redex_inv_genCtl (vs := [Val.i32 c]) hI h
  generalize hP : A ++ B = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brIf hl =>
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      obtain ⟨rfl, -⟩ := List.append_inj' hP (by simp at l1 l2 ⊢; omega)
      exact ⟨_, hl, fun out hout => hrep s out hout⟩
    | _ => rename_i hh; cases hh

/-- `Step_pure/br_if-true`. -/
theorem Step.brIfTrue_presCtl {s : Store H} {C : Context} {c : BitVec 32} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [constI32 c, .plain (.brIf l)] it) (hC : C.Wf) :
    AdminsOk s C [.plain (.br l)] it := by
  obtain ⟨ts, hl, hrep⟩ := brIf_invCtl h
  have hts := hC.label hl
  exact hrep _ (.single (.plain (by simpa using InstrOk.br (t₁ := []) hl ⟨by simp, hts, by simp⟩)))

/-- `Step_pure/br_if-false`. -/
theorem Step.brIfFalse_presCtl {s : Store H} {C : Context} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [constI32 0, .plain (.brIf l)] it) (hC : C.Wf) :
    AdminsOk s C [] it := by
  obtain ⟨ts, hl, hrep⟩ := brIf_invCtl h
  exact hrep _ (AdminsOk.id (hC.label hl))

/-- Inversion and replacement for `i32.const i; br_table ls l'`. -/
theorem brTable_invCtl {s : Store H} {C : Context} {i : BitVec 32} {ls : List LabelIdx}
    {l' : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [constI32 i, .plain (.brTable ls l')] it) :
    ∃ ts t₁ t₂, (∀ l ∈ ls, ∃ lt, C.labels[l.toNat]? = some lt ∧ ResultSub C.toTypeCtx ts lt) ∧
      (∃ lt, C.labels[l'.toNat]? = some lt ∧ ResultSub C.toTypeCtx ts lt) ∧
      InstrTypeOk C (.plain (t₁ ++ ts ++ [.i32]) t₂) ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨t₁ ++ ts, [], t₂⟩ → AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brTable ls l')) it' →
      it'.inits = [] ∧ [Val.i32 i].length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brTable _ _ _ => exact ⟨rfl, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, B, t₂', tv, hi, hvs, hB, hrep⟩ := redex_inv_genCtl (vs := [Val.i32 i]) hI h
  generalize hP : A ++ B = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brTable hls hl' hok =>
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      obtain ⟨rfl, -⟩ := List.append_inj' hP (by simp at l1 l2 ⊢; omega)
      exact ⟨_, _, _, hls, hl', hok, fun out hout => hrep s out hout⟩
    | _ => rename_i hh; cases hh

/-- `br l` typed at `t₁ ++ ts → t₂` when `ts` is below the label type. -/
theorem br_subCtl {s : Store H} {C : Context} {l : LabelIdx} {ts lt t₁ t₂ : List CValType}
    (hl : C.labels[l.toNat]? = some lt) (hs : ResultSub C.toTypeCtx ts lt)
    (hok : InstrTypeOk C (.plain (t₁ ++ ts) t₂)) :
    AdminsOk s C [.plain (.br l)] (.plain (t₁ ++ ts) t₂) := by
  have hok₁ : ResultOk C.toTypeCtx t₁ := ResultOk.left hok.1
  exact .sub (.single (.plain (.br hl ⟨hok₁, hok.2.1, by simp⟩)))
    ⟨ResultSub.append (ResultSub.refl _ _) hs, ResultSub.refl _ _, by simp⟩ hok

/-- `Step_pure/br_table-lt`. -/
theorem Step.brTableLt_presCtl {s : Store H} {C : Context} {i : BitVec 32} {ls : List LabelIdx}
    {l' l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [constI32 i, .plain (.brTable ls l')] it)
    (hi : ls[i.toNat]? = some l) : AdminsOk s C [.plain (.br l)] it := by
  obtain ⟨ts, t₁, t₂, hls, -, hok, hrep⟩ := brTable_invCtl h
  obtain ⟨lt, hl, hs⟩ := hls l (List.mem_of_getElem? hi)
  refine hrep _ (br_subCtl hl hs ⟨?_, hok.2.1, by simp⟩)
  have := hok.1
  simp only [ResultOk.append_iff] at this ⊢
  exact ⟨this.1.1, this.1.2⟩

/-- `Step_pure/br_table-ge`. -/
theorem Step.brTableGe_presCtl {s : Store H} {C : Context} {i : BitVec 32} {ls : List LabelIdx}
    {l' : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [constI32 i, .plain (.brTable ls l')] it) :
    AdminsOk s C [.plain (.br l')] it := by
  obtain ⟨ts, t₁, t₂, -, ⟨lt, hl, hs⟩, hok, hrep⟩ := brTable_invCtl h
  refine hrep _ (br_subCtl hl hs ⟨?_, hok.2.1, by simp⟩)
  have := hok.1
  simp only [ResultOk.append_iff] at this ⊢
  exact ⟨this.1.1, this.1.2⟩

/-! ## Reference branches -/

theorem forall₂_singleton_invCtl {α β : Type _} {R : α → β → Prop} {a : α} {l : List β}
    (h : List.Forall₂ R [a] l) : ∃ b, l = [b] ∧ R a b := by
  cases h with
  | cons h t => cases t; exact ⟨_, rfl, h⟩

/-- Inversion and replacement for `val instr` where `instr` has typings
`ts ++ [p] → r` only. -/
theorem redex1_invCtl {s : Store H} {C : Context} {v : Val} {a : Admin} {it : InstrType}
    (hI : ∀ it', AdminOk s C a it' → it'.inits = [] ∧ 1 ≤ it'.params.length)
    (h : AdminsOk s C [v.toAdmin, a] it) :
    ∃ A b t₂ t, AdminOk s C a ⟨A ++ [b], [], t₂⟩ ∧ ValOk s v t ∧ Sub C.toTypeCtx t b ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨A, [], t₂⟩ → AdminsOk s C out it := by
  obtain ⟨A, B, t₂, tv, hi, hvs, hB, hrep⟩ :=
    redex_inv_genCtl (vs := [v]) (fun it' h' => ⟨(hI it' h').1, by simpa using (hI it' h').2⟩) h
  obtain ⟨t, rfl, hv⟩ := forall₂_singleton_invCtl hvs
  obtain ⟨b, rfl, hs⟩ := forall₂_singleton_invCtl hB
  exact ⟨A, b, t₂, t, hi, hv, hs, fun out hout => hrep s out hout⟩

theorem append_single_invCtl {A ts : List CValType} {b c : CValType} (h : A ++ [b] = ts ++ [c]) :
    A = ts ∧ b = c := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  exact ⟨h1, by simpa using h2⟩

/-- A non-null value typed below `ref n ht` is typed at `ref n' ht` for any `n'`. -/
theorem nonnull_valCtl {s : Store H} {C : Context} {v : Val} {t : CValType} {n n' : Bool}
    {ht : CHeapType} (hv : ValOk s v t) (hs : Sub C.toTypeCtx t (Ty.refT n ht))
    (hn : v ≠ .ref .null) (hok : TyOk C.toTypeCtx (Ty.refT n' ht)) :
    AdminsOk s C [v.toAdmin] (.plain [] [Ty.refT n' ht]) := by
  unfold Ty.refT at hs hok ⊢
  cases hv with
  | num v => cases hs
  | vec b => cases hs
  | @ref r rt hr =>
    cases hs with
    | refv hs' =>
      obtain ⟨n₀, h₀⟩ := rt
      have hr' := RefOk.nonnull_subCtl hr (fun e => hn (by rw [e]))
      refine AdminsOk.val_subCtl (.ref hr') (.refv ?_) hok
      have hh := (Sub.ref_invCtl hs').1
      cases n' with
      | false => exact .refNonNull hh
      | true => exact .refNull hh

/-- A reference typed below `c₁` and not of type `c₂` has type `c₁ \ c₂`. -/
theorem ref_diffCtl {s : Store H} {Δ : TypeCtx} {r : Ref} {t : CValType} {c₁ c₂ : CRefType}
    (hv : ValOk s (.ref r) t) (hs : Sub Δ t (.refv c₁)) (hn : ¬ RefOk s r c₂)
    (h₂ok : TyOk {} c₂) :
    ∃ t', ValOk s (.ref r) t' ∧ Sub Δ t' (.refv (Ty.diffrt c₁ c₂)) := by
  cases hv with
  | @ref _ rt hr =>
    cases hs with
    | refv hs' =>
      cases c₁ with | ref n₁ h₁ =>
      cases c₂ with | ref n₂ h₂ =>
      cases n₂ with
      | false => exact ⟨_, .ref hr, .refv hs'⟩
      | true =>
        have hne : r ≠ .null := by
          rintro rfl
          exact hn (.sub .null h₂ok (.refNull .bot))
        obtain ⟨n₀, h₀⟩ := rt
        exact ⟨_, .ref (RefOk.nonnull_subCtl hr hne), .refv (.refNonNull (Sub.ref_invCtl hs').1)⟩

theorem brOnNull_invCtl {s : Store H} {C : Context} {v : Val} {l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [v.toAdmin, .plain (.brOnNull l)] it) :
    ∃ ts ht t, C.labels[l.toNat]? = some ts ∧ TyOk C.toTypeCtx ht ∧ ValOk s v t ∧
      Sub C.toTypeCtx t (Ty.refT true ht) ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨ts, [], ts ++ [Ty.refT false ht]⟩ →
        AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brOnNull l)) it' →
      it'.inits = [] ∧ 1 ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brOnNull _ _ => exact ⟨rfl, by simp⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, b, t₂, t, hi, hv, hs, hrep⟩ := redex1_invCtl hI h
  generalize hP : A ++ [b] = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brOnNull hl hh =>
      obtain ⟨rfl, rfl⟩ := append_single_invCtl hP
      exact ⟨_, _, _, hl, hh, hv, hs, hrep⟩
    | _ => rename_i hh; cases hh

/-- `Step_pure/br_on_null-null`. -/
theorem Step.brOnNullNull_presCtl {s : Store H} {C : Context} {l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [.ref .null, .plain (.brOnNull l)] it) (hC : C.Wf) :
    AdminsOk s C [.plain (.br l)] it := by
  obtain ⟨ts, ht, t, hl, hh, -, -, hrep⟩ := brOnNull_invCtl (v := .ref .null) h
  have hts := hC.label hl
  exact hrep _ (.single (.plain (by
    simpa using InstrOk.br (t₁ := []) hl ⟨by simp, by simp [hts, hh], by simp⟩)))

/-- `Step_pure/br_on_null-addr`. -/
theorem Step.brOnNullAddr_presCtl {s : Store H} {C : Context} {v : Val} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [v.toAdmin, .plain (.brOnNull l)] it) (hC : C.Wf)
    (hv : v ≠ .ref .null) : AdminsOk s C [v.toAdmin] it := by
  obtain ⟨ts, ht, t, hl, hh, hvt, hs, hrep⟩ := brOnNull_invCtl h
  have hts := hC.label hl
  have h1 := nonnull_valCtl (n' := false) hvt hs hv (by simpa using hh)
  exact hrep _ (by simpa using AdminsOk.frame h1 hts)

theorem brOnNonNull_invCtl {s : Store H} {C : Context} {v : Val} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [v.toAdmin, .plain (.brOnNonNull l)] it) :
    ∃ ts n ht t, C.labels[l.toNat]? = some (ts ++ [Ty.refT n ht]) ∧ ValOk s v t ∧
      Sub C.toTypeCtx t (Ty.refT true ht) ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨ts, [], ts⟩ → AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brOnNonNull l)) it' →
      it'.inits = [] ∧ 1 ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brOnNonNull _ => exact ⟨rfl, by simp⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, b, t₂, t, hi, hv, hs, hrep⟩ := redex1_invCtl hI h
  generalize hP : A ++ [b] = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brOnNonNull hl =>
      obtain ⟨rfl, rfl⟩ := append_single_invCtl hP
      exact ⟨_, _, _, _, hl, hv, hs, hrep⟩
    | _ => rename_i hh; cases hh

/-- `Step_pure/br_on_non_null-null`. -/
theorem Step.brOnNonNullNull_presCtl {s : Store H} {C : Context} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [.ref .null, .plain (.brOnNonNull l)] it) (hC : C.Wf) :
    AdminsOk s C [] it := by
  obtain ⟨ts, n, ht, t, hl, -, -, hrep⟩ := brOnNonNull_invCtl (v := .ref .null) h
  have hts := hC.label hl
  exact hrep _ (AdminsOk.id (ResultOk.left hts))

/-- `Step_pure/br_on_non_null-addr`. -/
theorem Step.brOnNonNullAddr_presCtl {s : Store H} {C : Context} {v : Val} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [v.toAdmin, .plain (.brOnNonNull l)] it) (hC : C.Wf)
    (hv : v ≠ .ref .null) : AdminsOk s C [v.toAdmin, .plain (.br l)] it := by
  obtain ⟨ts, n, ht, t, hl, hvt, hs, hrep⟩ := brOnNonNull_invCtl h
  have hts := hC.label hl
  simp only [ResultOk.append_iff, ResultOk.cons_iff, ResultOk.nil_iff, and_true] at hts
  have h1 := nonnull_valCtl (n' := n) hvt hs hv hts.2
  have h2 : AdminsOk s C [v.toAdmin] ⟨ts ++ [], [], ts ++ [Ty.refT n ht]⟩ := .frame h1 hts.1
  have h3 : AdminsOk s C [.plain (.br l)] ⟨ts ++ [Ty.refT n ht], [], ts⟩ := .single (.plain (by
    simpa using InstrOk.br (t₁ := []) hl ⟨by simp, hts.1, by simp⟩))
  have := AdminsOk.seq (by simpa using h2) (by simp) h3
  exact hrep _ (by simpa using this)

theorem closeRef_eqCtl {C : Context} {f : Frame} (ht : C.types = f.module.types) (rt : RefType) :
    C.closeRef rt = f.module.instRef rt := by
  simp [Context.closeRef, ModuleInst.instRef, ht]

theorem brOnCast_invCtl {s : Store H} {C : Context} {r : Ref} {l : LabelIdx}
    {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCast l rt₁ rt₂)] it) :
    ∃ ts rt t, C.labels[l.toNat]? = some (ts ++ [.refv rt]) ∧ TyOk C.toTypeCtx (C.closeRef rt₁) ∧
      TyOk C.toTypeCtx (C.closeRef rt₂) ∧ Sub C.toTypeCtx (C.closeRef rt₂) rt ∧
      ValOk s (.ref r) t ∧ Sub C.toTypeCtx t (.refv (C.closeRef rt₁)) ∧
      ∀ (out : List Admin),
        AdminsOk s C out ⟨ts, [], ts ++ [.refv (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂))]⟩ →
        AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brOnCast l rt₁ rt₂)) it' →
      it'.inits = [] ∧ 1 ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brOnCast _ _ _ _ _ => exact ⟨rfl, by simp⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, b, t₂, t, hi, hv, hs, hrep⟩ := redex1_invCtl (v := .ref r) hI h
  generalize hP : A ++ [b] = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brOnCast hl h₁ h₂ _ h₂l =>
      obtain ⟨rfl, rfl⟩ := append_single_invCtl hP
      exact ⟨_, _, _, hl, h₁, h₂, h₂l, hv, hs, hrep⟩
    | _ => rename_i hh; cases hh

/-- `Step_read/br_on_cast-succeed`. -/
theorem Step.brOnCastSucceed_presCtl {s : Store H} {C : Context} {f : Frame} {r : Ref}
    {l : LabelIdx} {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCast l rt₁ rt₂)] it) (hC : C.Wf)
    (ht : C.types = f.module.types) (hr : RefOk s r (f.module.instRef rt₂)) :
    AdminsOk s C [.ref r, .plain (.br l)] it := by
  obtain ⟨ts, rt, t, hl, h₁, h₂, h₂l, -, -, hrep⟩ := brOnCast_invCtl h
  rw [← closeRef_eqCtl ht] at hr
  have hts := hC.label hl
  simp only [ResultOk.append_iff, ResultOk.cons_iff, ResultOk.nil_iff, and_true,
    TyOk.refv_iff] at hts
  have h1 : AdminsOk s C [(Val.ref r).toAdmin] (.plain [] [.refv rt]) :=
    AdminsOk.val_subCtl (.ref hr) (.refv h₂l) (.refv hts.2)
  have h2 : AdminsOk s C [.ref r] ⟨ts ++ [], [], ts ++ [.refv rt]⟩ := .frame h1 hts.1
  have h3 : AdminsOk s C [.plain (.br l)]
      ⟨ts ++ [.refv rt], [], ts ++ [.refv (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂))]⟩ :=
    .single (.plain (by
      simpa using InstrOk.br (t₁ := []) hl ⟨by simp, by simp [hts.1, TyOk.diffrt h₁], by simp⟩))
  have := AdminsOk.seq (by simpa using h2) (by simp) h3
  exact hrep _ (by simpa using this)

/-- `Step_read/br_on_cast-fail`. (Statement: needs the cast target to be
well-formed in the empty context, which a null reference is checked against.) -/
theorem Step.brOnCastFail_presCtl {s : Store H} {C : Context} {f : Frame} {r : Ref}
    {l : LabelIdx} {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCast l rt₁ rt₂)] it) (hC : C.Wf)
    (ht : C.types = f.module.types) (hr : ¬ RefOk s r (f.module.instRef rt₂))
    (hrt₂ : TyOk {} (f.module.instRef rt₂)) :
    AdminsOk s C [.ref r] it := by
  obtain ⟨ts, rt, t, hl, h₁, h₂, h₂l, hv, hs, hrep⟩ := brOnCast_invCtl h
  rw [← closeRef_eqCtl ht] at hr hrt₂
  have hts := hC.label hl
  simp only [ResultOk.append_iff] at hts
  obtain ⟨t', hv', hs'⟩ := ref_diffCtl hv hs hr hrt₂
  have h1 : AdminsOk s C [(Val.ref r).toAdmin]
      (.plain [] [.refv (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂))]) :=
    AdminsOk.val_subCtl hv' hs' (.refv (TyOk.diffrt h₁))
  exact hrep _ (by simpa [Val.toAdmin] using AdminsOk.frame h1 hts.1)

theorem brOnCastFail_invCtl {s : Store H} {C : Context} {r : Ref} {l : LabelIdx}
    {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCastFail l rt₁ rt₂)] it) :
    ∃ ts rt t, C.labels[l.toNat]? = some (ts ++ [.refv rt]) ∧ TyOk C.toTypeCtx (C.closeRef rt₁) ∧
      TyOk C.toTypeCtx (C.closeRef rt₂) ∧
      Sub C.toTypeCtx (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂)) rt ∧
      ValOk s (.ref r) t ∧ Sub C.toTypeCtx t (.refv (C.closeRef rt₁)) ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨ts, [], ts ++ [.refv (C.closeRef rt₂)]⟩ →
        AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brOnCastFail l rt₁ rt₂)) it' →
      it'.inits = [] ∧ 1 ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brOnCastFail _ _ _ _ _ => exact ⟨rfl, by simp⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, b, t₂, t, hi, hv, hs, hrep⟩ := redex1_invCtl (v := .ref r) hI h
  generalize hP : A ++ [b] = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brOnCastFail hl h₁ h₂ _ hdl =>
      obtain ⟨rfl, rfl⟩ := append_single_invCtl hP
      exact ⟨_, _, _, hl, h₁, h₂, hdl, hv, hs, hrep⟩
    | _ => rename_i hh; cases hh

/-- `Step_read/br_on_cast_fail-succeed`. -/
theorem Step.brOnCastFailSucceed_presCtl {s : Store H} {C : Context} {f : Frame} {r : Ref}
    {l : LabelIdx} {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCastFail l rt₁ rt₂)] it) (hC : C.Wf)
    (ht : C.types = f.module.types) (hr : RefOk s r (f.module.instRef rt₂)) :
    AdminsOk s C [.ref r] it := by
  obtain ⟨ts, rt, t, hl, h₁, h₂, -, -, -, hrep⟩ := brOnCastFail_invCtl h
  rw [← closeRef_eqCtl ht] at hr
  have hts := hC.label hl
  simp only [ResultOk.append_iff] at hts
  have h1 : AdminsOk s C [(Val.ref r).toAdmin] (.plain [] [.refv (C.closeRef rt₂)]) :=
    AdminsOk.val_singleCtl (.ref hr)
  exact hrep _ (by simpa [Val.toAdmin] using AdminsOk.frame h1 hts.1)

/-- `Step_read/br_on_cast_fail-fail`. (Statement: as `brOnCastFail_presCtl`.) -/
theorem Step.brOnCastFailFail_presCtl {s : Store H} {C : Context} {f : Frame} {r : Ref}
    {l : LabelIdx} {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCastFail l rt₁ rt₂)] it) (hC : C.Wf)
    (ht : C.types = f.module.types) (hr : ¬ RefOk s r (f.module.instRef rt₂))
    (hrt₂ : TyOk {} (f.module.instRef rt₂)) :
    AdminsOk s C [.ref r, .plain (.br l)] it := by
  obtain ⟨ts, rt, t, hl, h₁, h₂, hdl, hv, hs, hrep⟩ := brOnCastFail_invCtl h
  rw [← closeRef_eqCtl ht] at hr hrt₂
  have hts := hC.label hl
  simp only [ResultOk.append_iff, ResultOk.cons_iff, ResultOk.nil_iff, and_true,
    TyOk.refv_iff] at hts
  obtain ⟨t', hv', hs'⟩ := ref_diffCtl hv hs hr hrt₂
  have h1 : AdminsOk s C [(Val.ref r).toAdmin] (.plain [] [.refv rt]) :=
    AdminsOk.val_subCtl hv' (Sub.trans_valCtl (.refv (TyOk.diffrt h₁)) hs' (.refv hdl))
      (.refv hts.2)
  have h2 : AdminsOk s C [.ref r] ⟨ts ++ [], [], ts ++ [.refv rt]⟩ := .frame h1 hts.1
  have h3 : AdminsOk s C [.plain (.br l)] ⟨ts ++ [.refv rt], [], ts ++ [.refv (C.closeRef rt₂)]⟩ :=
    .single (.plain (by
      simpa using InstrOk.br (t₁ := []) hl ⟨by simp, by simp [hts.1, h₂], by simp⟩))
  have := AdminsOk.seq (by simpa using h2) (by simp) h3
  exact hrep _ (by simpa using this)

/-! ## Branches and returns out of labels, handlers and frames -/

/-- Inversion of a label: its principal typing is `[] → t₂` with `t₂` well-formed,
and its continuation, body and label type. -/
theorem label_repCtl {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {body : List Admin} {it : InstrType} (hC : C.Wf)
    (h : AdminsOk s C [.label n cont body] it) :
    ∃ t₂ t' xs' xs, t'.length = n ∧ InstrTypeOk C ⟨t', xs', t₂⟩ ∧
      AdminsOk s C (expression cont) ⟨t', xs', t₂⟩ ∧
      AdminsOk s (C.withLabel t') body ⟨[], xs, t₂⟩ ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨[], [], t₂⟩ → AdminsOk s C out it := by
  obtain ⟨A, t₂, ha, hrep⟩ := single_repCtl AdminOk.label_initsCtl h
  obtain ⟨hA, -, t', xs', xs, hn, hc, hb⟩ := AdminOk.label_invCtl ha
  simp only at hA hc hb
  subst hA
  exact ⟨t₂, t', xs', xs, hn, AdminsOk.expr_okCtl hC hc, hc, hb, fun out hout => hrep s out hout⟩

/-- `Step_pure/br-label-zero`. -/
theorem Step.brLabelZero_presCtl {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)] it)
    (hC : C.Wf) (hl : l.toNat = 0) (hn : vs.length = n) :
    AdminsOk s C (vals vs ++ expression cont) it := by
  obtain ⟨t₂, t', xs', xs, hn', hok, hc, hb, hrep⟩ := label_repCtl hC h
  have hC' := Context.Wf.withLabelCtl hC hok.1
  rw [← vals_append] at hb
  obtain ⟨m, tv, F, it₀, hm, hv, h₁, hbr, h₂⟩ := vals_admin_invCtl hC' hb
  obtain ⟨lt, t₁, hlt, hp⟩ := AdminOk.br_invCtl hbr
  have e : lt = t' := by
    simp only [Context.withLabel, hl, List.getElem?_cons_zero, Option.some.injEq] at hlt
    exact hlt.symm
  subst e
  rw [hp, ← List.append_assoc] at h₂
  obtain ⟨tv₂, hv₂, hs₂⟩ := suffix_subCtl hC.types hm hv h₁ h₂ (by omega)
  have hV : AdminsOk s C (vals vs) (.plain [] lt) := AdminsOk.vals_toCtl hv₂ hs₂ hok.1
  have hseq := AdminsOk.seq hV (by simp) hc
  exact hrep _ (.sub hseq ⟨.nil, ResultSub.refl _ _, by simp⟩ ⟨by simp, hok.2.1, by simp⟩)

/-- `Step_pure/br-label-succ`. -/
theorem Step.brLabelSucc_presCtl {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {vs : List Val} {l : LabelIdx} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)] it)
    (hC : C.Wf) (hl : 0 < l.toNat) :
    AdminsOk s C (vals vs ++ [.plain (.br (labelPred l))]) it := by
  obtain ⟨t₂, t', xs', xs, hn', hok, hc, hb, hrep⟩ := label_repCtl hC h
  have hC' := Context.Wf.withLabelCtl hC hok.1
  obtain ⟨m, tv, F, it₀, hm, hv, h₁, hbr, h₂⟩ := vals_admin_invCtl hC' hb
  obtain ⟨lt, t₁, hlt, hp⟩ := AdminOk.br_invCtl hbr
  have hlt' : C.labels[(labelPred l).toNat]? = some lt := by
    obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by omega⟩
    have e : (labelPred l).toNat = k := by
      show l.toNat - 1 = k
      omega
    rw [e]
    rw [hk] at hlt
    simpa [Context.withLabel] using hlt
  rw [hp, ← List.append_assoc] at h₂
  exact hrep _ (vals_poly_retypeCtl (p := []) (by simp) hm hok.2.1 hv h₁ h₂
    fun t₁ ht₁ => .plain (.br hlt' ⟨ht₁, hok.2.1, by simp⟩))

/-- Inversion of a handler: its principal typing, body and catches. -/
theorem handler_bodyCtl {s : Store H} {C : Context} {n : Nat} {cs : List Catch}
    {body : List Admin} {it : InstrType}
    (h : AdminsOk s C [.handler n cs body] it) :
    ∃ t₂ xs, AdminsOk s C body ⟨[], xs, t₂⟩ := by
  obtain ⟨A, t₂, ha, -⟩ := single_repCtl AdminOk.handler_initsCtl h
  obtain ⟨-, -, -, xs, hb⟩ := AdminOk.handler_invCtl ha
  exact ⟨t₂, xs, hb⟩

/-- `Step_pure/br-handler`. (Statement: needs well-formed results of `it`; the
handler's own result type need not be well-formed, see the report.) -/
theorem Step.brHandler_presCtl {s : Store H} {C : Context} {n : Nat} {cs : List Catch}
    {vs : List Val} {l : LabelIdx} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)] it)
    (hC : C.Wf) (hr : ResultOk C.toTypeCtx it.results) :
    AdminsOk s C (vals vs ++ [.plain (.br l)]) it := by
  obtain ⟨t₂, xs, hb⟩ := handler_bodyCtl h
  obtain ⟨m, tv, F, it₀, hm, hv, h₁, hbr, h₂⟩ := vals_admin_invCtl hC hb
  obtain ⟨lt, t₁, hlt, hp⟩ := AdminOk.br_invCtl hbr
  rw [hp, ← List.append_assoc] at h₂
  have hp' := (AdminsOk.params_ok hC h).1
  exact single_at_itCtl hC hr AdminOk.handler_initsCtl h
    (vals_poly_retypeCtl hp' hm hr hv h₁ h₂ fun t₁ ht₁ => .plain (.br hlt ⟨ht₁, hr, by simp⟩))

/-- `Step_pure/return-label`. -/
theorem Step.returnLabel_presCtl {s : Store H} {C : Context} {n : Nat} {cont : List Instr}
    {vs : List Val} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.label n cont (vals vs ++ [.plain .return_] ++ rest)] it)
    (hC : C.Wf) :
    AdminsOk s C (vals vs ++ [.plain .return_]) it := by
  obtain ⟨t₂, t', xs', xs, hn', hok, hc, hb, hrep⟩ := label_repCtl hC h
  have hC' := Context.Wf.withLabelCtl hC hok.1
  obtain ⟨m, tv, F, it₀, hm, hv, h₁, hret, h₂⟩ := vals_admin_invCtl hC' hb
  obtain ⟨lt, t₁, hlt, hp⟩ := AdminOk.return_invCtl hret
  have hlt' : C.return_ = some lt := hlt
  rw [hp, ← List.append_assoc] at h₂
  exact hrep _ (vals_poly_retypeCtl (p := []) (by simp) hm hok.2.1 hv h₁ h₂
    fun t₁ ht₁ => .plain (.return_ hlt' ⟨ht₁, hok.2.1, by simp⟩))

/-- `Step_pure/return-handler`. (Statement: as `brHandler_presCtl`.) -/
theorem Step.returnHandler_presCtl {s : Store H} {C : Context} {n : Nat} {cs : List Catch}
    {vs : List Val} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.handler n cs (vals vs ++ [.plain .return_] ++ rest)] it)
    (hC : C.Wf) (hr : ResultOk C.toTypeCtx it.results) :
    AdminsOk s C (vals vs ++ [.plain .return_]) it := by
  obtain ⟨t₂, xs, hb⟩ := handler_bodyCtl h
  obtain ⟨m, tv, F, it₀, hm, hv, h₁, hret, h₂⟩ := vals_admin_invCtl hC hb
  obtain ⟨lt, t₁, hlt, hp⟩ := AdminOk.return_invCtl hret
  rw [hp, ← List.append_assoc] at h₂
  have hp' := (AdminsOk.params_ok hC h).1
  exact single_at_itCtl hC hr AdminOk.handler_initsCtl h
    (vals_poly_retypeCtl hp' hm hr hv h₁ h₂ fun t₁ ht₁ => .plain (.return_ hlt ⟨ht₁, hr, by simp⟩))

/-- Inversion of a frame: its principal typing `[] → t₂`, body and frame context. -/
theorem frame_repCtl {s : Store H} {C : Context} {n : Nat} {fr : Frame}
    {body : List Admin} {it : InstrType} (h : AdminsOk s C [.frame n fr body] it) :
    ∃ t₂ C', FrameOk s fr C' ∧ t₂.length = n ∧
      AdminsOk s { C' with return_ := some t₂ } body (.plain [] t₂) ∧ ResultOk {} t₂ ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨[], [], t₂⟩ → AdminsOk s C out it := by
  obtain ⟨A, t₂, ha, hrep⟩ := single_repCtl AdminOk.frame_initsCtl h
  obtain ⟨hA, -, C', hf, hn, hb, hok⟩ := AdminOk.frame_invCtl ha
  simp only at hA hn hb hok
  subst hA
  exact ⟨t₂, C', hf, hn, hb, hok, fun out hout => hrep s out hout⟩

/-- Values typed in a frame's context below a closed result type, retyped in the
caller's context. -/
theorem frame_vals_transferCtl {s : Store H} {C C' : Context} {fr : Frame} {vs : List Val}
    {tv t₂ : List CValType} (hf : FrameOk s fr C')
    (hX : ∀ C' : Context, FrameOk s fr C' → ∀ (v : Val) (t t' : CValType), ValOk s v t →
      Sub C'.toTypeCtx t t' → TyOk {} t' → ValOk s v t')
    (hok : ResultOk {} t₂) (hv : List.Forall₂ (ValOk s) vs tv)
    (hs : List.Forall₂ (SubEqR C'.toTypeCtx) tv t₂) :
    AdminsOk s C (vals vs) (.plain [] t₂) := by
  have hX' := hX C' hf
  have hv' : List.Forall₂ (ValOk s) vs t₂ := by
    clear hX
    induction hv generalizing t₂ with
    | nil => cases hs; exact .nil
    | @cons v t vs tv hvt _ ih =>
      cases hs with
      | @cons _ t' _ t₂' hst hs' =>
        refine .cons ?_ (ih (fun x hx => hok x (by simp [hx])) hs')
        rcases hst with rfl | ⟨hst, -⟩
        · exact hvt
        · exact hX' v t t' hvt hst (hok t' (by simp))
  exact AdminsOk.of_vals hv' fun t ht => TyOk.of_empty _ (hok t ht)

/-- `Step_pure/frame-vals`. (Statement: needs the transfer hypothesis `hX` for
values typed in the callee frame's context; see the report.) -/
theorem Step.frameVals_presCtl {s : Store H} {C : Context} {fi : Frame} {n : Nat}
    {vs : List Val} {it : InstrType}
    (h : AdminsOk s C [.frame n fi (vals vs)] it)
    (hX : ∀ C' : Context, FrameOk s fi C' → ∀ (v : Val) (t t' : CValType), ValOk s v t →
      Sub C'.toTypeCtx t t' → TyOk {} t' → ValOk s v t') :
    AdminsOk s C (vals vs) it := by
  obtain ⟨t₂, C', hf, -, hb, hok, hrep⟩ := frame_repCtl h
  obtain ⟨-, -, tv, hv, hs⟩ := AdminsOk.vals_auxPCtl hb vs rfl
  exact hrep _ (frame_vals_transferCtl hf hX hok hv (by simpa using hs))

/-- `Step_pure/return-frame`. (Statement: needs well-formed frame contexts `hW`
and the transfer hypothesis `hX`; see the report.) -/
theorem Step.returnFrame_presCtl {s : Store H} {C : Context} {fi : Frame} {n : Nat}
    {vs' vs : List Val} {rest : List Admin} {it : InstrType}
    (h : AdminsOk s C [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] it)
    (hn : vs.length = n)
    (hW : ∀ C' : Context, FrameOk s fi C' → C'.Wf)
    (hX : ∀ C' : Context, FrameOk s fi C' → ∀ (v : Val) (t t' : CValType), ValOk s v t →
      Sub C'.toTypeCtx t t' → TyOk {} t' → ValOk s v t') :
    AdminsOk s C (vals vs) it := by
  obtain ⟨t₂, C', hf, hn', hb, hok, hrep⟩ := frame_repCtl h
  have hW' := hW C' hf
  have hC'' : ({ C' with return_ := some t₂ } : Context).Wf := by
    refine ⟨hW'.types, hW'.tags, hW'.globals, hW'.tables, hW'.funcs, hW'.locals, hW'.labels, ?_, hW'.elems⟩
    intro ts hts
    simp only [Option.some.injEq] at hts
    subst hts
    exact fun t ht => TyOk.of_empty _ (hok t ht)
  rw [← vals_append] at hb
  obtain ⟨m, tv, F, it₀, hm, hv, h₁, hret, h₂⟩ := vals_admin_invCtl hC'' hb
  obtain ⟨lt, t₁, hlt, hp⟩ := AdminOk.return_invCtl hret
  simp only [Option.some.injEq] at hlt
  subst hlt
  rw [hp, ← List.append_assoc] at h₂
  obtain ⟨tv₂, hv₂, hs₂⟩ := suffix_subCtl hW'.types hm hv h₁ h₂ (by omega)
  exact hrep _ (frame_vals_transferCtl hf hX hok hv₂
    (forall₂_subEqR_of_sub hs₂ fun t ht => TyOk.of_empty _ (hok t ht)))


end Silmaril.Wasm.Execution.Core
