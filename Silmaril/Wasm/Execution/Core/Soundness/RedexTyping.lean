module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Validation.Subtyping.Properties

@[expose] public section

/-! # Typing inversion and replacement for redexes `val* instr`

Helper infrastructure for the reference/aggregate soundness units.

`redex_inv` inverts a typing of `vals vs ++ [.plain i]` at `it` into
* a principal typing `InstrOk C i ⟨A ++ B, [], t₂⟩` of the instruction,
* per-value typings `ValOk s v t` of the operands, with `ts ≤ B` pointwise,
* a *replacement* certificate: any code typed at `⟨A, [], t₂⟩` (in any store)
  is typed at the original `it` (`BaseRep` followed by `Lift`).

Only transitivity of subtyping on *value* types is used, which needs no
well-formedness of the context (`Sub.trans_val`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Lists -/

theorem List.forall₂_append_right_split {α β : Type _} {R : α → β → Prop} {l : List α}
    {l₁ l₂ : List β} (h : List.Forall₂ R l (l₁ ++ l₂)) :
    ∃ a b, l = a ++ b ∧ List.Forall₂ R a l₁ ∧ List.Forall₂ R b l₂ := by
  refine ⟨l.take l₁.length, l.drop l₁.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · exact List.forall₂_take_append l l₁ l₂ h
  · exact List.forall₂_drop_append l l₁ l₂ h

theorem ResultOk.appendRT {Δ : TypeCtx} {a b : List CValType} (ha : ResultOk Δ a) (hb : ResultOk Δ b) :
    ResultOk Δ (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem ResultOk.single {Δ : TypeCtx} {t : CValType} (h : TyOk Δ t) : ResultOk Δ [t] := by
  intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact h

theorem ResultOk.leftRT {Δ : TypeCtx} {a b : List CValType} (h : ResultOk Δ (a ++ b)) :
    ResultOk Δ a := fun t ht => h t (List.mem_append_left _ ht)

theorem ResultOk.rightRT {Δ : TypeCtx} {a b : List CValType} (h : ResultOk Δ (a ++ b)) :
    ResultOk Δ b := fun t ht => h t (List.mem_append_right _ ht)

/-! ## Transitivity of value subtyping (no context well-formedness needed) -/

theorem Sub.trans_heap {Δ : TypeCtx} {a b c : CHeapType} (hb : TyOk Δ b) (hab : Sub Δ a b)
    (hbc : Sub Δ b c) : Sub Δ a c := .heapTrans hb hab hbc

theorem Sub.trans_ref {Δ : TypeCtx} {a b c : CRefType} (hb : TyOk Δ b) (hab : Sub Δ a b)
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

theorem Sub.trans_val {Δ : TypeCtx} {a b c : CValType} (hb : TyOk Δ b) (hab : Sub Δ a b)
    (hbc : Sub Δ b c) : Sub Δ a c := by
  cases hab with
  | num => exact hbc
  | vec => exact hbc
  | botv => exact .botv
  | refv h1 =>
    cases hb with
    | refv hr =>
      cases hbc with
      | refv h2 => exact .refv (Sub.trans_ref hr h1 h2)

theorem ResultSub.trans_ok {Δ : TypeCtx} {a b c : List CValType} (hb : ResultOk Δ b)
    (hab : ResultSub Δ a b) (hbc : ResultSub Δ b c) : ResultSub Δ a c := by
  induction hab generalizing c with
  | nil => exact hbc
  | cons h _ ih =>
    cases hbc with
    | cons h' hl' =>
      exact .cons (Sub.trans_val (hb _ (by simp)) h h')
        (ih (fun t ht => hb t (by simp [ht])) hl')

/-! ## Empty sequences -/

theorem AdminsOk.nil_store {H' : Type} {s : Store H} (s' : Store H') :
    ∀ {C : Context} {as : List Admin}
    {it : InstrType}, AdminsOk s C as it → as = [] → AdminsOk s' C [] it
  | _, _, _, .nil, _ => .nil
  | _, _, _, .single _, he => by simp at he
  | _, _, _, .cons _ _ _, he => by simp at he
  | _, _, _, .seq h₁ hx h₂, he => by
    obtain ⟨e₁, e₂⟩ := List.append_eq_nil_iff.mp he
    have := AdminsOk.seq (AdminsOk.nil_store s' h₁ e₁) hx (AdminsOk.nil_store s' h₂ e₂)
    simpa using this
  | _, _, _, .sub h hs hok, he => .sub (AdminsOk.nil_store s' h he) hs hok
  | _, _, _, .frame h hok, he => .frame (AdminsOk.nil_store s' h he) hok

/-! ## Lifting a typing through `sub`/`frame` steps and empty sequences -/

/-- A sequence of `Instrs_ok2/sub` and `Instrs_ok2/frame` steps, and compositions
with typed empty sequences on either side. -/
inductive Lift (C : Context) : InstrType → InstrType → Prop where
  | refl {it : InstrType} : Lift C it it
  | sub {it₀ it₁ it₂ : InstrType} (h : Lift C it₀ it₁) (hs : InstrTypeSub C it₁ it₂)
      (hok : InstrTypeOk C it₂) : Lift C it₀ it₂
  | frame {it₀ : InstrType} {ts p r : List CValType} {x : List Nat}
      (h : Lift C it₀ ⟨p, x, r⟩) (hok : ResultOk C.toTypeCtx ts) :
      Lift C it₀ ⟨ts ++ p, x, ts ++ r⟩
  | tail {it₀ : InstrType} {p m r : List CValType} {x₁ x₂ : List Nat}
      (h : Lift C it₀ ⟨p, x₁, m⟩) (hx : ∀ x ∈ x₁, ∃ lt, C.locals[x]? = some lt)
      (ht : ∀ {H' : Type} (s : Store H'), AdminsOk s (C.initLocals x₁) [] ⟨m, x₂, r⟩) :
      Lift C it₀ ⟨p, x₁ ++ x₂, r⟩
  | head {it₀ : InstrType} {p m r : List CValType} {x₁ x₂ : List Nat}
      (h : Lift C it₀ ⟨m, x₂, r⟩) (hp : ResultSub C.toTypeCtx p m)
      (hpok : ResultOk C.toTypeCtx p) (hmok : ResultOk C.toTypeCtx m)
      (hx : ∀ x ∈ x₁, ∃ t, C.locals[x]? = some ⟨.set, t⟩) :
      Lift C it₀ ⟨p, x₁ ++ x₂, r⟩

theorem Lift.apply {s : Store H} {C : Context} {as : List Admin} {it₀ it : InstrType}
    (hl : Lift C it₀ it) (h : AdminsOk s C as it₀) : AdminsOk s C as it := by
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
theorem Lift.dropTop {C : Context} {it₀ it : InstrType} (hl : Lift C it₀ it) :
    ∀ {A B : List CValType}, it₀.params = A ++ B →
    ∃ QA QB, it.params = QA ++ QB ∧ ResultSub C.toTypeCtx QB B ∧
      Lift C ⟨A, it₀.inits, it₀.results⟩ ⟨QA, it.inits, it.results⟩ ∧
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
    obtain ⟨QA', QB', hp', h₁, h₂⟩ := List.forall₂_append_right_split hs₁
    have hokp : ResultOk C.toTypeCtx (QA' ++ QB') := hp' ▸ hok.1
    refine ⟨QA', QB', hp', ?_, ?_, .inr (ResultOk.rightRT hokp)⟩
    · rcases hinv with rfl | hQ
      · exact h₂
      · exact ResultSub.trans_ok hQ h₂ hQB
    · refine .sub hl ⟨h₁, hs₂, hs₃⟩ ⟨ResultOk.leftRT hokp, hok.2.1, hok.2.2⟩
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
    obtain ⟨pA, pB, rfl, h₁, h₂⟩ := List.forall₂_append_right_split hp
    refine ⟨pA, pB, rfl, ?_, .head hl h₁ (ResultOk.leftRT hpok) (ResultOk.leftRT hmok) hx,
      .inr (ResultOk.rightRT hpok)⟩
    rcases hinv with rfl | hQ
    · exact h₂
    · exact ResultSub.trans_ok (ResultOk.rightRT hmok) h₂ hQB

/-- Appending an empty-sequence typing: the replacement for the empty tail. -/
def BaseRep (C : Context) (t₂ : List CValType) (xs₂ : List Nat) (t₃ : List CValType) : Prop :=
  ∀ (s' : Store H) (out : List Admin) (Q : List CValType),
    AdminsOk s' C out ⟨Q, [], t₂⟩ → AdminsOk s' C out ⟨Q, xs₂, t₃⟩

/-! ## Values -/

theorem AdminOk.val_invRT {s : Store H} {C : Context} {v : Val} {it : InstrType}
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

theorem SubEqR.trans_val {Δ : TypeCtx} {a b c : CValType} (h₁ : SubEqR Δ a b)
    (h₂ : SubEqR Δ b c) : SubEqR Δ a c := by
  rcases h₁ with rfl | ⟨h₁, hb⟩
  · exact h₂
  rcases h₂ with rfl | ⟨h₂, hc⟩
  · exact .inr ⟨h₁, hb⟩
  exact .inr ⟨Sub.trans_val hb h₁ h₂, hc⟩

theorem SubEqR.sub_right_val {Δ : TypeCtx} {a b c : CValType} (h₁ : SubEqR Δ a b)
    (h₂ : Sub Δ b c) (hc : TyOk Δ c) : SubEqR Δ a c :=
  h₁.trans_val (.inr ⟨h₂, hc⟩)

theorem forall₂_subEqR_resultSub {Δ : TypeCtx} {x y z : List CValType}
    (h₁ : List.Forall₂ (SubEqR Δ) x y) (h₂ : ResultSub Δ y z) : ResultSub Δ x z :=
  forall₂_comp (S := Sub Δ) h₁ h₂ fun _ _ _ _ _ _ hab hbc => by
    rcases hab with rfl | ⟨hab, hb⟩
    · exact hbc
    · exact Sub.trans_val hb hab hbc

theorem forall₂_subEqR_ok {Δ : TypeCtx} : ∀ {x y : List CValType},
    List.Forall₂ (SubEqR Δ) x y → ResultOk Δ x → ResultOk Δ y
  | _, _, .nil, _ => fun _ h => by cases h
  | _, _, .cons h t, hx => by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rcases h with rfl | ⟨_, hb⟩
      · exact hx _ (by simp)
      · exact hb
    · exact forall₂_subEqR_ok t (fun u hu => hx u (by simp [hu])) c hc

/-- Inversion for a value sequence (no well-formedness of the context needed). -/
theorem AdminsOk.vals_aux' {s : Store H} :
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
    obtain ⟨t, rfl, hv⟩ := AdminOk.val_invRT h
    refine ⟨by simp [ResultOk], by simp, [t], .cons hv .nil, ?_⟩
    simp only [List.nil_append]
    exact forall₂_self (fun _ => .inl rfl) _
  | C, _, _, .cons ha _ hs, vs, e => by
    obtain ⟨v, vs', rfl, hv, e'⟩ := List.map_eq_cons_iff.mp e.symm
    subst hv
    obtain ⟨_, hi, ts', hv', r⟩ := AdminsOk.vals_aux' hs vs' e'.symm
    obtain ⟨t, hit, hv⟩ := AdminOk.val_invRT ha
    simp only [InstrType.plain, InstrType.mk.injEq] at hit
    obtain ⟨rfl, rfl, rfl⟩ := hit
    have hC0 : C.initLocals [] = C := rfl
    rw [hC0] at hi r
    exact ⟨by simp [ResultOk], by simpa using hi, t :: ts', .cons hv hv', by simpa using r⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, vs, e => by
    obtain ⟨vs₁, vs₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp e.symm
    obtain ⟨p₁, i₁, ts₁, v₁, r₁⟩ := AdminsOk.vals_aux' h₁ vs₁ e₁.symm
    obtain ⟨_, i₂, ts₂, v₂, r₂⟩ := AdminsOk.vals_aux' h₂ vs₂ e₂.symm
    rw [Context.initLocals_of_set i₁] at i₂ r₂
    refine ⟨p₁, ?_, ts₁ ++ ts₂, forall₂_append v₁ v₂, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact i₁ x h
      · exact i₂ x h
    · rw [← List.append_assoc]
      exact forall₂_comp (forall₂_append r₁ (forall₂_self (fun _ => .inl rfl) ts₂)) r₂
        fun _ _ _ _ _ _ hab hbc => hab.trans_val hbc
  | _, _, _, .sub (it := it₀) h hs hok, vs, e => by
    obtain ⟨p, i, ts, hv, r⟩ := AdminsOk.vals_aux' h vs e
    refine ⟨hok.1, fun x hx => ?_, ts, hv, ?_⟩
    · by_cases hx' : x ∈ it₀.inits
      · exact i x hx'
      · exact hs.2.2 x hx hx'
    · have h1 : List.Forall₂ (SubEqR _) _ _ :=
        forall₂_append (forall₂_subEqR_of_sub hs.1 p) (forall₂_self (fun _ => .inl rfl) ts)
      exact forall₂_comp (forall₂_comp h1 r fun _ _ _ _ _ _ hab hbc => hab.trans_val hbc) hs.2.1
        fun _ _ c _ _ hc hab hbc => SubEqR.sub_right_val hab hbc (hok.2.1 c hc)
  | _, _, _, .frame h hok, vs, e => by
    obtain ⟨p, i, ts, hv, r⟩ := AdminsOk.vals_aux' h vs e
    refine ⟨ResultOk.appendRT hok p, i, ts, hv, ?_⟩
    rw [List.append_assoc]
    exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) r

/-! ## Redex inversion -/

/-- Inversion and replacement for `vals vs ++ [a]`, where `a` has only typings
with no initialised locals and at least `N` parameters, `vs.length ≤ N`. -/
theorem redex_inv_aux {s : Store H} {C : Context} {a : Admin} {N : Nat}
    (hI : ∀ it', AdminOk s C a it' → it'.inits = [] ∧ N ≤ it'.params.length) :
    ∀ {C' : Context} {as : List Admin} {it : InstrType}, AdminsOk s C' as it → C' = C →
    ∀ vs : List Val, as = vals vs ++ [a] → vs.length ≤ N →
    ∃ A B t₂ ts xs₂ t₃, AdminOk s C a ⟨A ++ B, [], t₂⟩ ∧ List.Forall₂ (ValOk s) vs ts ∧
      ResultSub C.toTypeCtx ts B ∧ BaseRep (H := H) C t₂ xs₂ t₃ ∧ Lift C ⟨A, xs₂, t₃⟩ it
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
      refine ⟨t₁, [], t₂, [], xs₂, t₃, by simpa using ha, .nil, .nil, ?_, by simpa using Lift.refl⟩
      intro s' out Q hout
      have := AdminsOk.append hout (by simp) (by simpa using AdminsOk.nil_store s' hs rfl)
      simpa using this
    | cons v vs' =>
      simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at he
      obtain ⟨ha', has'⟩ := he
      obtain ⟨tv, hit, hv⟩ := AdminOk.val_invRT (ha' ▸ ha)
      simp only [InstrType.plain, InstrType.mk.injEq] at hit
      obtain ⟨ht₁, hxs₁, ht₂⟩ := hit
      simp only [List.length_cons] at hlen
      obtain ⟨A', B', t₂', ts', xs₂', t₃', hi, hvs, hB, hrep, hl⟩ :=
        redex_inv_aux hI hs (by rw [hxs₁, hC]; rfl) vs' has' (by omega)
      subst hC ht₁ hxs₁ ht₂
      have hN := (hI _ hi).2
      have hBl := hB.length_eq
      have hvl := hvs.length_eq
      simp only [List.length_append] at hN
      obtain ⟨A, b, rfl⟩ : ∃ A b, A' = A ++ [b] := by
        rcases List.eq_nil_or_concat A' with h | ⟨L, b, h⟩
        · subst h; simp at hN; omega
        · exact ⟨L, b, by simpa using h⟩
      obtain ⟨QA, QB, hp, hQB, hl', -⟩ := hl.dropTop (A := A) (B := [b]) rfl
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
        redex_inv_aux hI h₁ hC vs he' hlen
      have ht : ∀ {H' : Type} (s' : Store H'),
          AdminsOk s' (C₀.initLocals xs₁) [] ⟨t₂, xs₂, t₃⟩ :=
        fun s' => AdminsOk.nil_store s' h₂ h0
      subst hC
      exact ⟨A, B, t₂', ts, xs₂', t₃', hi, hvs, hB, hrep, .tail hl hx ht⟩
    · rw [List.concat_eq_append] at h0
      have he2 : (as₁ ++ l) ++ [x] = vals vs ++ [a] := by
        rw [List.append_assoc, ← h0]; exact he
      obtain ⟨he₁, hxa⟩ := List.append_inj' he2 rfl
      simp only [List.cons.injEq, and_true] at hxa
      obtain ⟨vs₁, vs₂, hvs0, e₁, e₂⟩ := List.map_eq_append_iff.mp he₁.symm
      obtain ⟨p₁, i₁, ts₁, v₁, r₁⟩ := AdminsOk.vals_aux' h₁ vs₁ e₁.symm
      have hC₁ : C₀.initLocals xs₁ = C := by rw [Context.initLocals_of_set i₁, hC]
      have he₂ : as₂ = vals vs₂ ++ [a] := by rw [h0, hxa, ← e₂]; rfl
      have hlen₂ : vs₂.length ≤ N := by
        rw [hvs0] at hlen; simp only [List.length_append] at hlen; omega
      obtain ⟨A₂, B₂, t₂', ts₂, xs₂', t₃', hi, hvs₂, hB₂, hrep, hl⟩ :=
        redex_inv_aux hI h₂ hC₁ vs₂ he₂ hlen₂
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
      obtain ⟨QA, QB, hp, hQB, hl', -⟩ := hl.dropTop (A := A) (B := B₁) rfl
      simp only at hp
      subst hp
      have hQBl := hQB.length_eq
      dsimp only at r₁ p₁ i₁
      obtain ⟨a₁, b₁, hab, ha₁, hb₁⟩ := List.forall₂_append_right_split r₁
      have ha₁l := ha₁.length_eq
      have hb₁l := hb₁.length_eq
      have htot := congrArg List.length hab
      simp only [List.length_append] at htot
      obtain ⟨rfl, rfl⟩ := List.append_inj hab (by omega)
      refine ⟨A, B₁ ++ B₂, t₂', ts₁ ++ ts₂, xs₂', t₃', by simpa [List.append_assoc] using hi,
        forall₂_append v₁ hvs₂, List.rel_append (forall₂_subEqR_resultSub hb₁ hQB) hB₂, hrep, ?_⟩
      exact .head hl' (ha₁.imp fun _ _ h => h.sub) p₁ (forall₂_subEqR_ok ha₁ p₁) i₁
  | _, _, _, .sub h hs hok, hC, vs, he, hlen => by
    obtain ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, hl⟩ := redex_inv_aux hI h hC vs he hlen
    subst hC
    exact ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, .sub hl hs hok⟩
  | _, _, _, .frame h hok, hC, vs, he, hlen => by
    obtain ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, hl⟩ := redex_inv_aux hI h hC vs he hlen
    subst hC
    exact ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, .frame hl hok⟩

/-- **General redex inversion.** For `vals vs ++ [a]`, where every typing of `a`
initialises no locals and has at least `vs.length` parameters: the operands are
typed at (subtypes of) the top `B` of the principal parameters `A ++ B`, and any
code typed at `A → t₂` replaces the redex. -/
theorem redex_inv_gen {s : Store H} {C : Context} {a : Admin} {vs : List Val} {it : InstrType}
    (hI : ∀ it', AdminOk s C a it' → it'.inits = [] ∧ vs.length ≤ it'.params.length)
    (h : AdminsOk s C (vals vs ++ [a]) it) :
    ∃ A B t₂ ts, AdminOk s C a ⟨A ++ B, [], t₂⟩ ∧ List.Forall₂ (ValOk s) vs ts ∧
      ResultSub C.toTypeCtx ts B ∧
      ∀ (s' : Store H) (out : List Admin), AdminsOk s' C out ⟨A, [], t₂⟩ →
        AdminsOk s' C out it := by
  obtain ⟨A, B, t₂, ts, xs₂, t₃, hi, hvs, hB, hrep, hl⟩ :=
    redex_inv_aux hI h rfl vs rfl le_rfl
  exact ⟨A, B, t₂, ts, hi, hvs, hB, fun s' out hout => hl.apply (hrep s' out A hout)⟩

/-- **Redex inversion.** For a redex whose value count is the instruction's
arity: the operands are typed at (subtypes of) the principal parameters, and any
code typed at `[] → t₂` replaces the redex. -/
theorem redex_inv {s : Store H} {C : Context} {i : Instr} {vs : List Val} {it : InstrType}
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
  obtain ⟨A, B, t₂, ts, hi, hvs, hB, hrep⟩ := redex_inv_gen hI' h
  have hi' : InstrOk C i ⟨A ++ B, [], t₂⟩ := hi.plain_inv_arity (fun it hi => (hI it hi).2)
  have hN := (hI _ hi').2
  have hBl := hB.length_eq
  have hvl := hvs.length_eq
  simp only [List.length_append] at hN
  obtain rfl : A = [] := List.eq_nil_of_length_eq_zero (by omega)
  exact ⟨B, t₂, ts, by simpa using hi', hvs, hB, hrep⟩

/-! ## Typing replacement code -/

theorem AdminsOk.trap_single {s : Store H} {C : Context} {t₂ : List CValType}
    (hok : ResultOk C.toTypeCtx t₂) : AdminsOk s C [.trap] (.plain [] t₂) :=
  AdminsOk.single (.trap ⟨by simp [ResultOk], hok, by simp⟩)

theorem AdminsOk.val_single {s : Store H} {C : Context} {v : Val} {t : CValType}
    (hv : ValOk s v t) : AdminsOk s C [v.toAdmin] (.plain [] [t]) :=
  AdminsOk.single (AdminOk.toAdmin_ok hv)

theorem AdminsOk.single_ok {s : Store H} {C : Context} {a : Admin} {t₁ t₂ : List CValType}
    (ha : AdminOk s C a (.plain t₁ t₂)) (_hok : ResultOk C.toTypeCtx t₂) :
    AdminsOk s C [a] (.plain t₁ t₂) :=
  .single ha


/-- A single value, subsumed to a well-formed type. -/
theorem AdminsOk.val_sub {s : Store H} {C : Context} {v : Val} {t t' : CValType}
    (hv : ValOk s v t) (hs : Sub C.toTypeCtx t t') (hok : TyOk C.toTypeCtx t') :
    AdminsOk s C [v.toAdmin] (.plain [] [t']) :=
  .sub (AdminsOk.val_single hv) ⟨.nil, .cons hs .nil, by simp⟩
    ⟨by simp [ResultOk], by simpa [ResultOk] using hok, by simp⟩

theorem ValOk.i32 {s : Store H} (b : BitVec 32) : ValOk s (Val.i32 b) Ty.i32 := .num _

theorem AdminsOk.constI32 {s : Store H} {C : Context} (b : BitVec 32) :
    AdminsOk s C [constI32 b] (.plain [] [Ty.i32]) :=
  AdminsOk.val_single (ValOk.i32 b)

end Silmaril.Wasm.Execution.Core
