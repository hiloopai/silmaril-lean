module

public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryAux
public import Silmaril.Wasm.Execution.Core.Soundness.RefOkClosed
public import Silmaril.Wasm.Execution.Core.Soundness.ValToClosed

@[expose] public section

/-! # Typing helpers for the table and memory preservation proofs

* `TyOk.of_empty`: well-formedness in the empty context weakens to any context
  (closed types);
* `AdminsOk.redex_replace`: subject replacement for a redex `vals vs ++ [plain i]`
  whose instruction has an inits-free principal type consuming exactly the
  operands;
* a small combinator library (`SeqOk`) for typing reducts as straight-line
  stack programs `[] → R`;
* store updates (`setTable`, `setMem`, `setElem`, `setData`) preserve `StoreOk`
  and extend the store.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Weakening from the empty context -/

/-- Well-formedness in the empty context holds in every context. The empty
context has no `TYPES` (so a derivation contains no `_IDX`, and `$clos` is the
identity) and no top-level `RECS` (group checks replace `RECS`). -/
-- `Ty.clos_nil` is in `RefTyping.lean` (imported via `ValToClosed`).

theorem TypeCtx.unrollUse_weakenE {Δ₁ Δ₂ : TypeCtx} (ht : Δ₁.types = [])
    (hr : ∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) {u : CTypeUse}
    {st : CSubType} (h : Δ₁.unrollUse u = some st) : Δ₂.unrollUse u = some st := by
  cases u with
  | dt d => exact h
  | idx x => simp [TypeCtx.unrollUse, ht] at h
  | recv i => exact hr _ _ h

mutual
theorem TyOk.weakenE : ∀ {Δ₁ : TypeCtx} {k : TKind} {t : Ty k}, TyOk Δ₁ t → ∀ (Δ₂ : TypeCtx),
    Δ₁.types = [] → (∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) → TyOk Δ₂ t
  | _, _, _, .idx h, _, ht, _ => by simp [ht] at h
  | _, _, _, .recv h, _, _, hr => .recv (hr _ _ h)
  | _, _, _, .dt h, Δ₂, ht, hr => .dt (TyOk.weakenE h Δ₂ ht hr)
  | _, _, _, .defn h hi, Δ₂, ht, _ =>
    .defn (GroupOk2.weakenE h (Δ₂.withRecs _) ht fun _ _ h => h) hi
  | _, _, _, .abs a, _, _, _ => .abs a
  | _, _, _, .bot, _, _, _ => .bot
  | _, _, _, .use h, Δ₂, ht, hr => .use (TyOk.weakenE h Δ₂ ht hr)
  | _, _, _, .ref h, Δ₂, ht, hr => .ref (TyOk.weakenE h Δ₂ ht hr)
  | _, _, _, .num t, _, _, _ => .num t
  | _, _, _, .vec t, _, _, _ => .vec t
  | _, _, _, .refv h, Δ₂, ht, hr => .refv (TyOk.weakenE h Δ₂ ht hr)
  | _, _, _, .botv, _, _, _ => .botv
  | _, _, _, .val h, Δ₂, ht, hr => .val (TyOk.weakenE h Δ₂ ht hr)
  | _, _, _, .pack p, _, _, _ => .pack p
  | _, _, _, .field h, Δ₂, ht, hr => .field (TyOk.weakenE h Δ₂ ht hr)
  | _, _, _, .struct h, Δ₂, ht, hr => .struct (TyOk.weakenE h Δ₂ ht hr)
  | _, _, _, .array h, Δ₂, ht, hr => .array (TyOk.weakenE h Δ₂ ht hr)
  | _, _, _, .func hp hq, Δ₂, ht, hr =>
    .func (TyOk.weakenE hp Δ₂ ht hr) (TyOk.weakenE hq Δ₂ ht hr)
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons ha hl, Δ₂, ht, hr =>
    .cons (TyOk.weakenE ha Δ₂ ht hr) (TyOk.weakenE hl Δ₂ ht hr)

theorem SubOk2.weakenE : ∀ {Δ₁ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2 Δ₁ st i →
    ∀ (Δ₂ : TypeCtx), Δ₁.types = [] →
      (∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) → SubOk2 Δ₂ st i
  | _, _, _, .noSuper hct, Δ₂, ht, hr => .noSuper (TyOk.weakenE hct Δ₂ ht hr)
  | _, _, _, .oneSuper hu hb hun hct hsub, Δ₂, ht, hr =>
    .oneSuper (TyOk.weakenE hu Δ₂ ht hr) hb (TypeCtx.unrollUse_weakenE ht hr hun)
      (TyOk.weakenE hct Δ₂ ht hr) (Sub.weakenE hsub Δ₂ ht hr)

theorem GroupOk2.weakenE : ∀ {Δ₁ : TypeCtx} {g : CRecType} {i : Nat}, GroupOk2 Δ₁ g i →
    ∀ (Δ₂ : TypeCtx), Δ₁.types = [] →
      (∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) → GroupOk2 Δ₂ g i
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons h hs, Δ₂, ht, hr =>
    .cons (SubOk2.weakenE h Δ₂ ht hr) (GroupOk2.weakenE hs Δ₂ ht hr)

theorem Sub.weakenE : ∀ {Δ₁ : TypeCtx} {k : TKind} {a b : Ty k}, Sub Δ₁ a b → ∀ (Δ₂ : TypeCtx),
    Δ₁.types = [] → (∀ (i : Nat) (st : CSubType), Δ₁.recs[i]? = some st → Δ₂.recs[i]? = some st) → Sub Δ₂ a b
  | _, _, _, _, .heapRefl, _, _, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, Δ₂, ht, hr =>
    .heapTrans (TyOk.weakenE hok Δ₂ ht hr) (Sub.weakenE h₁ Δ₂ ht hr) (Sub.weakenE h₂ Δ₂ ht hr)
  | _, _, _, _, .eqAny, _, _, _ => .eqAny
  | _, _, _, _, .i31Eq, _, _, _ => .i31Eq
  | _, _, _, _, .structEq, _, _, _ => .structEq
  | _, _, _, _, .arrayEq, _, _, _ => .arrayEq
  | _, _, _, _, .defStruct h, _, _, _ => .defStruct h
  | _, _, _, _, .defArray h, _, _, _ => .defArray h
  | _, _, _, _, .defFunc h, _, _, _ => .defFunc h
  | _, _, _, _, .defDef h, Δ₂, ht, hr => .defDef (Sub.weakenE h Δ₂ ht hr)
  | _, _, _, _, .idxL hx _, _, ht, _ => by simp [ht] at hx
  | _, _, _, _, .idxR hx _, _, ht, _ => by simp [ht] at hx
  | _, _, _, _, .recStruct h, _, _, hr => .recStruct (hr _ _ h)
  | _, _, _, _, .recArray h, _, _, hr => .recArray (hr _ _ h)
  | _, _, _, _, .recFunc h, _, _, hr => .recFunc (hr _ _ h)
  | _, _, _, _, .recSub h hj, _, _, hr => .recSub (hr _ _ h) hj
  | _, _, _, _, .none hs hb, Δ₂, ht, hr => .none (Sub.weakenE hs Δ₂ ht hr) hb
  | _, _, _, _, .nofunc hs hb, Δ₂, ht, hr => .nofunc (Sub.weakenE hs Δ₂ ht hr) hb
  | _, _, _, _, .noexn hs hb, Δ₂, ht, hr => .noexn (Sub.weakenE hs Δ₂ ht hr) hb
  | _, _, _, _, .noextern hs hb, Δ₂, ht, hr => .noextern (Sub.weakenE hs Δ₂ ht hr) hb
  | _, _, _, _, .bot, _, _, _ => .bot
  | _, _, _, _, .refNonNull h, Δ₂, ht, hr => .refNonNull (Sub.weakenE h Δ₂ ht hr)
  | _, _, _, _, .refNull h, Δ₂, ht, hr => .refNull (Sub.weakenE h Δ₂ ht hr)
  | _, _, _, _, .num, _, _, _ => .num
  | _, _, _, _, .vec, _, _, _ => .vec
  | _, _, _, _, .refv h, Δ₂, ht, hr => .refv (Sub.weakenE h Δ₂ ht hr)
  | _, _, _, _, .botv, _, _, _ => .botv
  | _, _, _, _, .val h, Δ₂, ht, hr => .val (Sub.weakenE h Δ₂ ht hr)
  | _, _, _, _, .pack, _, _, _ => .pack
  | _, _, _, _, .fieldConst h, Δ₂, ht, hr => .fieldConst (Sub.weakenE h Δ₂ ht hr)
  | _, _, _, _, .fieldVar h₁ h₂, Δ₂, ht, hr =>
    .fieldVar (Sub.weakenE h₁ Δ₂ ht hr) (Sub.weakenE h₂ Δ₂ ht hr)
  | _, _, _, _, .struct h, Δ₂, ht, hr => .struct (Sub.weakenE h Δ₂ ht hr)
  | _, _, _, _, .array h, Δ₂, ht, hr => .array (Sub.weakenE h Δ₂ ht hr)
  | _, _, _, _, .func hp hq, Δ₂, ht, hr =>
    .func (Sub.weakenE hp Δ₂ ht hr) (Sub.weakenE hq Δ₂ ht hr)
  | _, _, _, _, .defRefl h, _, ht, _ => by
    rw [ht, Ty.clos_nil, Ty.clos_nil] at h
    subst h
    exact .defRefl rfl
  | _, _, _, _, .defSuper h hj hs, Δ₂, ht, hr => .defSuper h hj (Sub.weakenE hs Δ₂ ht hr)
  | _, _, _, _, .nil, _, _, _ => .nil
  | _, _, _, _, .cons h hl, Δ₂, ht, hr => .cons (Sub.weakenE h Δ₂ ht hr) (Sub.weakenE hl Δ₂ ht hr)
end

theorem TyOk.of_empty {k : TKind} {t : Ty k} (Δ : TypeCtx) (h : TyOk {} t) : TyOk Δ t :=
  TyOk.weakenE h Δ rfl fun _ _ h => by simp at h

/-! ## Result types -/

theorem resultOk_nil {Δ : TypeCtx} : ResultOk Δ [] := fun _ h => by cases h

theorem resultOk_cons {Δ : TypeCtx} {t : CValType} {ts : List CValType} :
    ResultOk Δ (t :: ts) ↔ TyOk Δ t ∧ ResultOk Δ ts := by
  simp [ResultOk]

theorem resultOk_append {Δ : TypeCtx} {ts ts' : List CValType} :
    ResultOk Δ (ts ++ ts') ↔ ResultOk Δ ts ∧ ResultOk Δ ts' := by
  simp only [ResultOk, List.mem_append]
  exact ⟨fun h => ⟨fun t ht => h t (.inl ht), fun t ht => h t (.inr ht)⟩,
    fun h t ht => ht.elim (h.1 t) (h.2 t)⟩

theorem TyOk.addr {Δ : TypeCtx} (a : AddrType) : TyOk Δ a.valType := .num _

/-! ## Contexts -/

theorem Context.initLocals_nil_tm (C : Context) : C.initLocals [] = C := rfl

/-! ## Redex inversion machinery

Everything here avoids `C.Wf` / `C.toTypeCtx.Ok` (which `StateOk` does not
provide: local types need not be valid, and `RECS` is unconstrained). Subtyping
chains are composed only through well-formed middles (`Heaptype_sub/trans`).
-/

namespace TMR

theorem sub_trans_ref {Δ : TypeCtx} {a b c : CRefType} (hb : TyOk Δ b) (hab : Sub Δ a b)
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

theorem sub_trans_val {Δ : TypeCtx} {a b c : CValType} (hb : TyOk Δ b) (hab : Sub Δ a b)
    (hbc : Sub Δ b c) : Sub Δ a c := by
  cases hab with
  | num => exact hbc
  | vec => exact hbc
  | botv => exact .botv
  | refv h1 =>
    cases hb with
    | refv hr =>
      cases hbc with
      | refv h2 => exact .refv (sub_trans_ref hr h1 h2)

theorem resultSub_trans_ok {Δ : TypeCtx} {a b c : List CValType} (hb : ResultOk Δ b)
    (hab : ResultSub Δ a b) (hbc : ResultSub Δ b c) : ResultSub Δ a c := by
  induction hab generalizing c with
  | nil => exact hbc
  | cons h _ ih =>
    cases hbc with
    | cons h' hl' =>
      exact .cons (sub_trans_val (hb _ (by simp)) h h')
        (ih (fun t ht => hb t (by simp [ht])) hl')

theorem subEqR_trans {Δ : TypeCtx} {a b c : CValType} (h₁ : SubEqR Δ a b)
    (h₂ : SubEqR Δ b c) : SubEqR Δ a c := by
  rcases h₁ with rfl | ⟨h₁, hb⟩
  · exact h₂
  rcases h₂ with rfl | ⟨h₂, hc⟩
  · exact .inr ⟨h₁, hb⟩
  exact .inr ⟨sub_trans_val hb h₁ h₂, hc⟩

theorem subEqR_sub {Δ : TypeCtx} {a b c : CValType} (h₁ : SubEqR Δ a b) (h₂ : Sub Δ b c) :
    Sub Δ a c := by
  rcases h₁ with rfl | ⟨h₁, hb⟩
  · exact h₂
  · exact sub_trans_val hb h₁ h₂

theorem forall₂_split {α β : Type _} {R : α → β → Prop} {l : List α}
    {l₁ l₂ : List β} (h : List.Forall₂ R l (l₁ ++ l₂)) :
    ∃ a b, l = a ++ b ∧ List.Forall₂ R a l₁ ∧ List.Forall₂ R b l₂ :=
  ⟨l.take l₁.length, l.drop l₁.length, (List.take_append_drop _ _).symm,
    List.forall₂_take_append l l₁ l₂ h, List.forall₂_drop_append l l₁ l₂ h⟩

theorem initLocals_of_set {C : Context} {xs : List Nat}
    (h : ∀ x ∈ xs, ∃ t, C.locals[x]? = some ⟨.set, t⟩) : C.initLocals xs = C := by
  apply Context.initLocals_eq_locals _ rfl
  intro y
  split
  · next hy =>
    obtain ⟨t, ht⟩ := h y hy
    simp [ht]
  · rfl

theorem val_inv {s : Store H} {C : Context} {v : Val} {it : InstrType}
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

/-- Value sequences, without context well-formedness: well-formed parameters,
only already-set locals as inits, and pushed (well-formed supertypes of) value
types. -/
theorem vals_aux {s : Store H} :
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
    obtain ⟨t, rfl, hv⟩ := val_inv h
    exact ⟨by simp [ResultOk], by simp, [t], .cons hv .nil, forall₂_self (fun _ => .inl rfl) _⟩
  | C, _, _, .cons (t₁ := t₁) (t₂ := t₂) (xs₁ := xs₁) ha _ hs, vs, e => by
    obtain ⟨v, vs', rfl, hv, e'⟩ := List.map_eq_cons_iff.mp e.symm
    subst hv
    obtain ⟨t, hit, hv⟩ := val_inv ha
    obtain ⟨_, hx, ts', hv', r⟩ := vals_aux hs vs' e'.symm
    simp only [InstrType.plain, InstrType.mk.injEq] at hit
    obtain ⟨rfl, rfl, rfl⟩ := hit
    simp only [Context.initLocals_nil] at hx r
    exact ⟨by simp [ResultOk], by simpa using hx, t :: ts', .cons hv hv', r⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, vs, e => by
    obtain ⟨vs₁, vs₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp e.symm
    obtain ⟨p₁, hx₁, ts₁, v₁, r₁⟩ := vals_aux h₁ vs₁ e₁.symm
    have hC : C.initLocals xs₁ = C := initLocals_of_set hx₁
    obtain ⟨_, hx₂, ts₂, v₂, r₂⟩ := vals_aux h₂ vs₂ e₂.symm
    rw [hC] at hx₂ r₂
    refine ⟨p₁, ?_, ts₁ ++ ts₂, forall₂_append v₁ v₂, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hx₁ x h
      · exact hx₂ x h
    rw [← List.append_assoc]
    exact forall₂_comp (forall₂_append r₁ (forall₂_self (fun _ => .inl rfl) ts₂)) r₂
      fun _ _ _ _ _ _ hab hbc => subEqR_trans hab hbc
  | _, _, _, .sub (it := it₀) h hs hok, vs, e => by
    obtain ⟨p, hx, ts, hv, r⟩ := vals_aux h vs e
    refine ⟨hok.1, ?_, ts, hv, ?_⟩
    · intro x hx'
      by_cases hin : x ∈ it₀.inits
      · exact hx x hin
      · exact hs.2.2 x hx' hin
    have h1 : List.Forall₂ (SubEqR _) _ _ :=
      forall₂_append (forall₂_subEqR_of_sub hs.1 p) (forall₂_self (fun _ => .inl rfl) ts)
    exact forall₂_comp (forall₂_comp h1 r fun _ _ _ _ _ _ hab hbc => subEqR_trans hab hbc) hs.2.1
      fun _ _ c _ _ hc hab hbc => subEqR_trans hab (.inr ⟨hbc, hok.2.1 c hc⟩)
  | _, _, _, .frame h hok, vs, e => by
    obtain ⟨p, hx, ts, hv, r⟩ := vals_aux h vs e
    refine ⟨ResultOk.append hok p, hx, ts, hv, ?_⟩
    rw [List.append_assoc]
    exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) r

/-- Typings of the empty sequence do not depend on the store. -/
theorem nil_store {s : Store H} (s' : Store H) : ∀ {C : Context} {as : List Admin}
    {it : InstrType}, AdminsOk s C as it → as = [] → AdminsOk s' C [] it
  | _, _, _, .nil, _ => .nil
  | _, _, _, .single _, he => by simp at he
  | _, _, _, .seq h₁ hx h₂, he => by
    have e := List.append_eq_nil_iff.mp he
    have := AdminsOk.seq (nil_store s' h₁ e.1) hx (nil_store s' h₂ e.2)
    simpa using this
  | _, _, _, .cons _ _ _, he => by simp at he
  | _, _, _, .sub h hs hok, he => .sub (nil_store s' h he) hs hok
  | _, _, _, .frame h hok, he => .frame (nil_store s' h he) hok

/-- A chain of typing steps applicable to any code: `Instrs_ok2/sub`,
`Instrs_ok2/frame`, pre-composition with a typed empty sequence (`pre`) and
post-composition with one (`post`). -/
inductive Lift (H : Type) (C : Context) : InstrType → InstrType → Prop where
  | refl {it : InstrType} : Lift H C it it
  | sub {it₀ it₁ it₂ : InstrType} (h : Lift H C it₀ it₁) (hs : InstrTypeSub C it₁ it₂)
      (hok : InstrTypeOk C it₂) : Lift H C it₀ it₂
  | frame {it₀ : InstrType} {ts p r : List CValType} {x : List Nat}
      (h : Lift H C it₀ ⟨p, x, r⟩) (hok : ResultOk C.toTypeCtx ts) :
      Lift H C it₀ ⟨ts ++ p, x, ts ++ r⟩
  | pre {it₀ : InstrType} {p q r : List CValType} {x y : List Nat}
      (h : Lift H C it₀ ⟨q, y, r⟩) (hs : ResultSub C.toTypeCtx p q)
      (hp : ResultOk C.toTypeCtx p) (hq : ResultOk C.toTypeCtx q)
      (hx : ∀ z ∈ x, ∃ t, C.locals[z]? = some ⟨.set, t⟩) : Lift H C it₀ ⟨p, x ++ y, r⟩
  | post {it₀ : InstrType} {p r r' : List CValType} {x y : List Nat}
      (h : Lift H C it₀ ⟨p, x, r⟩) (hx : ∀ z ∈ x, ∃ lt, C.locals[z]? = some lt)
      (hn : ∀ s' : Store H, AdminsOk s' (C.initLocals x) [] ⟨r, y, r'⟩) :
      Lift H C it₀ ⟨p, x ++ y, r'⟩

theorem Lift.apply {s : Store H} {C : Context} {as : List Admin} {it₀ it : InstrType}
    (hl : Lift H C it₀ it) (h : AdminsOk s C as it₀) : AdminsOk s C as it := by
  induction hl with
  | refl => exact h
  | sub _ hs hok ih => exact .sub ih hs hok
  | frame _ hok ih => exact .frame ih hok
  | @pre p q r x y _ hs hp hq hx ih =>
    have hC : C.initLocals x = C := initLocals_of_set hx
    have hx' : ∀ z ∈ x, ∃ lt, C.locals[z]? = some lt := fun z hz =>
      let ⟨_, ht⟩ := hx z hz; ⟨_, ht⟩
    have e0 : AdminsOk s C [] ⟨p, [], p⟩ := by
      simpa using AdminsOk.frame (s := s) (C := C) (ts := p) AdminsOk.nil hp
    have e : AdminsOk s C [] ⟨p, x, q⟩ :=
      .sub e0 ⟨ResultSub.refl _ _, hs, fun z hz _ => hx z hz⟩ ⟨hp, hq, hx'⟩
    have ih' : AdminsOk s (C.initLocals x) as ⟨q, y, r⟩ := by rw [hC]; exact ih
    simpa using AdminsOk.seq e hx' ih'
  | post _ hx hn ih =>
    simpa using AdminsOk.seq ih hx (hn s)

/-- Dropping operands from the top of the parameter stack. -/
theorem Lift.dropTop {C : Context} {it₀ it : InstrType} (hl : Lift H C it₀ it) :
    ∀ {A B : List CValType}, it₀.params = A ++ B →
    ∃ QA QB, it.params = QA ++ QB ∧ ResultSub C.toTypeCtx QB B ∧
      Lift H C ⟨A, it₀.inits, it₀.results⟩ ⟨QA, it.inits, it.results⟩ ∧
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
    obtain ⟨QA', QB', hp', h₁, h₂⟩ := forall₂_split hs₁
    have hokp : ResultOk C.toTypeCtx (QA' ++ QB') := hp' ▸ hok.1
    refine ⟨QA', QB', hp', ?_, ?_, .inr (resultOk_append.1 hokp).2⟩
    · rcases hinv with rfl | hQ
      · exact h₂
      · exact resultSub_trans_ok hQ h₂ hQB
    · exact .sub hl ⟨h₁, hs₂, hs₃⟩ ⟨(resultOk_append.1 hokp).1, hok.2.1, hok.2.2⟩
  | frame _ hok ih =>
    intro A B he
    obtain ⟨QA, QB, hp, hQB, hl, hinv⟩ := ih he
    simp only at hp
    subst hp
    exact ⟨_, QB, (List.append_assoc _ _ _).symm, hQB, .frame hl hok, hinv⟩
  | pre _ hs hp hq hx ih =>
    intro A B he
    obtain ⟨QA, QB, hp', hQB, hl, hinv⟩ := ih he
    simp only at hp'
    subst hp'
    obtain ⟨PA, PB, rfl, h₁, h₂⟩ := forall₂_split hs
    refine ⟨PA, PB, rfl, ?_, .pre hl h₁ (resultOk_append.1 hp).1 (resultOk_append.1 hq).1 hx,
      .inr (resultOk_append.1 hp).2⟩
    rcases hinv with rfl | hQ
    · exact h₂
    · exact resultSub_trans_ok hQ h₂ hQB
  | post _ hx hn ih =>
    intro A B he
    obtain ⟨QA, QB, hp, hQB, hl, hinv⟩ := ih he
    exact ⟨QA, QB, hp, hQB, .post hl hx hn, hinv⟩

/-- One value-prefix step of the redex inversion. -/
theorem redex_step {s : Store H} {C : Context} {i : Instr} {N : Nat}
    (hI : ∀ it₀, InstrOk C i it₀ →
      it₀.inits = [] ∧ it₀.params.length = N ∧ ResultOk {} it₀.params)
    {vs₁ vs₂ : List Val} {t₁ t₂ t₃ : List CValType} {xs₁ xs₂ : List Nat}
    {ts₁ ts₂ A₂ B₂ R₀ : List CValType}
    (p₁ : ResultOk C.toTypeCtx t₁) (hx₁ : ∀ x ∈ xs₁, ∃ t, C.locals[x]? = some ⟨.set, t⟩)
    (v₁ : List.Forall₂ (ValOk s) vs₁ ts₁)
    (r₁ : List.Forall₂ (SubEqR C.toTypeCtx) (t₁ ++ ts₁) t₂)
    (hp₂ : ResultOk C.toTypeCtx t₂) (hi : InstrOk C i ⟨A₂ ++ B₂, [], R₀⟩)
    (hvs₂ : List.Forall₂ (ValOk s) vs₂ ts₂) (hB₂ : ResultSub C.toTypeCtx ts₂ B₂)
    (hl : Lift H C ⟨A₂, [], R₀⟩ ⟨t₂, xs₂, t₃⟩) (hlen : vs₁.length + vs₂.length ≤ N) :
    ResultOk C.toTypeCtx t₁ ∧ ∃ A B R₀ ts, InstrOk C i ⟨A ++ B, [], R₀⟩ ∧
      List.Forall₂ (ValOk s) (vs₁ ++ vs₂) ts ∧ ResultSub C.toTypeCtx ts B ∧
      Lift H C ⟨A, [], R₀⟩ ⟨t₁, xs₁ ++ xs₂, t₃⟩ := by
  have hN := (hI _ hi).2.1
  simp only [List.length_append] at hN
  have hl₁ := v₁.length_eq
  have hl₂ := hvs₂.length_eq
  have hlB : ts₂.length = B₂.length := List.Forall₂.length_eq hB₂
  obtain ⟨QA, QB, hp, hQB, hl', -⟩ :=
    hl.dropTop (A := A₂.take (A₂.length - vs₁.length)) (B := A₂.drop (A₂.length - vs₁.length))
      (List.take_append_drop _ _).symm
  simp only at hp hl'
  have hQBl : QB.length = _ := List.Forall₂.length_eq hQB
  simp only [List.length_drop] at hQBl
  rw [hp] at r₁
  obtain ⟨X, Y, hXY, hX, hY⟩ := forall₂_split r₁
  have hYl := hY.length_eq
  obtain ⟨rfl, rfl⟩ := List.append_inj' hXY (by omega)
  refine ⟨p₁, A₂.take (A₂.length - vs₁.length), A₂.drop (A₂.length - vs₁.length) ++ B₂, R₀,
    ts₁ ++ ts₂, ?_, forall₂_append v₁ hvs₂, forall₂_append ?_ hB₂, ?_⟩
  · rw [← List.append_assoc, List.take_append_drop]; exact hi
  · exact forall₂_comp hY hQB fun _ _ _ _ _ _ hab hbc => subEqR_sub hab hbc
  · have hQA : ResultOk C.toTypeCtx QA := by
      rw [hp] at hp₂; exact (resultOk_append.1 hp₂).1
    exact .pre hl' (hX.imp fun _ _ h => h.sub) p₁ hQA hx₁

/-- Inversion of a redex `vals vs ++ [plain i]` with `vs.length ≤ N`. -/
theorem redex_aux {s : Store H} {C : Context} {i : Instr} {N : Nat}
    (hI : ∀ it₀, InstrOk C i it₀ →
      it₀.inits = [] ∧ it₀.params.length = N ∧ ResultOk {} it₀.params) :
    ∀ {C' : Context} {as : List Admin} {it : InstrType}, AdminsOk s C' as it → C' = C →
    ∀ vs : List Val, as = vals vs ++ [.plain i] → vs.length ≤ N →
    ResultOk C.toTypeCtx it.params ∧ ∃ A B R₀ ts, InstrOk C i ⟨A ++ B, [], R₀⟩ ∧
      List.Forall₂ (ValOk s) vs ts ∧ ResultSub C.toTypeCtx ts B ∧ Lift H C ⟨A, [], R₀⟩ it
  | _, _, _, .nil, _, vs, he, _ => by simp at he
  | _, _, _, .single (it := it) ha, hC, vs, he, _ => by
    subst hC
    have hl := congrArg List.length he
    simp only [vals, List.length_append, List.length_map,
      List.length_cons, List.length_nil] at hl
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [vals, List.map_nil, List.nil_append, List.cons.injEq, and_true] at he
    subst he
    cases ha.plain_cases with
    | inr h => obtain ⟨rfl, -⟩ := h; exact (InstrOk.throwRef_arity_absurd fun it h => (hI it h).2.1).elim
    | inl hi =>
      obtain ⟨hx, -, hok⟩ := hI _ hi
      obtain ⟨p, x, r⟩ := it
      simp only at hx
      subst hx
      exact ⟨fun t ht => TyOk.of_empty _ (hok t ht), p, [], r, [], by simpa using hi, .nil, .nil,
        .refl⟩
  | _, _, _, .seq (as₁ := as₁) (as₂ := as₂) (xs₁ := xs₁) h₁ hx h₂, hC, vs, he, hlen => by
    rcases List.eq_nil_or_concat as₂ with h2 | ⟨M, last, h2⟩
    · have he' : as₁ = vals vs ++ [.plain i] := by simpa [h2] using he
      obtain ⟨hp, A, B, R₀, ts, hi, hvs, hB, hl⟩ := redex_aux hI h₁ hC vs he' hlen
      subst hC h2
      exact ⟨hp, A, B, R₀, ts, hi, hvs, hB, .post hl hx fun s' => nil_store s' h₂ rfl⟩
    · have he2 := he
      rw [h2, List.concat_eq_append, ← List.append_assoc] at he2
      obtain ⟨e1, e2⟩ := List.append_inj' he2 rfl
      simp only [List.cons.injEq, and_true] at e2
      obtain ⟨vs₁, vs₂, hvs, e₁, e₂⟩ := List.map_eq_append_iff.mp e1.symm
      obtain ⟨p₁, hx₁, ts₁, v₁, r₁⟩ := vals_aux h₁ vs₁ e₁.symm
      have hCe := (initLocals_of_set hx₁).trans hC
      have hlen' : vs₁.length + vs₂.length ≤ N := by subst hvs; simpa using hlen
      obtain ⟨hp₂, A₂, B₂, R₀, ts₂, hi, hvs₂, hB₂, hl⟩ :=
        redex_aux hI h₂ hCe vs₂ (by rw [h2, List.concat_eq_append, e2, ← e₂]; rfl) (by omega)
      subst hC hvs
      exact redex_step hI p₁ hx₁ v₁ r₁ hp₂ hi hvs₂ hB₂ hl hlen'
  | _, _, _, .cons (t₁ := t₁) (t₂ := t₂) (xs₁ := xs₁) ha hx hs, hC, vs, he, hlen => by
    cases vs with
    | nil =>
      subst hC
      simp only [vals, List.map_nil, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      cases ha.plain_cases with
      | inr h => obtain ⟨rfl, -⟩ := h; exact (InstrOk.throwRef_arity_absurd fun it h => (hI it h).2.1).elim
      | inl hi =>
        obtain ⟨hx₁, -, hok⟩ := hI _ hi
        simp only at hx₁
        subst hx₁
        exact ⟨fun t ht => TyOk.of_empty _ (hok t ht), t₁, [], t₂, [], by simpa using hi, .nil,
          .nil, .post .refl hx fun s' => nil_store s' hs rfl⟩
    | cons v vs' =>
      simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at he
      obtain ⟨ha', has'⟩ := he
      obtain ⟨t, hit, hv⟩ := val_inv (ha' ▸ ha)
      simp only [InstrType.plain, InstrType.mk.injEq] at hit
      obtain ⟨ht₁, hxs₁, ht₂⟩ := hit
      simp only [List.length_cons] at hlen
      obtain ⟨hp₂, A₂, B₂, R₀, ts₂, hi, hvs₂, hB₂, hl⟩ :=
        redex_aux hI hs (by rw [hxs₁, Context.initLocals_nil, hC]) vs' has' (by omega)
      subst hC ht₁ hxs₁ ht₂ ha'
      obtain ⟨p₁, hx₁, ts₁, v₁, r₁⟩ := vals_aux (AdminsOk.single ha) [v] rfl
      exact redex_step (vs₁ := [v]) hI p₁ hx₁ v₁ r₁ hp₂ hi hvs₂ hB₂ hl (by simp; omega)
  | _, _, _, .sub h hs hok, hC, vs, he, hlen => by
    obtain ⟨-, A, B, R₀, ts, hi, hvs, hB, hl⟩ := redex_aux hI h hC vs he hlen
    subst hC
    exact ⟨hok.1, A, B, R₀, ts, hi, hvs, hB, .sub hl hs hok⟩
  | _, _, _, .frame h hok, hC, vs, he, hlen => by
    obtain ⟨hp, A, B, R₀, ts, hi, hvs, hB, hl⟩ := redex_aux hI h hC vs he hlen
    subst hC
    exact ⟨ResultOk.append hok hp, A, B, R₀, ts, hi, hvs, hB, .frame hl hok⟩

end TMR

/-! ## Runtime subsumption of operands -/

/-- For every principal typing `P → R` of `i`, an operand whose runtime type is
a subtype, in `C`, of a *reference* parameter type `ref rt` (closed) has runtime
type `ref rt`. This is the invariant `AdminsOk.redex_inv` needs to turn the
operand typings into `ValOk` at the parameters themselves (for numeric and
vector parameters it is automatic). -/
def RedexSubOk (s : Store H) (C : Context) (i : Instr) (vs : List Val) : Prop :=
  ∀ P R, InstrOk C i ⟨P, [], R⟩ → ∀ (k : Nat) (v : Val) (rt : CRefType),
    vs[k]? = some v → P[k]? = some (.refv rt) → ∀ t, ValOk s v t →
    Sub C.toTypeCtx t (.refv rt) → TyOk {} rt → ValOk s v (.refv rt)

/-- Numeric and vector operands are never below a reference type. -/
theorem RedexSubOk.of_nonref {s : Store H} {C : Context} {i : Instr} {vs : List Val}
    (h : ∀ v ∈ vs, ∀ r, v ≠ .ref r) : RedexSubOk s C i vs := by
  intro P R _ k v rt hk _ t hvt hs _
  cases hvt with
  | num n => cases hs
  | vec b => cases hs
  | ref _ => exact absurd rfl (h _ (List.mem_of_getElem? hk) _)

/-- Instructions without reference parameters. -/
theorem RedexSubOk.of_noRefParams {s : Store H} {C : Context} {i : Instr} {vs : List Val}
    (h : ∀ P R, InstrOk C i ⟨P, [], R⟩ → ∀ rt, Ty.refv rt ∉ P) : RedexSubOk s C i vs := by
  intro P R hi _ _ rt _ hP
  exact absurd (List.mem_of_getElem? hP) (h P R hi rt)

theorem noRefParams_memoryFill {C : Context} {x : MemIdx} :
    ∀ P R, InstrOk C (.memoryFill x) ⟨P, [], R⟩ → ∀ rt, Ty.refv rt ∉ P := by
  intro P R h rt hrt
  cases h <;> rename_i h <;> cases h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrt
  rcases hrt with h | h | h <;> cases h

/-- Reference operands at reference parameters: the operand `v : t` with
`Sub C.toTypeCtx t (ref rt)` and `ref rt` closed is a `ValTo` of a closed type, so
`StateOk.valTo_valOk` (`Soundness/ValToClosed.lean`, via the value's principal
runtime type) gives `ValOk s v (ref rt)`. -/
theorem StateOk.redexSubOk {s : Store H} {f : Frame} {C : Context} {i : Instr} {vs : List Val}
    (hst : StateOk s f C) : RedexSubOk s C i vs := by
  intro P R _ k v rt _ _ t hvt hs hok
  exact hst.valTo_valOk ⟨t, hvt, .single hs⟩ (.refv hok)

theorem ValOk.sub_nonref {s : Store H} {Δ : TypeCtx} {v : Val} {t b : CValType}
    (hv : ValOk s v t) (hs : Sub Δ t b) (hb : ∀ rt, b ≠ .refv rt) : ValOk s v b := by
  cases hv with
  | num n => cases hs; exact .num n
  | vec x => cases hs; exact .vec x
  | ref _ => cases hs; exact absurd rfl (hb _)

theorem TMR.forall₂_idx {s : Store H} {Δ : TypeCtx} : ∀ {vs : List Val} {ts B : List CValType},
    (∀ (k : Nat) v b, vs[k]? = some v → B[k]? = some b → ∀ t, ValOk s v t → Sub Δ t b → TyOk {} b →
      ValOk s v b) →
    List.Forall₂ (ValOk s) vs ts → List.Forall₂ (Sub Δ) ts B → ResultOk {} B →
    List.Forall₂ (ValOk s) vs B
  | _, _, _, _, .nil, .nil, _ => .nil
  | v :: _, t :: _, b :: _, hc, .cons hv hvs, .cons hb hB, hok =>
    .cons (hc 0 v b rfl rfl t hv hb (hok b (by simp)))
      (TMR.forall₂_idx (fun k w c h₁ h₂ => hc (k + 1) w c (by simpa using h₁) (by simpa using h₂))
        hvs hB (fun x hx => hok x (by simp [hx])))

/-! ## Subject replacement for a redex -/

/-- **Subject replacement** for a redex `vals vs ++ [plain i]`: if every
principal typing `P → R` of `i` consumes exactly the operands (inits-free, with
`P` valid in the empty context), and the reduct `n` has type `[] → R` whenever
the operands have runtime types `P`, then `n` has every type the redex has.

Statement change (reported): the extra hypothesis `hsub : RedexSubOk s C i vs`
(an auto-parameter, so callers are unchanged). The operand typings only give
`ValOk s v t` with `Sub C.toTypeCtx t p`; for a reference parameter `p`,
turning that into `ValOk s v p` needs runtime types to be closed (the
`StoreOk.structsClosed`/`arraysClosed` deviation). The auto-parameter proves it outright when no operand
is a reference (`RedexSubOk.of_nonref`) or the instruction has no reference
parameters (`RedexSubOk.of_noRefParams`), and otherwise falls back to
`StateOk.redexSubOk`. -/
theorem AdminsOk.redex_inv {s : Store H} {f : Frame} {C : Context} {vs : List Val}
    {i : Instr} {it : InstrType} (_hst : StateOk s f C)
    (hi : ∀ it₀, InstrOk C i it₀ →
      it₀.inits = [] ∧ it₀.params.length = vs.length ∧ ResultOk {} it₀.params)
    (hty : AdminsOk s C (vals vs ++ [.plain i]) it)
    (hsub : RedexSubOk s C i vs := by
      first
        | (apply RedexSubOk.of_nonref; simp [Val.i32, Val.i64]; done)
        | exact RedexSubOk.of_noRefParams noRefParams_memoryFill
        | exact StateOk.redexSubOk ‹StateOk _ _ _›) :
    ∃ P R, InstrOk C i ⟨P, [], R⟩ ∧ List.Forall₂ (ValOk s) vs P ∧
      ∀ (s' : Store H) (n : List Admin), AdminsOk s' C n ⟨[], [], R⟩ → AdminsOk s' C n it := by
  obtain ⟨-, A, B, R₀, ts, hi', hvs, hB, hl⟩ := TMR.redex_aux (H := H) hi hty rfl vs rfl le_rfl
  have hN := (hi _ hi').2.1
  have h1 := hvs.length_eq
  have h2 : ts.length = B.length := List.Forall₂.length_eq hB
  simp only [List.length_append] at hN
  obtain rfl : A = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [List.nil_append] at hi'
  have hBok : ResultOk {} B := by simpa using (hi _ hi').2.2
  refine ⟨B, R₀, hi', TMR.forall₂_idx ?_ hvs hB hBok, fun s' n hn => hl.apply hn⟩
  intro k v b hk hb t hv hs hok
  by_cases hr : ∃ rt, b = .refv rt
  · obtain ⟨rt, rfl⟩ := hr
    exact hsub B R₀ hi' k v rt hk hb t hv hs (by cases hok; assumption)
  · exact hv.sub_nonref hs fun rt e => hr ⟨rt, e⟩

theorem AdminsOk.redex_replace {s s' : Store H} {f : Frame} {C : Context} {vs : List Val}
    {i : Instr} {n : List Admin} {it : InstrType} (hst : StateOk s f C)
    (hi : ∀ it₀, InstrOk C i it₀ →
      it₀.inits = [] ∧ it₀.params.length = vs.length ∧ ResultOk {} it₀.params)
    (hty : AdminsOk s C (vals vs ++ [.plain i]) it)
    (hn : ∀ P R, InstrOk C i ⟨P, [], R⟩ → List.Forall₂ (ValOk s) vs P →
      AdminsOk s' C n ⟨[], [], R⟩)
    (hsub : RedexSubOk s C i vs := by
      first
        | (apply RedexSubOk.of_nonref; simp [Val.i32, Val.i64]; done)
        | exact RedexSubOk.of_noRefParams noRefParams_memoryFill
        | exact StateOk.redexSubOk ‹StateOk _ _ _›) :
    AdminsOk s' C n it := by
  obtain ⟨P, R, hi', hvs, hk⟩ := AdminsOk.redex_inv hst hi hty hsub
  exact hk s' n (hn P R hi' hvs)

/-! ## Inversion helpers -/

theorem AddrType.intType_inj {a b : AddrType} (h : a.intType = b.intType) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem ValOk.addr_eq {s : Store H} {a a' : AddrType} {i : BitVec a.intType.width}
    (h : ValOk s (.num ⟨.int a.intType, i⟩) a'.valType) : a = a' := by
  cases a <;> cases a' <;> first | rfl | (unfold AddrType.valType at h; cases h)

theorem ValOk.num_eq {s : Store H} {t : NumType} {b : BitVec t.width} {t' : CValType}
    (h : ValOk s (.num ⟨t, b⟩) t') : t' = .num t := by
  cases h; rfl

theorem ValOk.ref_eq {s : Store H} {r : Ref} {rt : CRefType} (h : ValOk s (.ref r) (.refv rt)) :
    RefOk s r rt := by
  cases h; assumption

theorem Store.table?_spec {s : Store H} {f : Frame} {x : TableIdx} {a : Nat} {ti : TableInst}
    (h : s.table? f x = some (a, ti)) : f.module.tables[x.toNat]? = some a ∧ s.tables[a]? = some ti := by
  simp only [Store.table?] at h
  cases h₁ : f.module.tables[x.toNat]? with
  | none => simp [h₁] at h
  | some b =>
    cases h₂ : s.tables[b]? with
    | none => simp [h₁, h₂] at h
    | some t =>
      simp [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h₂⟩

theorem Store.mem?_spec {s : Store H} {f : Frame} {x : MemIdx} {a : Nat} {mi : MemInst}
    (h : s.mem? f x = some (a, mi)) : f.module.mems[x.toNat]? = some a ∧ s.mems[a]? = some mi := by
  simp only [Store.mem?] at h
  cases h₁ : f.module.mems[x.toNat]? with
  | none => simp [h₁] at h
  | some b =>
    cases h₂ : s.mems[b]? with
    | none => simp [h₁, h₂] at h
    | some t =>
      simp [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h₂⟩

/-! ## Straight-line stack programs -/

/-- `as` pushes `ts` onto an empty stack. -/
abbrev SeqOk (s : Store H) (C : Context) (as : List Admin) (ts : List CValType) : Prop :=
  AdminsOk s C as ⟨[], [], ts⟩

theorem AdminsOk.nil_frame {s : Store H} {C : Context} {ts : List CValType}
    (h : ResultOk C.toTypeCtx ts) : AdminsOk s C [] ⟨ts, [], ts⟩ := by
  have := AdminsOk.frame (s := s) (ts := ts) AdminsOk.nil h
  simpa using this

theorem ValOk.adminOk {s : Store H} {C : Context} {v : Val} {t : CValType} (h : ValOk s v t) :
    AdminOk s C v.toAdmin ⟨[], [], [t]⟩ := by
  cases h with
  | num v =>
    rcases v with ⟨_ | _, b⟩
    · exact .plain (.numeric (.intConst _ b))
    · exact .plain (.numeric (.floatConst _ b))
  | vec b => exact .plain (.vector (.vecConst b))
  | ref h => exact .ref h

theorem SeqOk.nil {s : Store H} {C : Context} : SeqOk s C [] [] := AdminsOk.nil

theorem AdminsOk.singleR {s : Store H} {C : Context} {a : Admin} {P R : List CValType}
    (h : AdminOk s C a ⟨P, [], R⟩) (hR : ResultOk C.toTypeCtx R) :
    AdminsOk s C [a] ⟨P, [], R⟩ :=
  AdminsOk.cons (xs₁ := []) (xs₂ := []) h (by simp) (AdminsOk.nil_frame hR)

/-- Append a typed sequence `P → R` on top of a stack `pre ++ P`. -/
theorem SeqOk.then {s : Store H} {C : Context} {as bs : List Admin}
    {pre P R : List CValType} (h : SeqOk s C as (pre ++ P)) (hpre : ResultOk C.toTypeCtx pre)
    (hb : AdminsOk s C bs ⟨P, [], R⟩) : SeqOk s C (as ++ bs) (pre ++ R) := by
  have hb' := AdminsOk.frame (ts := pre) hb hpre
  have := AdminsOk.append (xs₁ := []) (xs₂ := []) h (by simp) hb'
  simpa using this

theorem SeqOk.val {s : Store H} {C : Context} {as : List Admin} {ts : List CValType}
    {v : Val} {t : CValType} (h : SeqOk s C as ts) (hts : ResultOk C.toTypeCtx ts)
    (hv : ValOk s v t) (ht : TyOk C.toTypeCtx t) : SeqOk s C (as ++ [v.toAdmin]) (ts ++ [t]) :=
  SeqOk.then (P := []) (by simpa using h) hts
    (AdminsOk.singleR hv.adminOk (resultOk_cons.2 ⟨ht, resultOk_nil⟩))

theorem SeqOk.ref {s : Store H} {C : Context} {as : List Admin} {ts : List CValType}
    {r : Ref} {rt : CRefType} (h : SeqOk s C as ts) (hts : ResultOk C.toTypeCtx ts)
    (hr : RefOk s r rt) (ht : TyOk C.toTypeCtx rt) :
    SeqOk s C (as ++ [.ref r]) (ts ++ [.refv rt]) :=
  SeqOk.val (v := .ref r) h hts (.ref hr) (.refv ht)

theorem SeqOk.instr {s : Store H} {C : Context} {as : List Admin} {pre P R : List CValType}
    {i : Instr} (h : SeqOk s C as (pre ++ P)) (hpre : ResultOk C.toTypeCtx pre)
    (hi : InstrOk C i ⟨P, [], R⟩) (hR : ResultOk C.toTypeCtx R) :
    SeqOk s C (as ++ [.plain i]) (pre ++ R) :=
  SeqOk.then h hpre (AdminsOk.singleR (.plain hi) hR)

theorem SeqOk.trap {s : Store H} {C : Context} {R : List CValType}
    (hR : ResultOk C.toTypeCtx R) : SeqOk s C [.trap] R :=
  AdminsOk.singleR (.trap ⟨resultOk_nil, hR, by simp⟩) hR

theorem SeqOk.sub {s : Store H} {C : Context} {as : List Admin} {ts ts' : List CValType}
    (h : SeqOk s C as ts) (hs : ResultSub C.toTypeCtx ts ts') (hok : ResultOk C.toTypeCtx ts') :
    SeqOk s C as ts' :=
  AdminsOk.sub h ⟨.nil, hs, by simp⟩ ⟨resultOk_nil, hok, by simp⟩

/-! ## Store extension (local copies, namespaced to avoid clashes) -/

namespace TM

theorem extendsList_get {α : Type} {R : α → α → Prop} {l l' : List α} (h : ExtendsList R l l')
    {i : Nat} {x : α} (hx : l[i]? = some x) : ∃ y, l'[i]? = some y ∧ R x y := h.2 i x hx

theorem extendsList_set {α : Type} {R : α → α → Prop} {l : List α} {a : Nat} {x₀ y : α}
    (hrefl : ∀ x ∈ l, R x x) (ha : l[a]? = some x₀) (hR : R x₀ y) :
    ExtendsList R l (l.set a y) := by
  refine ⟨by simp, fun i x hx => ?_⟩
  by_cases hia : a = i
  · subst hia
    rw [ha] at hx; cases hx
    have hlt : a < l.length := (List.getElem?_eq_some_iff.1 ha).1
    exact ⟨y, by simp [hlt], hR⟩
  · exact ⟨x, by simp [hia, hx], hrefl x (List.mem_of_getElem? hx)⟩

theorem extendsList_modify {α : Type} {R : α → α → Prop} {l : List α} {a : Nat} {g : α → α}
    (hrefl : ∀ x ∈ l, R x x) (hR : ∀ x, l[a]? = some x → R x (g x)) :
    ExtendsList R l (l.modify a g) := by
  refine ⟨by simp, fun i x hx => ?_⟩
  by_cases hia : a = i
  · subst hia
    exact ⟨g x, by simp [hx], hR x hx⟩
  · exact ⟨x, by simp [hia, hx], hrefl x (List.mem_of_getElem? hx)⟩

theorem valOk_extend {s s' : Store H} {v : Val} {t : CValType} (he : Extend s s')
    (h : ValOk s v t) : ValOk s' v t := by
  cases h with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref h => exact .ref (h.extend he)

theorem fieldValOk_extend {s s' : Store H} {v : FieldVal} {t : CStorageType} (he : Extend s s')
    (h : FieldValOk s v t) : FieldValOk s' v t := by
  cases h with
  | val h => exact .val (valOk_extend he h)
  | pack p b => exact .pack p b

theorem subRefRefl (Δ : TypeCtx) (rt : CRefType) : Sub Δ rt rt := by
  cases rt with
  | ref n h => cases n
               · exact .refNonNull .heapRefl
               · exact .refNull .heapRefl

theorem limitsSub_of_grow {l l' : Limits} (hmax : l.max = l'.max) (hmin : l.min.val ≤ l'.min.val) :
    LimitsSub l' l := by
  rcases l with ⟨n, m⟩
  rcases l' with ⟨n', m'⟩
  simp only at hmax hmin
  subst hmax
  cases m with
  | none => exact .eps hmin
  | some m => exact .max hmin (fun _ e => by cases e; exact Nat.le_refl _)

theorem externAddrOk_extend {s s' : Store H} {xa : ExternAddr} {xt : CExternType}
    (hs : StoreOk s) (he : Extend s s') (h : ExternAddrOk s xa xt) : ExternAddrOk s' xa xt := by
  induction h with
  | tag h =>
    obtain ⟨ti', h', hx⟩ := extendsList_get he.tags h
    cases hx; exact .tag h'
  | global h =>
    obtain ⟨gi', h', hx⟩ := extendsList_get he.globals h
    have := ExternAddrOk.global (s := s') h'
    rwa [← hx.1] at this
  | @mem a mi h =>
    obtain ⟨mi', h', ha, hmax, hmin, _⟩ := extendsList_get he.mems h
    refine .sub (.mem h') (.mem (hs.mems mi (List.mem_of_getElem? h)).1) (.mem ?_)
    rcases hmt : mi.type with ⟨at₁, l₁⟩
    rcases hmt' : mi'.type with ⟨at₂, l₂⟩
    rw [hmt, hmt'] at ha hmax hmin
    simp only at ha hmax hmin
    subst ha
    exact .mk (limitsSub_of_grow hmax hmin)
  | @table a ti h =>
    obtain ⟨ti', h', ha, hmax, hel, hmin, _⟩ := extendsList_get he.tables h
    refine .sub (.table h') (.table (hs.tables ti (List.mem_of_getElem? h)).1) (.table ?_)
    rcases hmt : ti.type with ⟨at₁, l₁, r₁⟩
    rcases hmt' : ti'.type with ⟨at₂, l₂, r₂⟩
    rw [hmt, hmt'] at ha hmax hel hmin
    simp only at ha hmax hel hmin
    subst ha; subst hel
    exact .mk (limitsSub_of_grow hmax hmin) (subRefRefl _ _)
      (subRefRefl _ _)
  | func h =>
    obtain ⟨fi', h', hx⟩ := extendsList_get he.funcs h
    have := ExternAddrOk.func (s := s') h'
    rwa [← hx.1] at this
  | sub _ hok hsub ih => exact .sub ih hok hsub

theorem externAddrOk_exists_type {s s' : Store H} {xa : ExternAddr} {xt : CExternType}
    (he : Extend s s') (h : ExternAddrOk s xa xt) : ∃ xt', ExternAddrOk s' xa xt' := by
  induction h with
  | tag h => obtain ⟨_, h', _⟩ := extendsList_get he.tags h; exact ⟨_, .tag h'⟩
  | global h => obtain ⟨_, h', _⟩ := extendsList_get he.globals h; exact ⟨_, .global h'⟩
  | mem h => obtain ⟨_, h', _⟩ := extendsList_get he.mems h; exact ⟨_, .mem h'⟩
  | table h => obtain ⟨_, h', _⟩ := extendsList_get he.tables h; exact ⟨_, .table h'⟩
  | func h => obtain ⟨_, h', _⟩ := extendsList_get he.funcs h; exact ⟨_, .func h'⟩
  | sub _ _ _ ih => exact ih

theorem elemInstOk_extend {s s' : Store H} {ei ei' : ElemInst} (he : Extend s s')
    (hx : ExtendElem ei ei') (h : ElemInstOk s ei) : ElemInstOk s' ei' := by
  obtain ⟨ht, hr⟩ := hx
  refine ⟨ht ▸ h.1, fun r hr' => ?_⟩
  rw [← ht]
  rcases hr with hr | hr
  · rw [← hr] at hr'; exact (h.2 r hr').extend he
  · rw [hr] at hr'; cases hr'

theorem moduleInstOk_extend {s s' : Store H} {mi : ModuleInst} {C : Context} (hs : StoreOk s)
    (he : Extend s s') (h : ModuleInstOk s mi C) : ModuleInstOk s' mi C := by
  cases h with
  | mk htypes htags hglobals hfuncs hmems htables hdatas helems hexports hdisjoint hexportAddrs hk =>
    refine .mk htypes (htags.imp fun _ _ h => externAddrOk_extend hs he h)
      (hglobals.imp fun _ _ h => externAddrOk_extend hs he h)
      (hfuncs.imp fun _ _ h => externAddrOk_extend hs he h)
      (hmems.imp fun _ _ h => externAddrOk_extend hs he h)
      (htables.imp fun _ _ h => externAddrOk_extend hs he h)
      (fun a ha => ?_) (helems.imp fun _ _ h => ?_) (fun xi hxi => ?_) hdisjoint hexportAddrs hk
    · obtain ⟨di, hdi⟩ := hdatas a ha
      obtain ⟨di', h', _⟩ := extendsList_get he.datas hdi
      exact ⟨di', h'⟩
    · obtain ⟨ei, hei, hok, rfl⟩ := h
      obtain ⟨ei', h', hx⟩ := extendsList_get he.elems hei
      exact ⟨ei', h', elemInstOk_extend he hx hok, hx.1.symm⟩
    · obtain ⟨xt, hxt⟩ := hexports xi hxi
      exact externAddrOk_exists_type he hxt

theorem immutReachable_transfer {s s' : Store H} (hstructs : s'.structs = s.structs)
    (harrays : s'.arrays = s.arrays) (hexns : s'.exns = s.exns) {a b : FieldVal}
    (h : ImmutReachable s' a b) : ImmutReachable s a b := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct (hstructs ▸ hs) he hi hfv
  | refArray hs he hfv => exact .refArray (harrays ▸ hs) he hfv
  | refExn hs hv => exact .refExn (hexns ▸ hs) hv
  | refExtern r => exact .refExtern r

/-- A store that extends a valid store, changes only memories, tables, element
and data segments, and whose memories, tables and element segments are valid,
is valid. -/
theorem storeOk_transfer {s s' : Store H} (hs : StoreOk s) (he : Extend s s')
    (htags : s'.tags = s.tags) (hglobals : s'.globals = s.globals) (hfuncs : s'.funcs = s.funcs)
    (hstructs : s'.structs = s.structs) (harrays : s'.arrays = s.arrays)
    (hexns : s'.exns = s.exns)
    (hmems : ∀ mi ∈ s'.mems, MemInstOk mi) (htables : ∀ ti ∈ s'.tables, TableInstOk s' ti)
    (helems : ∀ ei ∈ s'.elems, ElemInstOk s' ei) : StoreOk s' where
  tags ti h := hs.tags ti (htags ▸ h)
  globals gi h := by
    obtain ⟨h₁, h₂⟩ := hs.globals gi (hglobals ▸ h)
    exact ⟨h₁, valOk_extend he h₂⟩
  mems := hmems
  tables := htables
  funcs fi h := by
    cases hs.funcs fi (hfuncs ▸ h) with
    | wasm hdt hm hcode hf hsub => exact .wasm hdt (moduleInstOk_extend hs he hm) hcode hf hsub
    | host hdt he' hcode => exact .host hdt he' hcode
  elems := helems
  structs si h := by
    obtain ⟨fs, hx, hf⟩ := hs.structs si (hstructs ▸ h)
    exact ⟨fs, hx, hf.imp fun _ _ h => fieldValOk_extend he h⟩
  arrays ai h := by
    obtain ⟨ft, hx, hf⟩ := hs.arrays ai (harrays ▸ h)
    exact ⟨ft, hx, fun fv hfv => fieldValOk_extend he (hf fv hfv)⟩
  exns e h := by
    obtain ⟨ti, ts, ht, hx, hf⟩ := hs.exns e (hexns ▸ h)
    exact ⟨ti, ts, htags ▸ ht, hx, hf.imp fun _ _ h => valOk_extend he h⟩
  acyclicStructs a ha hr := hs.acyclicStructs a (hstructs ▸ ha)
    (immutReachable_transfer hstructs harrays hexns hr)
  acyclicArrays a ha hr := hs.acyclicArrays a (harrays ▸ ha)
    (immutReachable_transfer hstructs harrays hexns hr)
  acyclicExns a ha hr := hs.acyclicExns a (hexns ▸ ha)
    (immutReachable_transfer hstructs harrays hexns hr)
  structsClosed si h := hs.structsClosed si (hstructs ▸ h)
  arraysClosed ai h := hs.arraysClosed ai (harrays ▸ h)

theorem tableInstOk_extend {s s' : Store H} {ti : TableInst} (he : Extend s s')
    (h : TableInstOk s ti) : TableInstOk s' ti :=
  ⟨h.1, h.2.1, fun r hr => (h.2.2 r hr).extend he⟩

end TM

/-! ## Store updates -/

theorem ExtendTable.refl (ti : TableInst) : ExtendTable ti ti :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem ExtendMem.refl (mi : MemInst) : ExtendMem mi mi :=
  ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem StoreOk.setTable {s : Store H} {a : Nat} {ti ti' : TableInst} (hs : StoreOk s)
    (ha : s.tables[a]? = some ti) (hx : ExtendTable ti ti') (hok : TableInstOk s ti') :
    StoreOk (s.setTable a ti') ∧ Extend s (s.setTable a ti') := by
  have he : Extend s (s.setTable a ti') :=
    { Extend.refl hs with
      tables := TM.extendsList_set (fun x _ => ExtendTable.refl x) ha hx }
  refine ⟨TM.storeOk_transfer hs he rfl rfl rfl rfl rfl rfl hs.mems (fun tj htj => ?_)
    (fun ej hej => TM.elemInstOk_extend he ⟨rfl, .inl rfl⟩ (hs.elems ej hej)), he⟩
  simp only [Store.setTable] at htj
  rcases List.mem_or_eq_of_mem_set htj with htj | rfl
  · exact TM.tableInstOk_extend he (hs.tables tj htj)
  · exact TM.tableInstOk_extend he hok

theorem StoreOk.setMem {s : Store H} {a : Nat} {mi mi' : MemInst} (hs : StoreOk s)
    (ha : s.mems[a]? = some mi) (hx : ExtendMem mi mi') (hok : MemInstOk mi') :
    StoreOk (s.setMem a mi') ∧ Extend s (s.setMem a mi') := by
  have he : Extend s (s.setMem a mi') :=
    { Extend.refl hs with
      mems := TM.extendsList_set (fun x _ => ExtendMem.refl x) ha hx }
  refine ⟨TM.storeOk_transfer hs he rfl rfl rfl rfl rfl rfl (fun mj hmj => ?_)
    (fun tj htj => TM.tableInstOk_extend he (hs.tables tj htj))
    (fun ej hej => TM.elemInstOk_extend he ⟨rfl, .inl rfl⟩ (hs.elems ej hej)), he⟩
  simp only [Store.setMem] at hmj
  rcases List.mem_or_eq_of_mem_set hmj with hmj | rfl
  · exact hs.mems mj hmj
  · exact hok

theorem StoreOk.setElem_nil {s : Store H} {a : Nat} (hs : StoreOk s) :
    StoreOk (s.setElem a []) ∧ Extend s (s.setElem a []) := by
  have he : Extend s (s.setElem a []) :=
    { Extend.refl hs with
      elems := TM.extendsList_modify (fun x _ => ⟨rfl, .inl rfl⟩) (fun _ _ => ⟨rfl, .inr rfl⟩) }
  refine ⟨TM.storeOk_transfer hs he rfl rfl rfl rfl rfl rfl hs.mems
    (fun tj htj => TM.tableInstOk_extend he (hs.tables tj htj)) (fun ej hej => ?_), he⟩
  simp only [Store.setElem] at hej
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hej
  rw [List.getElem_modify]
  split
  · exact ⟨(hs.elems _ (List.getElem_mem _)).1, fun r hr => by simp at hr⟩
  · exact TM.elemInstOk_extend he ⟨rfl, .inl rfl⟩ (hs.elems _ (List.getElem_mem _))

theorem StoreOk.setData_empty {s : Store H} {a : Nat} (hs : StoreOk s) :
    StoreOk (s.setData a ByteArray.empty) ∧ Extend s (s.setData a ByteArray.empty) := by
  have he : Extend s (s.setData a ByteArray.empty) :=
    { Extend.refl hs with
      datas := TM.extendsList_modify (fun x _ => .inl rfl) (fun _ _ => .inr rfl) }
  exact ⟨TM.storeOk_transfer hs he rfl rfl rfl rfl rfl rfl hs.mems
    (fun tj htj => TM.tableInstOk_extend he (hs.tables tj htj))
    (fun ej hej => TM.elemInstOk_extend he ⟨rfl, .inl rfl⟩ (hs.elems ej hej)), he⟩

/-! ## Growing tables and memories -/

theorem AddrType.width_le (a : AddrType) : a.width ≤ 64 := by
  cases a <;> decide

theorem TableInst.grow?_ok {s : Store H} {ti ti' : TableInst} {n : Nat} {r : Ref}
    (hok : TableInstOk s ti) (hr : RefOk s r ti.type.element) (hg : ti.grow? n r = some ti') :
    TableInstOk s ti' ∧ ExtendTable ti ti' := by
  unfold TableInst.grow? at hg
  dsimp only at hg
  split at hg
  · rename_i hc
    cases hg
    obtain ⟨⟨⟨hmin, hmax⟩, htyok⟩, hlen, hrefs⟩ := hok
    have hw := AddrType.width_le ti.type.address
    have hpow : 2 ^ ti.type.address.width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
    have hv : (Fin.ofNat (2 ^ 64) (ti.refs.length + n)).val = ti.refs.length + n := by
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨⟨⟨?_, ?_⟩, htyok⟩, ?_, ?_⟩, ⟨rfl, rfl, rfl, ?_, ?_⟩⟩
    · simp only [hv]; exact hc.1
    · simp only
      revert hmax
      cases hm : ti.type.limits.max with
      | none => intro _; trivial
      | some m => intro hmax; exact ⟨by simp only [hv]; exact hc.2 m hm, hmax.2⟩
    · simp only [List.length_append, List.length_replicate]; exact hv.symm
    · intro r' hr'
      simp only [List.mem_append, List.mem_replicate] at hr'
      rcases hr' with hr' | ⟨_, rfl⟩
      · exact hrefs r' hr'
      · exact hr
    · simp only [hv]; omega
    · simp
  · cases hg

theorem MemInst.grow?_ok {mi mi' : MemInst} {n : Nat} (hok : MemInstOk mi)
    (hg : mi.grow? n = some mi') : MemInstOk mi' ∧ ExtendMem mi mi' := by
  unfold MemInst.grow? at hg
  dsimp only at hg
  split at hg
  · rename_i hc
    cases hg
    obtain ⟨⟨hmin, hmax⟩, hsize⟩ := hok
    have hw := AddrType.width_le mi.type.address
    have hpow : 2 ^ (mi.type.address.width - 16) < 2 ^ 64 :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have hps : mi.bytes.size / Memory.pageSize = mi.type.limits.min.val := by
      rw [hsize]; simp [Memory.pageSize]
    have hv : (Fin.ofNat (2 ^ 64) (mi.bytes.size / Memory.pageSize + n)).val =
        mi.bytes.size / Memory.pageSize + n := by
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨rfl, rfl, ?_, ?_⟩⟩
    · simp only [hv]; exact hc.1
    · simp only
      revert hmax
      cases hm : mi.type.limits.max with
      | none => intro _; trivial
      | some m => intro hmax; exact ⟨by simp only [hv]; exact hc.2 m hm, hmax.2⟩
    · have hrep : (ByteArray.mk (Array.replicate (n * Memory.pageSize) (0 : UInt8))).size =
          n * Memory.pageSize := by simp [ByteArray.size]
      rw [ByteArray.size_append, hrep, hv, hps, hsize, Nat.add_mul]
    · simp only [hv]; omega
    · simp [ByteArray.size_append]
  · cases hg

/-! ## Tactic support -/

/-- Close a `ResultOk` goal for a literal list of number, vector and reference
types (reference types need their `TyOk` in the local context). -/
macro "rok" : tactic => `(tactic| (
  simp only [resultOk_cons, resultOk_nil, resultOk_append, and_true, List.nil_append,
    List.cons_append]
  repeat' constructor
  all_goals (first | exact .num _ | exact .vec _ | exact TyOk.addr _ | assumption |
    (apply TyOk.refv; assumption))))

theorem SeqOk.addr {s : Store H} {C : Context} {as : List Admin} {ts : List CValType}
    (h : SeqOk s C as ts) (a : AddrType) (i : BitVec a.intType.width)
    (hts : ResultOk C.toTypeCtx ts := by rok) :
    SeqOk s C (as ++ [aconst a i]) (ts ++ [a.valType]) :=
  SeqOk.val (v := .num ⟨.int a.intType, i⟩) h hts (.num _) (TyOk.addr a)

theorem SeqOk.i32 {s : Store H} {C : Context} {as : List Admin} {ts : List CValType}
    (h : SeqOk s C as ts) (i : BitVec 32) (hts : ResultOk C.toTypeCtx ts := by rok) :
    SeqOk s C (as ++ [constI32 i]) (ts ++ [Ty.i32]) :=
  SeqOk.val (v := Val.i32 i) h hts (.num _) (.num _)

theorem SeqOk.v {s : Store H} {C : Context} {as : List Admin} {ts : List CValType}
    {v : Val} {t : CValType} (h : SeqOk s C as ts) (hv : ValOk s v t)
    (ht : TyOk C.toTypeCtx t) (hts : ResultOk C.toTypeCtx ts := by rok) :
    SeqOk s C (as ++ [v.toAdmin]) (ts ++ [t]) :=
  SeqOk.val h hts hv ht

theorem SeqOk.ins {s : Store H} {C : Context} {as : List Admin} {i : Instr}
    (pre P : List CValType) {R : List CValType}
    (h : SeqOk s C as (pre ++ P)) (hi : InstrOk C i ⟨P, [], R⟩)
    (hpre : ResultOk C.toTypeCtx pre := by rok) (hR : ResultOk C.toTypeCtx R := by rok) :
    SeqOk s C (as ++ [.plain i]) (pre ++ R) :=
  SeqOk.instr h hpre hi hR

end Silmaril.Wasm.Execution.Core
