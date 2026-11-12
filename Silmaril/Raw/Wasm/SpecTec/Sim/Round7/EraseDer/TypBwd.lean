module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.TypFwd

/-!
# Round 7, typing across erasure: the backward direction (unrefined)

`tBwdAt`: if a member of the typing block answers `true` at fuel `n` on the erased values in the
erased scope, it answers `true` at fuel `n + K` on the original values, on checked types and
swap-set values. The shift `K` is the fuel at which the export lists of the swap set's records are
typed (`QExp K Q`): that is the one place where the erased side, which sees `[]`, says nothing
about the original. The proof mirrors `Round7/EraseDer/TypFwd.lean`; results of the evaluator
are moved up to the shifted fuel by monotonicity (`Sem.monoAt_of_le`, `Sem.monoTypAt_of_le`).

`typBwd_utf8Env` is `TypBwd` at round 7's environment, given `QExp K Q`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (Hyps SG ER eraseAt ArgIn grE gdE xExp xPrems xArgs
  xIter)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyB)

variable {Q : Value → Prop} {B : Builtins}

/-- The type `exportinst*`. -/
abbrev expT : Typ := .iterT (.varT "exportinst" []) .list

/-- **The export lists of the records of `Q` are typed at fuel `K`**, in the empty scope. -/
def QExp (B : Builtins) (K : Nat) (Q : Value → Prop) : Prop :=
  ∀ r, Q r → ∀ gs, r = .struct gs → ∀ u, ("EXPORTS", u) ∈ gs →
    hasTyp K (utf8Env B) VarEnv.empty expT u = .ok true

/-- A list of record fields declares `EXPORTS`. -/
def fsExp (fs : List TypField) : Bool := fs.any fun f => match f with | .mk a _ _ _ => a == "EXPORTS"

/-- **The typing block comes back from the erased side at fuel `n`**, shifted by `K`. -/
structure TBwdAt (Q : Value → Prop) (B : Builtins) (K n : Nat) : Prop where
  typ : ∀ ρ ρ' t v, TRel Q (freeTyp t) ρ ρ' → XT ρ → xTy tyB t = true → AllIn Q v →
    hasTyp n (utf8Env B) ρ' t (eraseV v) = .ok true → hasTyp (n + K) (utf8Env B) ρ t v = .ok true
  tup : ∀ ρ ρ' bs vs, TRel Q (freeTypBinds bs) ρ ρ' → XT ρ → xTyBinds tyB bs = true →
    (∀ v ∈ vs, AllIn Q v) → hasTypTup n (utf8Env B) ρ' bs (vs.map eraseV) = .ok true →
    hasTypTup (n + K) (utf8Env B) ρ bs vs = .ok true
  list : ∀ ρ ρ' t vs, TRel Q (freeTyp t) ρ ρ' → XT ρ → xTy tyB t = true →
    (∀ v ∈ vs, AllIn Q v) → hasTypList n (utf8Env B) ρ' t (vs.map eraseV) = .ok true →
    hasTypList (n + K) (utf8Env B) ρ t vs = .ok true
  defTyp : ∀ ρ dt v, SG Q gdE ρ → XT ρ → xDefTyp tyB dt = true →
    (defTypExp dt = true → ρ = VarEnv.empty) → AllIn Q v →
    hasTypDef n (utf8Env B) (eraseScope ρ) dt (eraseV v) = .ok true →
    hasTypDef (n + K) (utf8Env B) ρ dt v = .ok true
  fields : ∀ ρ fs gs, SG Q gdE ρ → XT ρ → xTFields tyB fs = true → (∀ p ∈ gs, AllIn Q p.2) →
    (∀ u, ("EXPORTS", u) ∈ gs → fsExp fs = true → hasTyp K (utf8Env B) ρ expT u = .ok true) →
    hasTypFields n (utf8Env B) (eraseScope ρ) fs (eraseVf gs) = .ok true →
    hasTypFields (n + K) (utf8Env B) ρ fs gs = .ok true
  case : ∀ ρ cs op w, SG Q gdE ρ → XT ρ → xTCases tyB cs = true → AllIn Q w →
    hasTypCase n (utf8Env B) (eraseScope ρ) cs op (eraseV w) = .ok true →
    hasTypCase (n + K) (utf8Env B) ρ cs op w = .ok true
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgIn Q gdE w) → (∀ w ∈ ws, ArgTyX w) →
    xInsts tyB insts = true → AllIn Q v →
    hasTypInsts n (utf8Env B) insts (ws.map eraseA) (eraseV v) = .ok true →
    hasTypInsts (n + K) (utf8Env B) insts ws v = .ok true

theorem tBwdAt_zero (K : Nat) : TBwdAt Q B K 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (simp only [hasTyp] at *; contradiction)
    | (simp only [hasTypTup] at *; contradiction)
    | (simp only [hasTypList] at *; contradiction)
    | (simp only [hasTypDef] at *; contradiction)
    | (simp only [hasTypFields] at *; contradiction)
    | (simp only [hasTypCase] at *; contradiction)
    | (simp only [hasTypInsts] at *; contradiction)

theorem evalExp_up {n K : Nat} {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : evalExp n env ρ e = .ok v) : evalExp (n + K) env ρ e = .ok v :=
  evalExp_ok_of_le (Nat.le_add_right n K) h

theorem evalArgs_up {n K : Nat} {env : Env} {ρ : VarEnv} {l : List Arg} {ws : List ArgV}
    (h : evalArgs n env ρ l = .ok ws) : evalArgs (n + K) env ρ l = .ok ws :=
  evalArgs_ok_of_le (Nat.le_add_right n K) h

theorem premsOk_up {n K : Nat} {env : Env} {ρ : VarEnv} {prems : List Prem} {b : Bool}
    (h : premsOk n env ρ prems = .ok b) : premsOk (n + K) env ρ prems = .ok b :=
  (premsOk_le (Nat.le_add_right n K) env ρ prems).ok h

theorem hasTyp_up {m n : Nat} {env : Env} {ρ : VarEnv} {t : Typ} {v : Value} (hmn : m ≤ n)
    (h : hasTyp m env ρ t v = .ok true) : hasTyp n env ρ t v = .ok true :=
  hasTyp_ok_of_le hmn h

theorem matchArgs_nil_pats {n : Nat} {env : Env} {ρ ρ' : VarEnv} {ws : List ArgV}
    (h : matchArgs n env ρ [] ws = .ok ρ') : ρ' = ρ := by
  rcases n with _ | n
  · simp [matchArgs] at h
  · cases ws <;> simp [matchArgs] at h; exact h.symm

theorem fsExp_of_struct {fs : List TypField} (h : fsExp fs = true) :
    defTypExp (.structT fs) = true := h

section Step

set_option linter.unusedSectionVars false

variable (H : Hyps Q grE gdE (utf8Env B)) {K m : Nat} (ih : TBwdAt Q B K m)
include H ih

/-- `hasTyp`, one step back. -/
theorem tb_typ : ∀ ρ ρ' t v, TRel Q (freeTyp t) ρ ρ' → XT ρ → xTy tyB t = true → AllIn Q v →
    hasTyp (m + 1) (utf8Env B) ρ' t (eraseV v) = .ok true →
    hasTyp (m + 1 + K) (utf8Env B) ρ t v = .ok true := by
  intro ρ ρ' t v hR hX ht hv h
  rw [Nat.add_right_comm]
  cases t with
  | boolT => simpa [hasTyp, asBool?_eraseV] using h
  | numT t => simpa [hasTyp, asNum?_eraseV] using h
  | textT => simpa [hasTyp, asText?_eraseV] using h
  | tupT bs =>
    simp only [xTy] at ht
    simp only [hasTyp, asTuple?_eraseV] at h ⊢
    cases hvt : v.asTuple? with
    | none => rw [hvt] at h; cases h
    | some vs =>
      rw [hvt] at h
      have hvs : ∀ w ∈ vs, AllIn Q w := by
        cases v <;> simp [Value.asTuple?] at hvt
        subst hvt; exact fun w hw => EraseAll.allIn_tuple_mem hv w hw
      exact ih.tup _ _ _ _ hR hX ht hvs h
  | iterT t it =>
    simp only [xTy, Bool.and_eq_true] at ht
    have hRt := hR.mono (freeTyp_iter_t t it)
    cases it with
    | opt =>
      simp only [hasTyp, asOpt?_eraseV] at h ⊢
      cases hvo : v.asOpt? with
      | none => rw [hvo] at h; cases h
      | some o =>
        rw [hvo] at h
        cases o with
        | none => rfl
        | some w =>
          have hw : AllIn Q w := by
            rcases v with _ | _ | _ | _ | _ | _ | _ | (_ | w') <;> simp [Value.asOpt?] at hvo
            subst hvo; exact hv
          exact ih.typ _ _ _ _ hRt hX ht.1 hw h
    | list =>
      simp only [hasTyp, asList?_eraseV] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        have hvs : ∀ w ∈ vs, AllIn Q w := by
          cases v <;> simp [Value.asList?] at hvl
          subst hvl; exact fun w hw => EraseAll.allIn_list_mem hv w hw
        exact ih.list _ _ _ _ hRt hX ht.1 hvs h
    | list1 =>
      simp only [hasTyp, asList?_eraseV] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        have hvs : ∀ w ∈ vs, AllIn Q w := by
          cases v <;> simp [Value.asList?] at hvl
          subst hvl; exact fun w hw => EraseAll.allIn_list_mem hv w hw
        simp only [Option.map_some, List.isEmpty_map] at h
        by_cases he : vs.isEmpty = true
        · simp [he] at h
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ih.list _ _ _ _ hRt hX ht.1 hvs h
    | listN e o =>
      have hxe : xExp grE gdE e = true := by simpa [xIter] using ht.2
      simp only [hasTyp, asList?_eraseV] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        have hvs : ∀ w ∈ vs, AllIn Q w := by
          cases v <;> simp [Value.asList?] at hvl
          subst hvl; exact fun w hw => EraseAll.allIn_list_mem hv w hw
        simp only [Option.map_some, Res.bind_eq_ok] at h ⊢
        obtain ⟨kv', hkv', k, hk, hl⟩ := h
        have hE := evalExp_er H hR.er (freeTyp_iter_n t e o) hxe m
        obtain ⟨kv, hkv, rfl⟩ := (EraseAll.ER.ok_iff hE).1 hkv'
        refine ⟨kv, evalExp_up hkv, k, by rw [asNat?_eraseV] at hk; exact hk, ?_⟩
        obtain ⟨hlen, hl⟩ := iteP_ok_true hl
        simp only [List.length_map] at hlen
        simp only [hlen, ↓reduceIte]
        exact ih.list _ _ _ _ hRt hX ht.1 hvs hl
  | varT x args =>
    simp only [xTy, Bool.and_eq_true] at ht
    simp only [hasTyp] at h ⊢
    have hloc : localTyp? ρ' x args = localTyp? ρ x args := by
      cases args with
      | nil => simp only [localTyp?, VarEnv.findTyp?, hR.typs]
      | cons _ _ => rfl
    rw [hloc] at h
    cases hl : localTyp? ρ x args with
    | some t' =>
      rw [hl] at h
      have ht' : TyX t' := by
        cases args with
        | nil => exact hX (x, t') (Script.mem_of_find? hl)
        | cons _ _ => simp [localTyp?] at hl
      exact ih.typ _ _ _ _ (tRel_closed ht'.2 hR.er.defs hR.typs hR.defs hR.grams) hX ht'.1 hv h
    | none =>
      rw [hl] at h
      simp only [Res.bind_eq_ok] at h ⊢
      obtain ⟨td, htd, ws', hws', hi⟩ := h
      have htd' : (utf8Env B).findTyp? x = some td := by
        cases hf : (utf8Env B).findTyp? x with
        | none => rw [hf] at htd; simp [Res.ofOption] at htd
        | some td' => rw [hf] at htd; simp [Res.ofOption] at htd; rw [htd]
      have hE := evalArgs_er H hR.er (freeTyp_var_args x args) (xArgs_of_xTyArgs ht.2) m
      obtain ⟨ws, hws, rfl⟩ := (EraseAll.ER.ok_iff hE).1 hws'
      refine ⟨td, htd, ws, evalArgs_up hws, ?_⟩
      exact ih.insts _ _ _ (hE.2 ws hws) (evalArgs_argTyX hX ht.2 hws)
        (xInsts_of_find htd' ht.1) hv hi

/-- `hasTypTup`, one step back. -/
theorem tb_tup : ∀ ρ ρ' bs vs, TRel Q (freeTypBinds bs) ρ ρ' → XT ρ → xTyBinds tyB bs = true →
    (∀ v ∈ vs, AllIn Q v) → hasTypTup (m + 1) (utf8Env B) ρ' bs (vs.map eraseV) = .ok true →
    hasTypTup (m + 1 + K) (utf8Env B) ρ bs vs = .ok true := by
  intro ρ ρ' bs vs hR hX hbs hvs h
  rw [Nat.add_right_comm]
  cases bs with
  | nil => cases vs <;> simp_all [hasTypTup]
  | cons b bs =>
    obtain ⟨x, t⟩ := b
    simp only [xTyBinds, Bool.and_eq_true] at hbs
    cases vs with
    | nil => simp [hasTypTup] at h
    | cons v vs =>
      simp only [hasTypTup, Res.bind_eq_ok, List.map_cons] at h ⊢
      obtain ⟨c, hc, hrest⟩ := h
      cases c
      · simp at hrest
      · simp only [↓reduceIte] at hrest
        have hRt : TRel Q (freeTyp t) ρ ρ' := hR.mono (Sets.subset_union_left _ _)
        have hv := hvs v List.mem_cons_self
        refine ⟨true, ih.typ _ _ _ _ hRt hX hbs.1 hv hc, ?_⟩
        simp only [↓reduceIte]
        have hR' := hR.bindVal (T := freeTypBinds bs) hv (Sets.subset_union_right _ _)
        exact ih.tup _ _ _ _ hR' hX hbs.2 (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) hrest

/-- `hasTypList`, one step back. -/
theorem tb_list : ∀ ρ ρ' t vs, TRel Q (freeTyp t) ρ ρ' → XT ρ → xTy tyB t = true →
    (∀ v ∈ vs, AllIn Q v) → hasTypList (m + 1) (utf8Env B) ρ' t (vs.map eraseV) = .ok true →
    hasTypList (m + 1 + K) (utf8Env B) ρ t vs = .ok true := by
  intro ρ ρ' t vs hR hX ht hvs h
  rw [Nat.add_right_comm]
  cases vs with
  | nil => simp [hasTypList]
  | cons v vs =>
    simp only [hasTypList, Res.bind_eq_ok, List.map_cons] at h ⊢
    obtain ⟨c, hc, hrest⟩ := h
    cases c
    · simp at hrest
    · simp only [↓reduceIte] at hrest
      refine ⟨true, ih.typ _ _ _ _ hR hX ht (hvs v List.mem_cons_self) hc, ?_⟩
      simp only [↓reduceIte]
      exact ih.list _ _ _ _ hR hX ht (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) hrest

/-- `hasTypDef`, one step back. -/
theorem tb_defTyp (hQE : QExp B K Q) : ∀ ρ dt v, SG Q gdE ρ → XT ρ → xDefTyp tyB dt = true →
    (defTypExp dt = true → ρ = VarEnv.empty) → AllIn Q v →
    hasTypDef (m + 1) (utf8Env B) (eraseScope ρ) dt (eraseV v) = .ok true →
    hasTypDef (m + 1 + K) (utf8Env B) ρ dt v = .ok true := by
  intro ρ dt v hρ hX hdt hE hv h
  rw [Nat.add_right_comm]
  cases dt with
  | aliasT t =>
    simp only [xDefTyp] at hdt
    simp only [hasTypDef] at h ⊢
    exact ih.typ _ _ _ _ (tRel_of_sg hρ) hX hdt hv h
  | structT fs =>
    simp only [xDefTyp] at hdt
    simp only [hasTypDef, EraseAll.asStruct?_eraseV] at h ⊢
    cases hvs : v.asStruct? with
    | none => rw [hvs] at h; cases h
    | some gs =>
      rw [hvs] at h
      have hv' : v = .struct gs := by
        cases v <;> simp [Value.asStruct?] at hvs
        rw [hvs]
      subst hv'
      have hgs : ∀ p ∈ gs, AllIn Q p.2 := fun p hp => EraseAll.allIn_struct_fields hv p hp
      refine ih.fields _ _ _ hρ hX hdt hgs (fun u hu hfs => ?_) h
      have hρe := hE (fsExp_of_struct hfs)
      subst hρe
      have hex : hasExp gs = true := by
        simp only [hasExp, List.any_eq_true]
        exact ⟨_, hu, rfl⟩
      exact hQE _ (hv.1 hex) gs rfl u hu
  | variantT cs =>
    simp only [xDefTyp] at hdt
    simp only [hasTypDef, asCase?_eraseV] at h ⊢
    cases hvc : v.asCase? with
    | none => rw [hvc] at h; cases h
    | some p =>
      rw [hvc] at h
      obtain ⟨op, w⟩ := p
      have hw : AllIn Q w := by
        cases v <;> simp [Value.asCase?] at hvc
        obtain ⟨rfl, rfl⟩ := hvc; exact hv
      exact ih.case _ _ _ _ hρ hX hdt hw h

/-- `hasTypFields`, one step back. -/
theorem tb_fields : ∀ ρ fs gs, SG Q gdE ρ → XT ρ → xTFields tyB fs = true →
    (∀ p ∈ gs, AllIn Q p.2) →
    (∀ u, ("EXPORTS", u) ∈ gs → fsExp fs = true → hasTyp K (utf8Env B) ρ expT u = .ok true) →
    hasTypFields (m + 1) (utf8Env B) (eraseScope ρ) fs (eraseVf gs) = .ok true →
    hasTypFields (m + 1 + K) (utf8Env B) ρ fs gs = .ok true := by
  intro ρ fs gs hρ hX hfs hgs hex h
  rw [Nat.add_right_comm]
  cases fs with
  | nil =>
    cases gs with
    | nil => simp [hasTypFields]
    | cons _ _ => simp [hasTypFields, eraseVf] at h
  | cons f fs =>
    obtain ⟨a, t, qs, prems⟩ := f
    cases gs with
    | nil => simp [hasTypFields, eraseVf] at h
    | cons g gs =>
      obtain ⟨a', w⟩ := g
      simp only [xTFields, Bool.and_eq_true] at hfs
      obtain ⟨hf, hfs⟩ := hfs
      simp only [hasTypFields, eraseVf_cons] at h ⊢
      obtain ⟨haa, h₁⟩ := iteP_ok_true h
      subst haa
      rw [Res.bind_eq_ok] at h₁
      obtain ⟨c, hc, h₂⟩ := h₁
      obtain ⟨hc₁, h₃⟩ := ite_ok_true h₂
      subst hc₁
      rw [Res.bind_eq_ok] at h₃
      obtain ⟨hp, hpv, h₄⟩ := h₃
      obtain ⟨hp₁, hrest⟩ := ite_ok_true h₄
      subst hp₁
      have hw : AllIn Q w := hgs _ List.mem_cons_self
      have hgs' : ∀ p ∈ gs, AllIn Q p.2 := fun p hp => hgs p (List.mem_cons_of_mem _ hp)
      have hfsE : ∀ fs' : List TypField, fsExp fs' = true →
          fsExp (TypField.mk a t qs prems :: fs') = true := by
        intro fs' h'; simp only [fsExp, List.any_cons, Bool.or_eq_true]; exact Or.inr h'
      have htail := ih.fields _ _ _ hρ hX hfs hgs'
        (fun u hu hfs' => hex u (List.mem_cons_of_mem _ hu) (hfsE fs hfs')) hrest
      simp only [↓reduceIte]
      rw [Res.bind_eq_ok]
      by_cases hE : a = "EXPORTS"
      · subst hE
        simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, List.isEmpty_iff] at hf
        obtain ⟨hT, rfl⟩ := hf
        have hfe : fsExp (TypField.mk "EXPORTS" t qs [] :: fs) = true := by
          simp [fsExp]
        have hwT := hex w List.mem_cons_self hfe
        rw [isExpT_eq hT]
        rcases m with _ | m
        · simp [hasTyp] at hc
        refine ⟨true, hasTyp_up (by omega) hwT, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        refine ⟨true, ?_, by simpa using htail⟩
        rw [show m + 1 + K = (m + K) + 1 by omega]
        simp [premsOk, premsHold_nil_eq, Res.elimUndef]
      · have hne : (a == "EXPORTS") = false := by simpa using hE
        simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hf
        simp only [hE, ↓reduceIte] at hc hpv
        refine ⟨true, ih.typ _ _ _ _ (tRel_of_sg hρ) hX hf.1 hw hc, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        refine ⟨true, ?_, by simpa using htail⟩
        rw [caseScope_erase, premsOk_er H (sg_caseScope hρ t hw) hf.2] at hpv
        exact premsOk_up hpv

/-- `bindQuants` comes back from the erased side. -/
theorem tb_bindQuants : ∀ (ρ : VarEnv) (ds : List (IL.Id × Typ × Exp)) (ρq' : VarEnv),
    SG Q gdE ρ → XT ρ → (∀ d ∈ ds, xExp grE gdE d.2.2 = true ∧ xTy tyB d.2.1 = true) →
    bindQuants (fun ρ e => evalExp m (utf8Env B) ρ e) (fun ρ t v => hasTyp m (utf8Env B) ρ t v)
      (eraseScope ρ) ds = .ok (some ρq') →
    ∃ ρq, SG Q gdE ρq ∧ XT ρq ∧ ρq' = eraseScope ρq ∧
      bindQuants (fun ρ e => evalExp (m + K) (utf8Env B) ρ e)
        (fun ρ t v => hasTyp (m + K) (utf8Env B) ρ t v) ρ ds = .ok (some ρq)
  | ρ, [], ρq', hρ, hX, _, h => by
    simp only [bindQuants, Except.ok.injEq, Option.some.injEq] at h
    subst h; exact ⟨ρ, hρ, hX, rfl, rfl⟩
  | ρ, (x, t, e) :: ds, ρq', hρ, hX, hds, h => by
    have h₀ := hds _ List.mem_cons_self
    simp only [bindQuants, Res.bind_eq_ok] at h ⊢
    obtain ⟨v', hv', c, hc, h⟩ := h
    have hE := (eraseAt H m).exp ρ e hρ h₀.1
    obtain ⟨v, hv, rfl⟩ := (EraseAll.ER.ok_iff hE).1 hv'
    have hva : AllIn Q v := hE.2 v hv
    cases c
    · simp at h
    · simp only [↓reduceIte] at h
      rw [← EraseAll.eraseScope_bindVal] at h
      obtain ⟨ρq, h₁, h₂, h₃, h₄⟩ := tb_bindQuants (ρ.bindVal x v) ds ρq' (hρ.bindVal hva) hX
        (fun d hd => hds d (List.mem_cons_of_mem _ hd)) h
      refine ⟨ρq, h₁, h₂, h₃, v, evalExp_up hv, true,
        ih.typ _ _ _ _ (tRel_of_sg hρ) hX h₀.2 hva hc, ?_⟩
      simp only [↓reduceIte]
      exact h₄

/-- `hasTypCase`, one step back. -/
theorem tb_case : ∀ ρ cs op w, SG Q gdE ρ → XT ρ → xTCases tyB cs = true → AllIn Q w →
    hasTypCase (m + 1) (utf8Env B) (eraseScope ρ) cs op (eraseV w) = .ok true →
    hasTypCase (m + 1 + K) (utf8Env B) ρ cs op w = .ok true := by
  intro ρ cs op w hρ hX hcs hw h
  rw [Nat.add_right_comm]
  cases cs with
  | nil => simp [hasTypCase] at h
  | cons c cs =>
    obtain ⟨op', t, qs, prems⟩ := c
    simp only [xTCases, Bool.and_eq_true] at hcs
    obtain ⟨⟨⟨hct, hq⟩, hpr⟩, hcs⟩ := hcs
    simp only [hasTypCase] at h ⊢
    by_cases hop : op' = op
    · simp only [hop, ↓reduceIte, Res.bind_eq_ok] at h ⊢
      obtain ⟨c, hc, h⟩ := h
      have hc' : c = true := by cases c <;> simp_all
      subst hc'
      simp only [↓reduceIte] at h
      refine ⟨true, ih.typ _ _ _ _ (tRel_of_sg hρ) hX hct hw hc, ?_⟩
      simp only [↓reduceIte]
      have hcs₀ := sg_caseScope hρ t hw
      have hXc : XT (caseScope ρ t w) := xt_of_typs hX (TypAgree.caseScope_typs ρ t w).1
      rw [caseScope_erase] at h
      rcases TypAgree.elimUndef_eq_ok' h with ⟨o, ho, hk⟩ | ⟨_, hk⟩
      · cases o with
        | none => simp at hk
        | some ρq' =>
          obtain ⟨ρq, hρq, -, rfl, hb⟩ := tb_bindQuants H ih _ _ ρq' hcs₀ hXc (quantDefs_x hpr hq) ho
          rw [hb]
          simp only [Res.elimUndef]
          simp only at hk
          rw [premsOk_er H hρq hpr] at hk
          exact premsOk_up hk
      · simp at hk
    · simp only [hop, ↓reduceIte] at h ⊢
      exact ih.case _ _ _ _ hρ hX hcs hw h

/-- `hasTypInsts`, one step back. -/
theorem tb_insts : ∀ insts ws v, (∀ w ∈ ws, ArgIn Q gdE w) → (∀ w ∈ ws, ArgTyX w) →
    xInsts tyB insts = true → AllIn Q v →
    hasTypInsts (m + 1) (utf8Env B) insts (ws.map eraseA) (eraseV v) = .ok true →
    hasTypInsts (m + 1 + K) (utf8Env B) insts ws v = .ok true := by
  intro insts ws v hW hWT hins hv h
  rw [Nat.add_right_comm]
  cases insts with
  | nil => simp [hasTypInsts] at h
  | cons i insts =>
    obtain ⟨qs, pats, dt⟩ := i
    simp only [xInsts, List.all_cons, Bool.and_eq_true] at hins
    obtain ⟨⟨⟨hpats, hdt⟩, hpe⟩, hins⟩ := hins
    simp only [hasTypInsts] at h ⊢
    have hE := (eraseAt H m).matchArgs VarEnv.empty pats ws EraseAll.sg_empty hpats hW
    rw [EraseAll.eraseScope_empty] at hE
    rw [hE.1] at h
    cases hm : matchArgs m (utf8Env B) VarEnv.empty pats ws with
    | ok ρi =>
      rw [hm] at h
      simp only [Functor.map, Except.map, Res.elimUndef] at h
      have hm' : matchArgs (m + K) (utf8Env B) VarEnv.empty pats ws = .ok ρi :=
        ((monoAt_of_le (Nat.le_add_right m K)).matchArgs _ _ _ _).ok hm
      rw [hm']
      simp only [Res.elimUndef]
      refine ih.defTyp _ _ _ (hE.2 ρi hm) (matchArgs_xt m xt_empty hWT hm) hdt (fun hd => ?_) hv h
      have hp : pats = [] := by simpa [hd] using hpe
      subst hp
      exact matchArgs_nil_pats hm
    | error er =>
      rw [hm] at h
      cases er with
      | outOfFuel => simp [Functor.map, Except.map, Res.elimUndef] at h
      | undef =>
        simp only [Functor.map, Except.map, Res.elimUndef] at h
        have hm' : matchArgs (m + K) (utf8Env B) VarEnv.empty pats ws = .error .undef :=
          ((monoAt_of_le (Nat.le_add_right m K)).matchArgs _ _ _ _).eq_of_ne_oof (by rw [hm]; simp)
            |>.trans hm
        rw [hm']
        simp only [Res.elimUndef]
        exact ih.insts _ _ _ hW hWT (by unfold xInsts; exact hins) hv h

end Step

theorem tBwdAt_succ (H : Hyps Q grE gdE (utf8Env B)) {K m : Nat} (hQE : QExp B K Q)
    (ih : TBwdAt Q B K m) : TBwdAt Q B K (m + 1) :=
  ⟨tb_typ H ih, tb_tup H ih, tb_list H ih, tb_defTyp H ih hQE, tb_fields H ih, tb_case H ih,
    tb_insts H ih⟩

/-- **The typing block comes back from the erased side, at every fuel.** -/
theorem tBwdAt (H : Hyps Q grE gdE (utf8Env B)) {K : Nat} (hQE : QExp B K Q) :
    ∀ n, TBwdAt Q B K n
  | 0 => tBwdAt_zero K
  | n + 1 => tBwdAt_succ H hQE (tBwdAt H hQE n)

/-- **`TypBwd` holds in the round-7 environment**, given typed export lists. -/
theorem typBwd_utf8Env (H : Hyps Q grE gdE (utf8Env B)) {K : Nat} (hQE : QExp B K Q) :
    TypBwd Q gdE (utf8Env B) := by
  intro ρ ρ' t w hR ht hρ _ hd hg hxt hw ⟨n, hn⟩
  have hX : XT ρ := fun p hp => by rw [hρ] at hp; cases hp
  exact ⟨n + K, (tBwdAt H hQE n).typ ρ ρ' t w ⟨hR, ht, hd, hg⟩ hX hxt hw hn⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
