module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.TypBase

/-!
# Round 7, typing across erasure: the forward direction (unrefined)

`tFwdAt`: at every fuel, if a member of the typing block answers `true` on checked types
(`xTy tyB`) and swap-set values, it answers `true` on the erased values in the erased scope. The
proof is one step per member (`tf_typ`, …, `tf_insts`), with the calls out of the typing block going
to the whole-evaluator erasure (`Round7.EraseAll.eraseAt`).

The one place where the two sides differ is the `EXPORTS` field of a module record: there the
erased value is `[]`, which every list type holds once there is fuel to look at it, and the check
puts no premise on that field. So the statement is an implication on `true`, not an equality: an
ill-typed export list is typed after erasure.

`typFwd_utf8Env` is `TypFwd` at round 7's environment.
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

/-- **The typing block goes to the erased side at fuel `n`.** -/
structure TFwdAt (Q : Value → Prop) (B : Builtins) (n : Nat) : Prop where
  typ : ∀ ρ ρ' t v, TRel Q (freeTyp t) ρ ρ' → XT ρ → xTy tyB t = true → AllIn Q v →
    hasTyp n (utf8Env B) ρ t v = .ok true → hasTyp n (utf8Env B) ρ' t (eraseV v) = .ok true
  tup : ∀ ρ ρ' bs vs, TRel Q (freeTypBinds bs) ρ ρ' → XT ρ → xTyBinds tyB bs = true →
    (∀ v ∈ vs, AllIn Q v) → hasTypTup n (utf8Env B) ρ bs vs = .ok true →
    hasTypTup n (utf8Env B) ρ' bs (vs.map eraseV) = .ok true
  list : ∀ ρ ρ' t vs, TRel Q (freeTyp t) ρ ρ' → XT ρ → xTy tyB t = true →
    (∀ v ∈ vs, AllIn Q v) → hasTypList n (utf8Env B) ρ t vs = .ok true →
    hasTypList n (utf8Env B) ρ' t (vs.map eraseV) = .ok true
  defTyp : ∀ ρ dt v, SG Q gdE ρ → XT ρ → xDefTyp tyB dt = true → AllIn Q v →
    hasTypDef n (utf8Env B) ρ dt v = .ok true →
    hasTypDef n (utf8Env B) (eraseScope ρ) dt (eraseV v) = .ok true
  fields : ∀ ρ fs gs, SG Q gdE ρ → XT ρ → xTFields tyB fs = true → (∀ p ∈ gs, AllIn Q p.2) →
    hasTypFields n (utf8Env B) ρ fs gs = .ok true →
    hasTypFields n (utf8Env B) (eraseScope ρ) fs (eraseVf gs) = .ok true
  case : ∀ ρ cs op w, SG Q gdE ρ → XT ρ → xTCases tyB cs = true → AllIn Q w →
    hasTypCase n (utf8Env B) ρ cs op w = .ok true →
    hasTypCase n (utf8Env B) (eraseScope ρ) cs op (eraseV w) = .ok true
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgIn Q gdE w) → (∀ w ∈ ws, ArgTyX w) →
    xInsts tyB insts = true → AllIn Q v → hasTypInsts n (utf8Env B) insts ws v = .ok true →
    hasTypInsts n (utf8Env B) insts (ws.map eraseA) (eraseV v) = .ok true

theorem tFwdAt_zero : TFwdAt Q B 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (simp only [hasTyp] at *; contradiction)
    | (simp only [hasTypTup] at *; contradiction)
    | (simp only [hasTypList] at *; contradiction)
    | (simp only [hasTypDef] at *; contradiction)
    | (simp only [hasTypFields] at *; contradiction)
    | (simp only [hasTypCase] at *; contradiction)
    | (simp only [hasTypInsts] at *; contradiction)

theorem ite_ok_true {b : Bool} {r : Res Bool} (h : (if b = true then r else .ok false) = .ok true) :
    b = true ∧ r = .ok true := by
  cases b
  · simp at h
  · exact ⟨rfl, by simpa using h⟩

theorem iteP_ok_true {c : Prop} [Decidable c] {r : Res Bool}
    (h : (if c then r else .ok false) = .ok true) : c ∧ r = .ok true := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h; exact ⟨hc, h⟩
  · simp [hc] at h

theorem freeTyp_tup (bs : List TypBind) : freeTyp (.tupT bs) = freeTypBinds bs := rfl

theorem freeTyp_iter_t (t : Typ) (it : Iter) : freeTyp t ⊆ freeTyp (.iterT t it) :=
  Sets.subset_union_left _ _

theorem freeTyp_iter_n (t : Typ) (e : Exp) (o : Option IL.Id) :
    freeExp e ⊆ freeTyp (.iterT t (.listN e o)) := Sets.subset_union_right (freeTyp t) _

theorem freeTyp_var_args (x : IL.Id) (args : List Arg) : freeArgs args ⊆ freeTyp (.varT x args) :=
  Sets.subset_union_right _ _

theorem typid_mem_var (x : IL.Id) (args : List Arg) : x ∈ (freeTyp (.varT x args)).typid := by
  simp [freeTyp, freeTypid, Sets.union, Sets.empty]

theorem isExpT_eq {t : Typ} (h : isExpT t = true) : t = .iterT (.varT "exportinst" []) .list := by
  unfold isExpT at h
  split at h
  · rfl
  · cases h

theorem hasTyp_nil_list {n : Nat} {ρ ρ₁ : VarEnv} {t : Typ} {w : Value} (hE : isExpT t = true)
    (h : hasTyp n (utf8Env B) ρ t w = .ok true) :
    hasTyp n (utf8Env B) ρ₁ t (.list []) = .ok true := by
  rw [isExpT_eq hE] at h ⊢
  rcases n with _ | m
  · simp [hasTyp] at h
  simp only [hasTyp] at h ⊢
  cases hw : w.asList? with
  | none => rw [hw] at h; cases h
  | some vs =>
    rw [hw] at h
    rcases m with _ | m
    · simp [hasTypList] at h
    · simp [Value.asList?, hasTypList]

section Step

set_option linter.unusedSectionVars false

variable (H : Hyps Q grE gdE (utf8Env B)) {m : Nat} (ih : TFwdAt Q B m)
include H ih

/-- `hasTyp`, one step. -/
theorem tf_typ : ∀ ρ ρ' t v, TRel Q (freeTyp t) ρ ρ' → XT ρ → xTy tyB t = true → AllIn Q v →
    hasTyp (m + 1) (utf8Env B) ρ t v = .ok true →
    hasTyp (m + 1) (utf8Env B) ρ' t (eraseV v) = .ok true := by
  intro ρ ρ' t v hR hX ht hv h
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
        simp only [Option.map_some, List.isEmpty_map]
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
        obtain ⟨kv, hkv, k, hk, hl⟩ := h
        have hE := evalExp_er H hR.er (freeTyp_iter_n t e o) hxe m
        refine ⟨eraseV kv, EraseAll.ER.eq_ok hE hkv, k, by rw [asNat?_eraseV]; exact hk, ?_⟩
        obtain ⟨hlen, hl⟩ := iteP_ok_true hl
        simp only [List.length_map, hlen, ↓reduceIte]
        exact ih.list _ _ _ _ hRt hX ht.1 hvs hl
  | varT x args =>
    simp only [xTy, Bool.and_eq_true] at ht
    simp only [hasTyp] at h ⊢
    have hloc : localTyp? ρ' x args = localTyp? ρ x args := by
      cases args with
      | nil => simp only [localTyp?, VarEnv.findTyp?, hR.typs]
      | cons _ _ => rfl
    rw [hloc]
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
      obtain ⟨td, htd, ws, hws, hi⟩ := h
      have htd' : (utf8Env B).findTyp? x = some td := by
        cases hf : (utf8Env B).findTyp? x with
        | none => rw [hf] at htd; simp [Res.ofOption] at htd
        | some td' => rw [hf] at htd; simp [Res.ofOption] at htd; rw [htd]
      have hE := evalArgs_er H hR.er (freeTyp_var_args x args) (xArgs_of_xTyArgs ht.2) m
      refine ⟨td, htd, ws.map eraseA, EraseAll.ER.eq_ok hE hws, ?_⟩
      exact ih.insts _ _ _ (hE.2 ws hws) (evalArgs_argTyX hX ht.2 hws)
        (xInsts_of_find htd' ht.1) hv hi

/-- `hasTypTup`, one step. -/
theorem tf_tup : ∀ ρ ρ' bs vs, TRel Q (freeTypBinds bs) ρ ρ' → XT ρ → xTyBinds tyB bs = true →
    (∀ v ∈ vs, AllIn Q v) → hasTypTup (m + 1) (utf8Env B) ρ bs vs = .ok true →
    hasTypTup (m + 1) (utf8Env B) ρ' bs (vs.map eraseV) = .ok true := by
  intro ρ ρ' bs vs hR hX hbs hvs h
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

/-- `hasTypList`, one step. -/
theorem tf_list : ∀ ρ ρ' t vs, TRel Q (freeTyp t) ρ ρ' → XT ρ → xTy tyB t = true →
    (∀ v ∈ vs, AllIn Q v) → hasTypList (m + 1) (utf8Env B) ρ t vs = .ok true →
    hasTypList (m + 1) (utf8Env B) ρ' t (vs.map eraseV) = .ok true := by
  intro ρ ρ' t vs hR hX ht hvs h
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

/-- `hasTypDef`, one step. -/
theorem tf_defTyp : ∀ ρ dt v, SG Q gdE ρ → XT ρ → xDefTyp tyB dt = true → AllIn Q v →
    hasTypDef (m + 1) (utf8Env B) ρ dt v = .ok true →
    hasTypDef (m + 1) (utf8Env B) (eraseScope ρ) dt (eraseV v) = .ok true := by
  intro ρ dt v hρ hX hdt hv h
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
      have hgs : ∀ p ∈ gs, AllIn Q p.2 := by
        cases v <;> simp [Value.asStruct?] at hvs
        subst hvs
        exact fun p hp => EraseAll.allIn_struct_fields hv p hp
      exact ih.fields _ _ _ hρ hX hdt hgs h
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

/-- `hasTypFields`, one step. -/
theorem tf_fields : ∀ ρ fs gs, SG Q gdE ρ → XT ρ → xTFields tyB fs = true →
    (∀ p ∈ gs, AllIn Q p.2) → hasTypFields (m + 1) (utf8Env B) ρ fs gs = .ok true →
    hasTypFields (m + 1) (utf8Env B) (eraseScope ρ) fs (eraseVf gs) = .ok true := by
  intro ρ fs gs hρ hX hfs hgs h
  cases fs with
  | nil =>
    cases gs with
    | nil => simp [hasTypFields, eraseVf]
    | cons _ _ => simp [hasTypFields] at h
  | cons f fs =>
    obtain ⟨a, t, qs, prems⟩ := f
    cases gs with
    | nil => simp [hasTypFields] at h
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
      have htail := ih.fields _ _ _ hρ hX hfs hgs' hrest
      simp only [↓reduceIte]
      rw [Res.bind_eq_ok]
      by_cases hE : a = "EXPORTS"
      · subst hE
        simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, List.isEmpty_iff] at hf
        obtain ⟨hT, rfl⟩ := hf
        refine ⟨true, hasTyp_nil_list hT hc, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        refine ⟨true, ?_, by simpa using htail⟩
        rcases m with _ | m
        · simp [hasTypFields] at hrest
        · simp [premsOk, premsHold_nil_eq, Res.elimUndef]
      · have hne : (a == "EXPORTS") = false := by simpa using hE
        simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hf
        simp only [hE, ↓reduceIte]
        refine ⟨true, ih.typ _ _ _ _ (tRel_of_sg hρ) hX hf.1 hw hc, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        refine ⟨true, ?_, by simpa using htail⟩
        rw [caseScope_erase, premsOk_er H (sg_caseScope hρ t hw) hf.2]
        exact hpv

/-- `bindQuants` goes to the erased side on a swap-set scope. -/
theorem tf_bindQuants : ∀ (ρ : VarEnv) (ds : List (IL.Id × Typ × Exp)) (ρq : VarEnv), SG Q gdE ρ →
    XT ρ → (∀ d ∈ ds, xExp grE gdE d.2.2 = true ∧ xTy tyB d.2.1 = true) →
    bindQuants (fun ρ e => evalExp m (utf8Env B) ρ e) (fun ρ t v => hasTyp m (utf8Env B) ρ t v)
      ρ ds = .ok (some ρq) →
    SG Q gdE ρq ∧ XT ρq ∧
      bindQuants (fun ρ e => evalExp m (utf8Env B) ρ e) (fun ρ t v => hasTyp m (utf8Env B) ρ t v)
        (eraseScope ρ) ds = .ok (some (eraseScope ρq))
  | ρ, [], ρq, hρ, hX, _, h => by
    simp only [bindQuants, Except.ok.injEq, Option.some.injEq] at h
    subst h; exact ⟨hρ, hX, rfl⟩
  | ρ, (x, t, e) :: ds, ρq, hρ, hX, hds, h => by
    have h₀ := hds _ List.mem_cons_self
    simp only [bindQuants, Res.bind_eq_ok] at h ⊢
    obtain ⟨v, hv, c, hc, h⟩ := h
    have hE := (eraseAt H m).exp ρ e hρ h₀.1
    have hva : AllIn Q v := hE.2 v hv
    cases c
    · simp at h
    · simp only [↓reduceIte] at h
      have ih' := tf_bindQuants (ρ.bindVal x v) ds ρq (hρ.bindVal hva) hX
        (fun d hd => hds d (List.mem_cons_of_mem _ hd)) h
      refine ⟨ih'.1, ih'.2.1, eraseV v, EraseAll.ER.eq_ok hE hv, true,
        ih.typ _ _ _ _ (tRel_of_sg hρ) hX h₀.2 hva hc, ?_⟩
      simp only [↓reduceIte]
      rw [← EraseAll.eraseScope_bindVal]
      exact ih'.2.2

/-- `hasTypCase`, one step. -/
theorem tf_case : ∀ ρ cs op w, SG Q gdE ρ → XT ρ → xTCases tyB cs = true → AllIn Q w →
    hasTypCase (m + 1) (utf8Env B) ρ cs op w = .ok true →
    hasTypCase (m + 1) (utf8Env B) (eraseScope ρ) cs op (eraseV w) = .ok true := by
  intro ρ cs op w hρ hX hcs hw h
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
      rcases TypAgree.elimUndef_eq_ok' h with ⟨o, ho, hk⟩ | ⟨_, hk⟩
      · cases o with
        | none => simp at hk
        | some ρq =>
          obtain ⟨hρq, -, hb⟩ := tf_bindQuants H ih _ _ ρq hcs₀ hXc (quantDefs_x hpr hq) ho
          rw [caseScope_erase, hb]
          simp only [Res.elimUndef]
          rw [premsOk_er H hρq hpr]
          exact hk
      · simp at hk
    · simp only [hop, ↓reduceIte] at h ⊢
      exact ih.case _ _ _ _ hρ hX hcs hw h

/-- `hasTypInsts`, one step. -/
theorem tf_insts : ∀ insts ws v, (∀ w ∈ ws, ArgIn Q gdE w) → (∀ w ∈ ws, ArgTyX w) →
    xInsts tyB insts = true → AllIn Q v → hasTypInsts (m + 1) (utf8Env B) insts ws v = .ok true →
    hasTypInsts (m + 1) (utf8Env B) insts (ws.map eraseA) (eraseV v) = .ok true := by
  intro insts ws v hW hWT hins hv h
  cases insts with
  | nil => simp [hasTypInsts] at h
  | cons i insts =>
    obtain ⟨qs, pats, dt⟩ := i
    simp only [xInsts, List.all_cons, Bool.and_eq_true] at hins
    obtain ⟨⟨⟨hpats, hdt⟩, -⟩, hins⟩ := hins
    simp only [hasTypInsts] at h ⊢
    have hE := (eraseAt H m).matchArgs VarEnv.empty pats ws EraseAll.sg_empty hpats hW
    rw [EraseAll.eraseScope_empty] at hE
    rw [hE.1]
    rcases TypAgree.elimUndef_eq_ok' h with ⟨ρi, hρi, hk⟩ | ⟨hu, hk⟩
    · rw [hρi]
      simp only [Functor.map, Except.map, Res.elimUndef]
      exact ih.defTyp _ _ _ (hE.2 ρi hρi) (matchArgs_xt m xt_empty hWT hρi) hdt hv hk
    · rw [hu]
      simp only [Functor.map, Except.map, Res.elimUndef]
      exact ih.insts _ _ _ hW hWT (by unfold xInsts; exact hins) hv hk

end Step

theorem tFwdAt_succ (H : Hyps Q grE gdE (utf8Env B)) {m : Nat} (ih : TFwdAt Q B m) :
    TFwdAt Q B (m + 1) :=
  ⟨tf_typ H ih, tf_tup H ih, tf_list H ih, tf_defTyp H ih, tf_fields H ih, tf_case H ih,
    tf_insts H ih⟩

/-- **The typing block goes to the erased side, at every fuel.** -/
theorem tFwdAt (H : Hyps Q grE gdE (utf8Env B)) : ∀ n, TFwdAt Q B n
  | 0 => tFwdAt_zero
  | n + 1 => tFwdAt_succ H (tFwdAt H n)

/-- **`TypFwd` holds in the round-7 environment.** -/
theorem typFwd_utf8Env (H : Hyps Q grE gdE (utf8Env B)) : TypFwd Q gdE (utf8Env B) := by
  intro ρ ρ' t w hR ht hρ _ hd hg hxt hw ⟨n, hn⟩
  have hX : XT ρ := fun p hp => by rw [hρ] at hp; cases hp
  exact ⟨n, (tFwdAt H n).typ ρ ρ' t w ⟨hR, ht, hd, hg⟩ hX hxt hw hn⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
