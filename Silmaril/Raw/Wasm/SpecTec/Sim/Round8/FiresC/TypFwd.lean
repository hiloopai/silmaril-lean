module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.FiresC.Code

/-!
# Round 8, typing across code erasure: the forward direction (unrefined)

Round 7's `Raw/…/Round7/EraseDer/TypFwd.lean`, copied for `CODE` with every value in the swap set
(so the erased scope is `eraseScope ρ`). `tFwdAt`: at every fuel, if a member of the typing block
answers `true` on checked types (`xTy tyC`), it answers `true` on the erased values in the erased
scope. Calls out of the typing block go to round 8's evaluator-level erasure
(`CodeErase.EraseAll.eraseAt`).

The one place where the two sides differ is the `CODE` field of `funcinst`: the erased value is
`hostC u`, which is a `funccode` whenever `u` is (`hasTyp_code`). The field has no premises and
its record type is an instance without argument patterns, so it is typed in a scope without type
variables (the hypotheses `defTypCode dt = true → ρ.typs = []`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (Hyps SG ER ArgIn grC gdC xExp xPrems xArgs
  xIter eraseAt)

variable {B : Builtins}

/-- The instances of a `tyC` type are checked. -/
theorem xInsts_of_find {x : IL.Id} {v : TypDef}
    (h : (simEnv B).findTyp? x = some v) (hS : tyC.contains x = true) : xInsts tyC v.2 = true := by
  have hm := Round7.TypAgree.mem_typs_of_findTyp h
  have := List.all_eq_true.1 xTypMap_fixed _ hm
  simp only [hS, Bool.not_true, Bool.false_or] at this
  exact this

/-- **The typing block goes to the erased side at fuel `n`.** -/
structure TFwdAt (B : Builtins) (n : Nat) : Prop where
  typ : ∀ ρ t v, SG QT gdC ρ → XT ρ → xTy tyC t = true →
    hasTyp n (simEnv B) ρ t v = .ok true →
    hasTyp n (simEnv B) (eraseScope ρ) t (eraseC v) = .ok true
  tup : ∀ ρ bs vs, SG QT gdC ρ → XT ρ → xTyBinds tyC bs = true →
    hasTypTup n (simEnv B) ρ bs vs = .ok true →
    hasTypTup n (simEnv B) (eraseScope ρ) bs (vs.map eraseC) = .ok true
  list : ∀ ρ t vs, SG QT gdC ρ → XT ρ → xTy tyC t = true →
    hasTypList n (simEnv B) ρ t vs = .ok true →
    hasTypList n (simEnv B) (eraseScope ρ) t (vs.map eraseC) = .ok true
  defTyp : ∀ ρ dt v, SG QT gdC ρ → XT ρ → xDefTyp tyC dt = true →
    (defTypCode dt = true → ρ.typs = []) →
    hasTypDef n (simEnv B) ρ dt v = .ok true →
    hasTypDef n (simEnv B) (eraseScope ρ) dt (eraseC v) = .ok true
  fields : ∀ ρ fs gs, SG QT gdC ρ → XT ρ → xTFields tyC fs = true →
    (fieldsCode fs = true → ρ.typs = []) →
    hasTypFields n (simEnv B) ρ fs gs = .ok true →
    hasTypFields n (simEnv B) (eraseScope ρ) fs (eraseCf gs) = .ok true
  case : ∀ ρ cs op w, SG QT gdC ρ → XT ρ → xTCases tyC cs = true →
    hasTypCase n (simEnv B) ρ cs op w = .ok true →
    hasTypCase n (simEnv B) (eraseScope ρ) cs op (eraseC w) = .ok true
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgIn QT gdC w) → (∀ w ∈ ws, ArgTyX w) →
    xInsts tyC insts = true → hasTypInsts n (simEnv B) insts ws v = .ok true →
    hasTypInsts n (simEnv B) insts (ws.map eraseA) (eraseC v) = .ok true

theorem tFwdAt_zero : TFwdAt B 0 := by
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

theorem fieldsCode_cons {a : AtomS} {t : Typ} {qs : List Param} {prems : List Prem}
    {fs : List TypField} :
    fieldsCode (.mk a t qs prems :: fs) = ((a == "CODE") || fieldsCode fs) := by
  simp [fieldsCode]

theorem isCodeT_eq {t : Typ} (h : isCodeT t = true) : t = .varT "funccode" [] := by
  unfold isCodeT at h
  split at h
  · rfl
  · cases h

theorem premsOk_nil {env : Env} {m : Nat} {σ σ' : VarEnv}
    (h : premsOk m env σ [] = .ok true) : premsOk m env σ' [] = .ok true := by
  rcases m with _ | m
  · simp [premsOk, premsHold, Res.elimUndef] at h
  · simp [premsOk, premsHold_nil_eq, Res.elimUndef]

section Step

set_option linter.unusedSectionVars false

variable (H : Hyps QT grC gdC (simEnv B)) {m : Nat} (ih : TFwdAt B m)
include H ih

/-- `hasTyp`, one step. -/
theorem tf_typ : ∀ ρ t v, SG QT gdC ρ → XT ρ → xTy tyC t = true →
    hasTyp (m + 1) (simEnv B) ρ t v = .ok true →
    hasTyp (m + 1) (simEnv B) (eraseScope ρ) t (eraseC v) = .ok true := by
  intro ρ t v hρ hX ht h
  cases t with
  | boolT => simpa [hasTyp, asBool?_eraseC] using h
  | numT t => simpa [hasTyp, asNum?_eraseC] using h
  | textT => simpa [hasTyp, asText?_eraseC] using h
  | tupT bs =>
    simp only [xTy] at ht
    simp only [hasTyp, asTuple?_eraseC] at h ⊢
    cases hvt : v.asTuple? with
    | none => rw [hvt] at h; cases h
    | some vs =>
      rw [hvt] at h
      exact ih.tup _ _ _ hρ hX ht h
  | iterT t it =>
    simp only [xTy, Bool.and_eq_true] at ht
    cases it with
    | opt =>
      simp only [hasTyp, asOpt?_eraseC] at h ⊢
      cases hvo : v.asOpt? with
      | none => rw [hvo] at h; cases h
      | some o =>
        rw [hvo] at h
        cases o with
        | none => rfl
        | some w => exact ih.typ _ _ _ hρ hX ht.1 h
    | list =>
      simp only [hasTyp, asList?_eraseC] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        exact ih.list _ _ _ hρ hX ht.1 h
    | list1 =>
      simp only [hasTyp, asList?_eraseC] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        simp only [Option.map_some, List.isEmpty_map]
        by_cases he : vs.isEmpty = true
        · simp [he] at h
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ih.list _ _ _ hρ hX ht.1 h
    | listN e o =>
      have hxe : xExp grC gdC e = true := by simpa [CodeErase.EraseAll.xIter] using ht.2
      simp only [hasTyp, asList?_eraseC] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        simp only [Option.map_some, Res.bind_eq_ok] at h ⊢
        obtain ⟨kv, hkv, k, hk, hl⟩ := h
        have hE := (eraseAt H m).exp ρ e hρ hxe
        refine ⟨eraseC kv, CodeErase.EraseAll.ER.eq_ok hE hkv, k,
          by rw [asNat?_eraseC]; exact hk, ?_⟩
        obtain ⟨hlen, hl⟩ := iteP_ok_true hl
        simp only [List.length_map, hlen, ↓reduceIte]
        exact ih.list _ _ _ hρ hX ht.1 hl
  | varT x args =>
    simp only [xTy, Bool.and_eq_true] at ht
    simp only [hasTyp] at h ⊢
    have hloc : localTyp? (eraseScope ρ) x args = localTyp? ρ x args := by
      cases args with
      | nil => simp only [localTyp?, VarEnv.findTyp?, CodeErase.EraseAll.eraseScope_typs]
      | cons _ _ => rfl
    rw [hloc]
    cases hl : localTyp? ρ x args with
    | some t' =>
      rw [hl] at h
      have ht' : TyX t' := by
        cases args with
        | nil => exact hX (x, t') (Round7.Script.mem_of_find? hl)
        | cons _ _ => simp [localTyp?] at hl
      exact ih.typ _ _ _ hρ hX ht'.1 h
    | none =>
      rw [hl] at h
      simp only [Res.bind_eq_ok] at h ⊢
      obtain ⟨td, htd, ws, hws, hi⟩ := h
      have htd' : (simEnv B).findTyp? x = some td := by
        cases hf : (simEnv B).findTyp? x with
        | none => rw [hf] at htd; simp [Res.ofOption] at htd
        | some td' => rw [hf] at htd; simp [Res.ofOption] at htd; rw [htd]
      have hE := (eraseAt H m).args ρ args hρ (xArgs_of_xTyArgs ht.2)
      refine ⟨td, htd, ws.map eraseA, CodeErase.EraseAll.ER.eq_ok hE hws, ?_⟩
      exact ih.insts _ _ _ (hE.2 ws hws) (evalArgs_argTyX hX ht.2 hws)
        (xInsts_of_find htd' ht.1) hi

/-- `hasTypTup`, one step. -/
theorem tf_tup : ∀ ρ bs vs, SG QT gdC ρ → XT ρ → xTyBinds tyC bs = true →
    hasTypTup (m + 1) (simEnv B) ρ bs vs = .ok true →
    hasTypTup (m + 1) (simEnv B) (eraseScope ρ) bs (vs.map eraseC) = .ok true := by
  intro ρ bs vs hρ hX hbs h
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
        refine ⟨true, ih.typ _ _ _ hρ hX hbs.1 hc, ?_⟩
        simp only [↓reduceIte]
        rw [← CodeErase.EraseAll.eraseScope_bindVal]
        exact ih.tup _ _ _ (hρ.bindVal (CodeErase.EraseAll.allIn_true v)) hX hbs.2 hrest

/-- `hasTypList`, one step. -/
theorem tf_list : ∀ ρ t vs, SG QT gdC ρ → XT ρ → xTy tyC t = true →
    hasTypList (m + 1) (simEnv B) ρ t vs = .ok true →
    hasTypList (m + 1) (simEnv B) (eraseScope ρ) t (vs.map eraseC) = .ok true := by
  intro ρ t vs hρ hX ht h
  cases vs with
  | nil => simp [hasTypList]
  | cons v vs =>
    simp only [hasTypList, Res.bind_eq_ok, List.map_cons] at h ⊢
    obtain ⟨c, hc, hrest⟩ := h
    cases c
    · simp at hrest
    · simp only [↓reduceIte] at hrest
      refine ⟨true, ih.typ _ _ _ hρ hX ht hc, ?_⟩
      simp only [↓reduceIte]
      exact ih.list _ _ _ hρ hX ht hrest

/-- `hasTypDef`, one step. -/
theorem tf_defTyp : ∀ ρ dt v, SG QT gdC ρ → XT ρ → xDefTyp tyC dt = true →
    (defTypCode dt = true → ρ.typs = []) →
    hasTypDef (m + 1) (simEnv B) ρ dt v = .ok true →
    hasTypDef (m + 1) (simEnv B) (eraseScope ρ) dt (eraseC v) = .ok true := by
  intro ρ dt v hρ hX hdt hT h
  cases dt with
  | aliasT t =>
    simp only [xDefTyp] at hdt
    simp only [hasTypDef] at h ⊢
    exact ih.typ _ _ _ hρ hX hdt h
  | structT fs =>
    simp only [xDefTyp] at hdt
    simp only [hasTypDef, CodeErase.EraseAll.asStruct?_eraseC] at h ⊢
    cases hvs : v.asStruct? with
    | none => rw [hvs] at h; cases h
    | some gs =>
      rw [hvs] at h
      exact ih.fields _ _ _ hρ hX hdt hT h
  | variantT cs =>
    simp only [xDefTyp] at hdt
    simp only [hasTypDef, asCase?_eraseC] at h ⊢
    cases hvc : v.asCase? with
    | none => rw [hvc] at h; cases h
    | some p =>
      rw [hvc] at h
      exact ih.case _ _ _ _ hρ hX hdt h

/-- `hasTypFields`, one step. -/
theorem tf_fields : ∀ ρ fs gs, SG QT gdC ρ → XT ρ → xTFields tyC fs = true →
    (fieldsCode fs = true → ρ.typs = []) →
    hasTypFields (m + 1) (simEnv B) ρ fs gs = .ok true →
    hasTypFields (m + 1) (simEnv B) (eraseScope ρ) fs (eraseCf gs) = .ok true := by
  intro ρ fs gs hρ hX hfs hT h
  cases fs with
  | nil =>
    cases gs with
    | nil => simp [hasTypFields]
    | cons _ _ => simp [hasTypFields] at h
  | cons f fs =>
    obtain ⟨a, t, qs, prems⟩ := f
    cases gs with
    | nil => simp [hasTypFields] at h
    | cons g gs =>
      obtain ⟨a', w⟩ := g
      simp only [xTFields, Bool.and_eq_true] at hfs
      obtain ⟨hf, hfs⟩ := hfs
      simp only [hasTypFields, eraseCf_cons] at h ⊢
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
      have hT' : fieldsCode fs = true → ρ.typs = [] := fun hc => hT (by
        rw [fieldsCode_cons, hc, Bool.or_true])
      have htail := ih.fields _ _ _ hρ hX hfs hT' hrest
      simp only [↓reduceIte]
      rw [Res.bind_eq_ok]
      by_cases hE : a = "CODE"
      · subst hE
        simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, List.isEmpty_iff] at hf
        obtain ⟨hTc, rfl⟩ := hf
        have hρT : ρ.typs = [] := hT (by rw [fieldsCode_cons]; rfl)
        rw [isCodeT_eq hTc] at hc ⊢
        refine ⟨true, hasTyp_code hρT (by simpa using hρT) w hc, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        exact ⟨true, premsOk_nil hpv, by simpa using htail⟩
      · have hne : (a == "CODE") = false := by simpa using hE
        simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hf
        simp only [hE, ↓reduceIte]
        refine ⟨true, ih.typ _ _ _ hρ hX hf.1 hc, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        refine ⟨true, ?_, by simpa using htail⟩
        rw [caseScope_erase, premsOk_er H (sg_caseScope hρ t w) hf.2]
        exact hpv

/-- `bindQuants` goes to the erased side. -/
theorem tf_bindQuants : ∀ (ρ : VarEnv) (ds : List (IL.Id × Typ × Exp)) (ρq : VarEnv),
    SG QT gdC ρ → XT ρ → (∀ d ∈ ds, xExp grC gdC d.2.2 = true ∧ xTy tyC d.2.1 = true) →
    bindQuants (fun ρ e => evalExp m (simEnv B) ρ e) (fun ρ t v => hasTyp m (simEnv B) ρ t v)
      ρ ds = .ok (some ρq) →
    SG QT gdC ρq ∧ XT ρq ∧
      bindQuants (fun ρ e => evalExp m (simEnv B) ρ e) (fun ρ t v => hasTyp m (simEnv B) ρ t v)
        (eraseScope ρ) ds = .ok (some (eraseScope ρq))
  | ρ, [], ρq, hρ, hX, _, h => by
    simp only [bindQuants, Except.ok.injEq, Option.some.injEq] at h
    subst h; exact ⟨hρ, hX, rfl⟩
  | ρ, (x, t, e) :: ds, ρq, hρ, hX, hds, h => by
    have h₀ := hds _ List.mem_cons_self
    simp only [bindQuants, Res.bind_eq_ok] at h ⊢
    obtain ⟨v, hv, c, hc, h⟩ := h
    have hE := (eraseAt H m).exp ρ e hρ h₀.1
    cases c
    · simp at h
    · simp only [↓reduceIte] at h
      have ih' := tf_bindQuants (ρ.bindVal x v) ds ρq
        (hρ.bindVal (CodeErase.EraseAll.allIn_true v)) hX
        (fun d hd => hds d (List.mem_cons_of_mem _ hd)) h
      refine ⟨ih'.1, ih'.2.1, eraseC v, CodeErase.EraseAll.ER.eq_ok hE hv, true,
        ih.typ _ _ _ hρ hX h₀.2 hc, ?_⟩
      simp only [↓reduceIte]
      rw [← CodeErase.EraseAll.eraseScope_bindVal]
      exact ih'.2.2

/-- `hasTypCase`, one step. -/
theorem tf_case : ∀ ρ cs op w, SG QT gdC ρ → XT ρ → xTCases tyC cs = true →
    hasTypCase (m + 1) (simEnv B) ρ cs op w = .ok true →
    hasTypCase (m + 1) (simEnv B) (eraseScope ρ) cs op (eraseC w) = .ok true := by
  intro ρ cs op w hρ hX hcs h
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
      refine ⟨true, ih.typ _ _ _ hρ hX hct hc, ?_⟩
      simp only [↓reduceIte]
      have hcs₀ := sg_caseScope hρ t w
      have hXc : XT (caseScope ρ t w) := xt_of_typs hX (Round7.TypAgree.caseScope_typs ρ t w).1
      rcases Round7.TypAgree.elimUndef_eq_ok' h with ⟨o, ho, hk⟩ | ⟨_, hk⟩
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
      exact ih.case _ _ _ _ hρ hX hcs h

/-- `hasTypInsts`, one step. -/
theorem tf_insts : ∀ insts ws v, (∀ w ∈ ws, ArgIn QT gdC w) → (∀ w ∈ ws, ArgTyX w) →
    xInsts tyC insts = true → hasTypInsts (m + 1) (simEnv B) insts ws v = .ok true →
    hasTypInsts (m + 1) (simEnv B) insts (ws.map eraseA) (eraseC v) = .ok true := by
  intro insts ws v hW hWT hins h
  cases insts with
  | nil => simp [hasTypInsts] at h
  | cons i insts =>
    obtain ⟨qs, pats, dt⟩ := i
    simp only [xInsts, List.all_cons, Bool.and_eq_true] at hins
    obtain ⟨⟨⟨hpats, hdt⟩, hcode⟩, hins⟩ := hins
    simp only [hasTypInsts] at h ⊢
    have hE := (eraseAt H m).matchArgs VarEnv.empty pats ws CodeErase.EraseAll.sg_empty hpats hW
    rw [CodeErase.EraseAll.eraseScope_empty] at hE
    rw [hE.1]
    rcases Round7.TypAgree.elimUndef_eq_ok' h with ⟨ρi, hρi, hk⟩ | ⟨hu, hk⟩
    · rw [hρi]
      simp only [Functor.map, Except.map, Res.elimUndef]
      have hT : defTypCode dt = true → ρi.typs = [] := by
        intro hc
        rw [hc, Bool.not_true, Bool.false_or, List.isEmpty_iff] at hcode
        subst hcode
        rw [matchArgs_nil hρi]
        rfl
      exact ih.defTyp _ _ _ (hE.2 ρi hρi) (matchArgs_xt m xt_empty hWT hρi) hdt hT hk
    · rw [hu]
      simp only [Functor.map, Except.map, Res.elimUndef]
      exact ih.insts _ _ _ hW hWT (by unfold xInsts; exact hins) hk

end Step

theorem tFwdAt_succ (H : Hyps QT grC gdC (simEnv B)) {m : Nat} (ih : TFwdAt B m) :
    TFwdAt B (m + 1) :=
  ⟨tf_typ H ih, tf_tup H ih, tf_list H ih, tf_defTyp H ih, tf_fields H ih, tf_case H ih,
    tf_insts H ih⟩

/-- **The typing block goes to the erased side, at every fuel.** -/
theorem tFwdAt (H : Hyps QT grC gdC (simEnv B)) : ∀ n, TFwdAt B n
  | 0 => tFwdAt_zero
  | n + 1 => tFwdAt_succ H (tFwdAt H n)

/-- **Typing goes to the erased side**, at a checked type, in a scope whose definition variables
are `gdC` and whose type variables are bound to closed checked types. -/
theorem hasTyp_erase (H : Hyps QT grC gdC (simEnv B)) {ρ : VarEnv} {t : Typ} {v : Value}
    (hρ : SG QT gdC ρ) (hX : XT ρ) (ht : xTy tyC t = true) (h : HasTyp (simEnv B) ρ t v) :
    HasTyp (simEnv B) (eraseScope ρ) t (eraseC v) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (tFwdAt H n).typ ρ t v hρ hX ht hn⟩

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
