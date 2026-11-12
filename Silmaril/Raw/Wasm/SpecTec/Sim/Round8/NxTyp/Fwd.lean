module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.NxTyp.Base
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Thms

/-!
# Round 8, typing across erasure without a swap set: the induction (unrefined)

`tfAt`: at every fuel, if a member of the typing block answers `true` on checked types, it answers
`true` on the erased value. The scope changes only in `hasTyp`, `hasTypTup` and `hasTypList`, where
the two sides agree on the variables `A`; the members below a type instance (`hasTypDef`,
`hasTypFields`, `hasTypCase`, `hasTypInsts`) run on the same scope on both sides, because the
instance is selected by the same evaluated type arguments.

The environment is abstract: `EnvN S env` says that every type `env` finds under a name of `S` is
checked, and `NxSites.EnvNx` that the `good` types are export-free.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVf nxB)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (nxAT toAT sigFixed TypsNx EnvNx)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn isExpT)

/-- **Every type `env` finds under a name of `S` is checked.** -/
def EnvN (S : List String) (env : Env) : Prop :=
  ∀ x td, env.findTyp? x = some td → S.contains x = true → nInsts S td.2 = true

variable {S : List String} {env : Env}

/-- **The typing block goes to the erased side at fuel `n`.** -/
structure TFAt (S : List String) (env : Env) (n : Nat) : Prop where
  typ : ∀ A ρ ρ' t v, Agr A ρ ρ' → TypsTP S ρ → nTy S A t = true →
    hasTyp n env ρ t v = .ok true → hasTyp n env ρ' t (eraseV v) = .ok true
  tup : ∀ A ρ ρ' bs vs, Agr A ρ ρ' → TypsTP S ρ → nTyBinds S A bs = true →
    hasTypTup n env ρ bs vs = .ok true → hasTypTup n env ρ' bs (vs.map eraseV) = .ok true
  list : ∀ A ρ ρ' t vs, Agr A ρ ρ' → TypsTP S ρ → nTy S A t = true →
    hasTypList n env ρ t vs = .ok true → hasTypList n env ρ' t (vs.map eraseV) = .ok true
  defTyp : ∀ A ρ dt v, TypsTP S ρ → nDefTyp S A dt = true →
    hasTypDef n env ρ dt v = .ok true → hasTypDef n env ρ dt (eraseV v) = .ok true
  fields : ∀ A ρ fs gs, TypsTP S ρ → nFields S A fs = true →
    hasTypFields n env ρ fs gs = .ok true → hasTypFields n env ρ fs (eraseVf gs) = .ok true
  case : ∀ A ρ cs op w, TypsTP S ρ → nCases S A cs = true →
    hasTypCase n env ρ cs op w = .ok true → hasTypCase n env ρ cs op (eraseV w) = .ok true
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgTP S w) → nInsts S insts = true →
    hasTypInsts n env insts ws v = .ok true → hasTypInsts n env insts ws (eraseV v) = .ok true

theorem tfAt_zero : TFAt S env 0 := by
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

theorem isExpT_eq {t : Typ} (h : isExpT t = true) : t = .iterT (.varT "exportinst" []) .list := by
  unfold isExpT at h
  split at h
  · rfl
  · cases h

theorem hasTyp_nil_list {n : Nat} {ρ ρ₁ : VarEnv} {t : Typ} {w : Value} (hE : isExpT t = true)
    (h : hasTyp n env ρ t w = .ok true) : hasTyp n env ρ₁ t (.list []) = .ok true := by
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

theorem nInsts_cons {S : List String} {qs : List Param} {pats : List Arg} {dt : DefTyp}
    {insts : List Inst} (h : nInsts S (.instD qs pats dt :: insts) = true) :
    nDefTyp S (Determ.quantNames qs) dt = true ∧ nInsts S insts = true := by
  simp only [nInsts, List.all_cons, Bool.and_eq_true] at h
  exact h

theorem premsOk_nil (n : Nat) (ρ ρ' : VarEnv) : premsOk n env ρ [] = premsOk n env ρ' [] := by
  rcases n with _ | n
  · simp [premsOk, premsHold]
  · simp [premsOk, premsHold_nil_eq, Res.elimUndef]

section Step

set_option linter.unusedSectionVars false

variable (hN : EnvN S env) (hE : EnvNx sigFixed.good env) {m : Nat} (ih : TFAt S env m)
include hN hE ih

/-- An export-free type has export-free values at fuel `m`. -/
theorem nx_at {ρ : VarEnv} {t : Typ} {v : Value} (hρ : TypsTP S ρ) (ht : nxT t = true)
    (h : hasTyp m env ρ t v = .ok true) : nxB v = true :=
  (NxSites.nxTyp hE m).typ ρ t v (typsNx_of_TP hρ) ht h

/-- `hasTyp`, one step. -/
theorem tf_typ : ∀ A ρ ρ' t v, Agr A ρ ρ' → TypsTP S ρ → nTy S A t = true →
    hasTyp (m + 1) env ρ t v = .ok true → hasTyp (m + 1) env ρ' t (eraseV v) = .ok true := by
  intro A ρ ρ' t v hR hX ht h
  cases t with
  | boolT => simpa [hasTyp, Swap.asBool?_eraseV] using h
  | numT t => simpa [hasTyp, Swap.asNum?_eraseV] using h
  | textT => simpa [hasTyp, Swap.asText?_eraseV] using h
  | tupT bs =>
    simp only [nTy] at ht
    simp only [hasTyp, Swap.asTuple?_eraseV] at h ⊢
    cases hvt : v.asTuple? with
    | none => rw [hvt] at h; cases h
    | some vs =>
      rw [hvt] at h
      exact ih.tup _ _ _ _ _ hR hX ht h
  | iterT t it =>
    simp only [nTy, Bool.and_eq_true] at ht
    cases it with
    | opt =>
      simp only [hasTyp, Swap.asOpt?_eraseV] at h ⊢
      cases hvo : v.asOpt? with
      | none => rw [hvo] at h; cases h
      | some o =>
        rw [hvo] at h
        cases o with
        | none => rfl
        | some w => exact ih.typ _ _ _ _ _ hR hX ht.1 h
    | list =>
      simp only [hasTyp, Swap.asList?_eraseV] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        exact ih.list _ _ _ _ _ hR hX ht.1 h
    | list1 =>
      simp only [hasTyp, Swap.asList?_eraseV] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        simp only [Option.map_some, List.isEmpty_map]
        by_cases he : vs.isEmpty = true
        · simp [he] at h
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ih.list _ _ _ _ _ hR hX ht.1 h
    | listN e o =>
      have hxe : varsIn A (freeExp e) = true := by simpa [nIter] using ht.2
      simp only [hasTyp, Swap.asList?_eraseV] at h ⊢
      cases hvl : v.asList? with
      | none => rw [hvl] at h; cases h
      | some vs =>
        rw [hvl] at h
        simp only [Option.map_some, Res.bind_eq_ok] at h ⊢
        obtain ⟨kv, hkv, k, hk, hl⟩ := h
        refine ⟨kv, by rw [evalExp_agr hR hxe]; exact hkv, k, hk, ?_⟩
        obtain ⟨hlen, hl⟩ := iteP_ok_true hl
        simp only [List.length_map, hlen, ↓reduceIte]
        exact ih.list _ _ _ _ _ hR hX ht.1 hl
  | varT x args =>
    simp only [nTy, Bool.and_eq_true] at ht
    simp only [hasTyp] at h ⊢
    rw [localTyp?_agr hR]
    cases hl : localTyp? ρ x args with
    | some t' =>
      rw [hl] at h
      have ht' : TP S t' := by
        cases args with
        | nil => exact hX (x, t') (Script.mem_of_find? hl)
        | cons _ _ => simp [localTyp?] at hl
      exact ih.typ _ _ _ _ _ hR.nil hX ht'.1 h
    | none =>
      rw [hl] at h
      simp only [Res.bind_eq_ok] at h ⊢
      obtain ⟨td, htd, ws, hws, hi⟩ := h
      have htd' : env.findTyp? x = some td := by
        cases hf : env.findTyp? x with
        | none => rw [hf] at htd; simp [Res.ofOption] at htd
        | some td' => rw [hf] at htd; simp [Res.ofOption] at htd; rw [htd]
      refine ⟨td, htd, ws, by rw [evalArgs_agr hR ht.2]; exact hws, ?_⟩
      exact ih.insts _ _ _ (evalArgs_argTP hX ht.2 hws) (hN x td htd' ht.1) hi

/-- `hasTypTup`, one step. -/
theorem tf_tup : ∀ A ρ ρ' bs vs, Agr A ρ ρ' → TypsTP S ρ → nTyBinds S A bs = true →
    hasTypTup (m + 1) env ρ bs vs = .ok true →
    hasTypTup (m + 1) env ρ' bs (vs.map eraseV) = .ok true := by
  intro A ρ ρ' bs vs hR hX hbs h
  cases bs with
  | nil => cases vs <;> simp_all [hasTypTup]
  | cons b bs =>
    obtain ⟨x, t⟩ := b
    rw [nTyBinds, Bool.and_eq_true] at hbs
    cases vs with
    | nil => simp [hasTypTup] at h
    | cons v vs =>
      simp only [hasTypTup, Res.bind_eq_ok, List.map_cons] at h ⊢
      obtain ⟨c, hc, hrest⟩ := h
      cases c
      · simp at hrest
      · simp only [↓reduceIte] at hrest
        refine ⟨true, ih.typ _ _ _ _ _ hR hX hbs.1 hc, ?_⟩
        simp only [↓reduceIte]
        have hR' := hR.bind x t (v := v) fun hn => nx_at hN hE ih hX hn hc
        exact ih.tup _ _ _ _ _ hR' (typsTP_bindVal hX x v) hbs.2 hrest

/-- `hasTypList`, one step. -/
theorem tf_list : ∀ A ρ ρ' t vs, Agr A ρ ρ' → TypsTP S ρ → nTy S A t = true →
    hasTypList (m + 1) env ρ t vs = .ok true →
    hasTypList (m + 1) env ρ' t (vs.map eraseV) = .ok true := by
  intro A ρ ρ' t vs hR hX ht h
  cases vs with
  | nil => simp [hasTypList]
  | cons v vs =>
    simp only [hasTypList, Res.bind_eq_ok, List.map_cons] at h ⊢
    obtain ⟨c, hc, hrest⟩ := h
    cases c
    · simp at hrest
    · simp only [↓reduceIte] at hrest
      refine ⟨true, ih.typ _ _ _ _ _ hR hX ht hc, ?_⟩
      simp only [↓reduceIte]
      exact ih.list _ _ _ _ _ hR hX ht hrest

/-- `hasTypDef`, one step. -/
theorem tf_defTyp : ∀ A ρ dt v, TypsTP S ρ → nDefTyp S A dt = true →
    hasTypDef (m + 1) env ρ dt v = .ok true →
    hasTypDef (m + 1) env ρ dt (eraseV v) = .ok true := by
  intro A ρ dt v hX hdt h
  cases dt with
  | aliasT t =>
    simp only [nDefTyp] at hdt
    simp only [hasTypDef] at h ⊢
    exact ih.typ _ _ _ _ _ (agr_refl A ρ) hX hdt h
  | structT fs =>
    simp only [nDefTyp] at hdt
    simp only [hasTypDef, EraseAll.asStruct?_eraseV] at h ⊢
    cases hvs : v.asStruct? with
    | none => rw [hvs] at h; cases h
    | some gs =>
      rw [hvs] at h
      exact ih.fields _ _ _ _ hX hdt h
  | variantT cs =>
    simp only [nDefTyp] at hdt
    simp only [hasTypDef, Swap.asCase?_eraseV] at h ⊢
    cases hvc : v.asCase? with
    | none => rw [hvc] at h; cases h
    | some p =>
      rw [hvc] at h
      obtain ⟨op, w⟩ := p
      exact ih.case _ _ _ _ _ hX hdt h

/-- `hasTypFields`, one step. -/
theorem tf_fields : ∀ A ρ fs gs, TypsTP S ρ → nFields S A fs = true →
    hasTypFields (m + 1) env ρ fs gs = .ok true →
    hasTypFields (m + 1) env ρ fs (eraseVf gs) = .ok true := by
  intro A ρ fs gs hX hfs h
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
      simp only [nFields, Bool.and_eq_true] at hfs
      obtain ⟨hf, hfs⟩ := hfs
      simp only [hasTypFields, Swap.eraseVf] at h ⊢
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
      have htail := ih.fields _ _ _ _ hX hfs hrest
      simp only [↓reduceIte]
      rw [Res.bind_eq_ok]
      by_cases hEx : a = "EXPORTS"
      · subst hEx
        simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, List.isEmpty_iff] at hf
        obtain ⟨hT, rfl⟩ := hf
        refine ⟨true, hasTyp_nil_list hT hc, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        refine ⟨true, ?_, by simpa using htail⟩
        rcases m with _ | m
        · simp [hasTypFields] at hrest
        · simp [premsOk, premsHold_nil_eq, Res.elimUndef]
      · have hne : (a == "EXPORTS") = false := by simpa using hEx
        simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true]
          at hf
        simp only [hEx, ↓reduceIte]
        refine ⟨true, ih.typ _ _ _ _ _ (agr_refl A ρ) hX hf.1 hc, ?_⟩
        simp only [↓reduceIte, Res.bind_eq_ok]
        refine ⟨true, ?_, by simpa using htail⟩
        rcases hf.2 with ⟨hpe, -⟩ | hnx
        · simp only [List.isEmpty_iff] at hpe
          subst hpe
          rcases m with _ | m
          · simp [hasTypFields] at hrest
          · simp [premsOk, premsHold_nil_eq, Res.elimUndef]
        · rw [Swap.eraseV_of_nxB _ (nx_at hN hE ih hX hnx hc)]
          exact hpv

/-- `hasTypCase`, one step. -/
theorem tf_case : ∀ A ρ cs op w, TypsTP S ρ → nCases S A cs = true →
    hasTypCase (m + 1) env ρ cs op w = .ok true →
    hasTypCase (m + 1) env ρ cs op (eraseV w) = .ok true := by
  intro A ρ cs op w hX hcs h
  cases cs with
  | nil => simp [hasTypCase] at h
  | cons c cs =>
    obtain ⟨op', t, qs, prems⟩ := c
    simp only [nCases, Bool.and_eq_true, Bool.or_eq_true] at hcs
    obtain ⟨⟨hct, hq⟩, hcs⟩ := hcs
    by_cases hop : op' = op
    · subst hop
      have h' := h
      simp only [hasTypCase, ↓reduceIte, Res.bind_eq_ok] at h'
      obtain ⟨c, hc, hc''⟩ := h'
      cases c
      · simp at hc''
      rcases hq with ⟨hpe, hqe⟩ | hnx
      · simp only [List.isEmpty_iff] at hpe hqe
        subst hpe hqe
        simp only [hasTypCase, ↓reduceIte, Res.bind_eq_ok] at h ⊢
        refine ⟨true, ih.typ _ _ _ _ _ (agr_refl A ρ) hX hct hc, ?_⟩
        obtain ⟨c, hc₂, h⟩ := h
        rw [hc] at hc₂
        cases hc₂
        simp only [quantDefs, List.flatMap_nil, bindQuants, Res.elimUndef, ↓reduceIte] at h ⊢
        rwa [premsOk_nil] at h
      · rw [Swap.eraseV_of_nxB _ (nx_at hN hE ih hX hnx hc)]
        exact h
    · simp only [hasTypCase, hop, ↓reduceIte] at h ⊢
      exact ih.case _ _ _ _ _ hX hcs h

/-- `hasTypInsts`, one step. -/
theorem tf_insts : ∀ insts ws v, (∀ w ∈ ws, ArgTP S w) → nInsts S insts = true →
    hasTypInsts (m + 1) env insts ws v = .ok true →
    hasTypInsts (m + 1) env insts ws (eraseV v) = .ok true := by
  intro insts ws v hW hins h
  cases insts with
  | nil => simp [hasTypInsts] at h
  | cons i insts =>
    obtain ⟨qs, pats, dt⟩ := i
    obtain ⟨hdt, hins⟩ := nInsts_cons hins
    simp only [hasTypInsts] at h ⊢
    rcases TypAgree.elimUndef_eq_ok' h with ⟨ρi, hρi, hk⟩ | ⟨hu, hk⟩
    · rw [hρi]
      simp only [Res.elimUndef]
      exact ih.defTyp _ _ _ _ (matchArgs_typsTP m typsTP_empty hW hρi) hdt hk
    · rw [hu]
      simp only [Res.elimUndef]
      exact ih.insts _ _ _ hW hins hk

end Step

theorem tfAt_succ (hN : EnvN S env) (hE : EnvNx sigFixed.good env) {m : Nat}
    (ih : TFAt S env m) : TFAt S env (m + 1) :=
  ⟨tf_typ hN hE ih, tf_tup hN hE ih, tf_list hN hE ih, tf_defTyp hN hE ih,
    tf_fields hN hE ih, tf_case hN hE ih, tf_insts hN hE ih⟩

/-- **The typing block goes to the erased side, at every fuel.** -/
theorem tfAt (hN : EnvN S env) (hE : EnvNx sigFixed.good env) : ∀ n, TFAt S env n
  | 0 => tfAt_zero
  | n + 1 => tfAt_succ hN hE (tfAt hN hE n)

/-- **`HasTyp` goes to the erased side** on scopes that agree on `A`, at a type checked over `A`. -/
theorem hasTyp_fwd (hN : EnvN S env) (hE : EnvNx sigFixed.good env) {A : List String}
    {ρ ρ' : VarEnv} {t : Typ} {v : Value} (hR : Agr A ρ ρ') (hX : TypsTP S ρ)
    (ht : nTy S A t = true) (h : HasTyp env ρ t v) : HasTyp env ρ' t (eraseV v) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (tfAt hN hE n).typ A ρ ρ' t v hR hX ht hn⟩

end Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp
